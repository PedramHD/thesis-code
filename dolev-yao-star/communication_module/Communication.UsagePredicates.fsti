/// Communication.UsagePredicates
/// =============================
///
/// This module defines the usage predicates the different send methods, e.g.,
/// [confidential_send_pred]. These predicates can be used by the application layer to restrict the
/// usage of the different send methods. These predicates are enforced using the predicates on
/// cryptographic operations, i.e., this module "combines" the global usages of the application
/// layer with these send predicates (see [send_layer_usage_preds] below).

module Communication.UsagePredicates

open Communication.MessageStructurePredicates
open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib
module LC = LabeledCryptoAPI


noeq type predicates_for_send_functions = {
  confidential_send_pred: (trace_idx:nat  -> m:bytes -> Type0);
  authenticated_send_pred: (trace_idx:nat  -> m:bytes -> Type0);
  authenticated_confidential_send_pred: (trace_idx:nat  -> m:bytes -> Type0);
  request_pred: (trace_idx:nat -> m:bytes -> Type0);
  response_pred: (trace_idx:nat -> response:bytes -> request:bytes -> sym_key:bytes -> Type0);
}

noeq type extended_global_usage = {
  higher_layer_gu:LC.global_usage;
  send_function_predicates:predicates_for_send_functions;
}

(**
  The usage predicates ppred, apred, spred, and mpred extend those of the higher layer. Thus, they
  get the usage_preds as an input (currently contained in the send_layer_preds)
*)
let public_key_enc_pred (extended_gu:extended_global_usage) (i:timestamp) (s:string) (pub_key:bytes) (m:bytes)  =
  let higher_layer_key_usages = extended_gu.higher_layer_gu.LC.key_usages in
  let higher_layer_usage_preds = extended_gu.higher_layer_gu.LC.usage_preds in
  let confidential_send_pred = extended_gu.send_function_predicates.confidential_send_pred in
  let authenticated_send_pred = extended_gu.send_function_predicates.authenticated_send_pred in
  let request_pred = extended_gu.send_function_predicates.request_pred in
  match s with
  | "SEND_LAYER_CONF_SEND" -> confidential_send_pred i m
  | "SEND_LAYER_CONF_AUTHN_SEND" -> (
    // The plaintext must contain a principal (the sender), and in particular, the payload must be
    // readable by this principal. After a successful signature verification, we know that either
    // the sender was corrupted, or the signature predicate holds true. In combination, we can at
    // least show that the payload is publishable if the sender was corrupted.
    match split m with
    | Error e -> higher_layer_usage_preds.LC.can_pke_encrypt i s pub_key m
    | Success (sender_and_pred_idx_bytes, msg) -> (
      match split sender_and_pred_idx_bytes with
      | Error e -> higher_layer_usage_preds.LC.can_pke_encrypt i s pub_key m
      | Success (sender_bytes, pred_idx_bytes) -> (
        match bytes_to_string sender_bytes with
        | Error e -> higher_layer_usage_preds.LC.can_pke_encrypt i s pub_key m
        | Success sender -> LC.can_flow i (LC.get_label higher_layer_key_usages msg) (readers [P sender])
      )
    )
  )

  | "SEND_LAYER_CONF_REQUEST_ONLY_PKE" -> ( // used for sending requests that contain a symmetric key
    // The plaintext must contain a byte (the symmetric key, added by the send layer), and the
    // message that must fulfill the same properties as the normal confidential-send.
    LC.can_flow i (LC.get_label higher_layer_key_usages m) public \/
    // (1) the message is publishable, or
    // (2) the message m has the form (sym_key, msg),
    //     the request predicate holds true for a previous timestamp,
    //     and the symmetric key is an aead-key labeled with some sender and some receiver
    (
      match split m with
      | Error e -> False
      | Success (sym_key, msg) -> (
        (exists (real_sender real_receiver:string). was_rand_generated_before i sym_key (join (readers [P real_sender]) (readers [P real_receiver])) (aead_usage "AEAD.Symmetric_Send_Key") /\ LC.can_flow i (LC.get_label higher_layer_key_usages m) (join (readers [P real_sender]) (readers [P real_receiver]))) /\
        (exists j. j<=i /\ request_pred j msg) /\
        //Require that the label of the message can flow to the label of the symmetric
        //key. This is useful when, for example, the request contains credentials and the
        //receiver wants to send a response with a secret that has the same label as the
        //credential.
        LC.can_flow i (LC.get_label higher_layer_key_usages msg) (LC.get_label higher_layer_key_usages sym_key)
      )
    )
  )
  | "SEND_LAYER_CONF_REQUEST_HYBRID" -> ( // used for sending requests where only the symmetric key is encrypted asymetrically, and the remaining payload is encrypted symetrically
    let sym_key = m in
    (exists (real_sender real_receiver:string). (was_rand_generated_before i sym_key (join (readers [P real_sender]) (readers [P real_receiver])) (aead_usage "AEAD.Symmetric_Send_Key")))
  )
  | _ -> higher_layer_usage_preds.LC.can_pke_encrypt i s pub_key m


let aead_pred (extended_gu:extended_global_usage) (i:timestamp) s k m ad =
  let higher_layer_key_usages = extended_gu.higher_layer_gu.LC.key_usages in
  let higher_layer_usage_preds = extended_gu.higher_layer_gu.LC.usage_preds in
  let request_pred = extended_gu.send_function_predicates.request_pred in
  let response_pred = extended_gu.send_function_predicates.response_pred in

  // We allow the attacker to create its own symmetric key (i.e., some publishable value). For these
  // keys, we do not want any restrictions on their usage.  In particular, when using hybrid
  // encryption (i.e., the request contains only the symmetric key encrypted asymetrically), the
  // responder gets the guarantee that the symmetric key is publishable or some pke-predicate holds
  // true. This means that in the first case (the symmetric key is publishable), the receiver does
  // not have any other guarantees. However, [aead_enc] (when encrypting the response with the
  // symmetric key) requires that for all strings s, when [is_aead_key] holds true for the key and
  // s, then also the aead predicate must hold true.
  LC.can_flow i (LC.get_label higher_layer_key_usages k) public \/
  (
    match s with
    | "AEAD.Symmetric_Send_Key" -> (
      match split m with
      | Error e -> higher_layer_usage_preds.LC.can_aead_encrypt i s k m ad
      | Success (msg_tag_bytes, message) -> (
        match bytes_to_string msg_tag_bytes with
        | Error _ -> higher_layer_usage_preds.LC.can_aead_encrypt i s k m ad
        | Success msg_tag -> (
          match msg_tag with
          | "Send.Layer.Request" -> (exists j. j<=i /\ request_pred j message)
          | "Send.Layer.Response" -> (
            match split message with
            | Error _ -> False
            | Success (request_send_idx_bytes, response) -> (
              match bytes_to_nat request_send_idx_bytes with
              | Error _ -> False
              | Success request_send_idx -> exists sym_key j request. j<=i /\ response_pred j response request sym_key /\ is_request_at_idx request request_send_idx sym_key
              )
            )
          | _ -> higher_layer_usage_preds.LC.can_aead_encrypt i s k m ad
        )
      )
    )
    | _ -> higher_layer_usage_preds.LC.can_aead_encrypt i s k m ad
  )

let signature_pred (extended_gu:extended_global_usage) (i:timestamp) (s:string) (k:bytes) (m:bytes) =
  let higher_layer_key_usages = extended_gu.higher_layer_gu.LC.key_usages in
  let higher_layer_usage_preds = extended_gu.higher_layer_gu.LC.usage_preds in
  let authenticated_send_pred = extended_gu.send_function_predicates.authenticated_send_pred in
  let authenticated_confidential_send_pred = extended_gu.send_function_predicates.authenticated_confidential_send_pred in
  match s with
  | "SEND_LAYER_AUTHN_SEND" -> (
      match split m with
      | Error e -> False
      | Success (auth_pred_idx_bytes, msg_payload) -> ( // some trace index at which the predicate holds true
        match bytes_to_nat auth_pred_idx_bytes with
        | Error e -> False
        | Success auth_pred_idx -> authenticated_send_pred auth_pred_idx msg_payload
      )
  )
  | "SEND_LAYER_CONF_AUTHN_SEND" -> (
    exists pub_key nonce plaintext. m == pke_enc pub_key nonce plaintext /\
    (
      match split plaintext with
      | Error e -> False
      | Success (sender_and_pred_idx_bytes, msg_payload) -> (
        match split sender_and_pred_idx_bytes with
        | Error e -> False
        | Success (sender_bytes, pred_idx_bytes) -> (
          match bytes_to_nat pred_idx_bytes with
          | Error e -> False
          | Success authn_conf_pred_idx -> authenticated_confidential_send_pred authn_conf_pred_idx msg_payload
        )
      )
    )
  )
  | "SEND_LAYER_CONF_AUTHN_REQUEST" -> (
    (match split m with 
    | Error e -> False
    | Success (sender_bytes, r_ct) -> 
	(match split r_ct with
	| Error e -> False
	| Success (receiver_bytes, ct) ->
	  (match bytes_to_string sender_bytes, bytes_to_string receiver_bytes with
	  | Success sender, Success receiver ->
	    LC.get_signkey_label higher_layer_key_usages k == readers [P sender] /\
	    (exists pk n pt. ct == pke_enc pk n pt /\
	       //LC.can_flow i (LC.get_label higher_layer_key_usages pt) (join (readers [P sender]) (readers [P receiver])) /\
	       (LC.can_flow i (LC.get_label higher_layer_key_usages pt) public \/
	       (match split pt with 
	       | Error e -> False
	       | Success (sym_key, msg) -> was_rand_generated_before i sym_key (join (readers [P sender]) (readers [P receiver])) (aead_usage "AEAD.Symmetric_Send_Key") /\ LC.can_flow i (LC.get_label higher_layer_key_usages m) (join (readers [P sender]) (readers [P receiver])) /\
		 (exists j. j<=i /\ extended_gu.send_function_predicates.request_pred j msg) /\
		 LC.can_flow i (LC.get_label higher_layer_key_usages msg) (LC.get_label higher_layer_key_usages sym_key))))
	  | _ -> False)
	)))
  | _ -> higher_layer_usage_preds.LC.can_sign i s k m

let mac_pred (extended_gu:extended_global_usage) i s k m =
  let higher_layer_usage_preds = extended_gu.higher_layer_gu.LC.usage_preds in
  higher_layer_usage_preds.LC.can_mac i s k m


// Goal: get a usage_pred from the higher layer, combine both preds into one
let send_layer_usage_preds (extended_gu:extended_global_usage) : LC.usage_preds = {
  LC.can_pke_encrypt = public_key_enc_pred extended_gu;
  LC.can_aead_encrypt =  aead_pred extended_gu;
  LC.can_sign = signature_pred extended_gu;
  LC.can_mac = mac_pred extended_gu
}
