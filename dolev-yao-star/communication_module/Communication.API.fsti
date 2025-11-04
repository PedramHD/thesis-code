/// Communication.API
/// ===============================
///
/// This module defines an API to be used by applications. The functions are intended to be called
/// by the principals and some of them are stateful as they modify or read the trace.
///
/// This is a layer on top of the "Labeled" layer and provides implementations for confidential and authenticated send.

module Communication.API

open SecrecyLabels
open Communication.CryptoLib
module C = CryptoLib
open GlobalRuntimeLib

module LCA = LabeledCryptoAPI

open LabeledRuntimeAPI
open LabeledPKI
// (from tls13) 
open TLS13.API
open Communication.MessageStructurePredicates
open Communication.UsagePredicates
open Communication.Sessions
open Communication.Preds
open Communication.Sessions.Lemmas
open Communication.CoreFunctions


type send_layer_channel_property =
  | Raw: send_layer_channel_property
  | AuthN: send_layer_channel_property
  | AuthNConf: send_layer_channel_property
  | Conf: send_layer_channel_property


(**
   Send a message. Returns the index of the send event in the trace (needed to receive that message
  later). Here, when sending confidentially, we simply encrypt the message with the public key of
  the receiver. In particular, this function does not handle connections/symmetric keys.
*)
val send:
    #i:timestamp ->
    #higher_level_preds:send_layer_preds ->
    sender:principal ->
    receiver:principal ->
    message:msg (higher_level_preds.extended_higher_layer_gu) i (join (readers [P sender]) (readers [P receiver])) ->
    channel_property:send_layer_channel_property ->
    LCrypto (message_idx:timestamp) (pki (send_preds higher_level_preds))
    (requires (fun t0 ->
      let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
      (i <= trace_len t0) /\
      ((channel_property = AuthN) ==> send_predicates.authenticated_send_pred i message) /\
      ((channel_property = Conf) ==>
	// (from tls13)	
	// (send_preds higher_level_preds) == (TLS13.Sessions.tls13 higher_level_preds) /\
        // (is_publishable ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) i message \/
        // send_predicates.confidential_send_pred i message)) /\
        send_predicates.confidential_send_pred i message) /\
      ((channel_property = AuthNConf) ==> send_predicates.authenticated_confidential_send_pred i message) /\
      (((channel_property = Raw) \/ (channel_property = AuthN)) ==> is_publishable  (higher_level_preds.extended_higher_layer_gu) i message)
    ))
    (ensures (fun t0 message_idx t1 ->
      ((channel_property = Raw) ==>
        message_idx == trace_len t0 /\
        trace_len t1 = trace_len t0 + 1 /\
        was_message_sent_at message_idx sender receiver message) /\
      ((channel_property = AuthN) ==> (
        message_idx == trace_len t0 + 1 /\
        trace_len t1 = trace_len t0 + 2 /\
        (exists (signed_message:C.bytes).
          is_authenticated_message_sent_at message_idx i message signed_message
        )
      ))  /\
      ((channel_property = Conf) ==> (
        (exists (confidential_message:C.bytes).
          is_confidential_message_sent_at message_idx message confidential_message
        )
      )) /\
      ((channel_property = AuthNConf) ==>
          is_authenticated_confidential_message_sent_at message_idx message
      )
    ))


(**
  Receive a message for [receiver] sent at the given index. If the event at the given index is not a
  send event or the receiver does not match the intended receiver (as recorded in the send event),
  this function returns None.
*)
val receive_i:
    #higher_level_preds:send_layer_preds ->
    index_of_send_event:timestamp ->
    receiver:principal ->
    channel_property:send_layer_channel_property ->
    LCrypto (now:timestamp & sender:principal & msg:msg (higher_level_preds.extended_higher_layer_gu) now (readers [P receiver])) (pki (send_preds higher_level_preds))
    // (requires (fun t0 -> channel_property = Conf ==> (send_preds higher_level_preds) == (TLS13.Sessions.tls13 higher_level_preds)))
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,sender,msg|) t1 ->
      let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
      let higher_layer_key_usages = higher_level_preds.extended_higher_layer_gu.higher_layer_gu.LabeledCryptoAPI.key_usages in
      // t0 == t1 /\ // We update session in TLS13, so the trace len increases by 1 - if this behavior is required, remove state updates in TLS13.
      now = trace_len t1 /\
      (index_of_send_event < trace_len t1) /\
      (
        match channel_property with
        | Raw -> exists sender' recv. was_message_sent_at index_of_send_event sender' recv msg
        | AuthN -> (exists (verification_idx:nat) (signed_message:C.bytes).
            is_authenticated_message_sent_at index_of_send_event verification_idx msg signed_message
          ) /\
          //message is publishable
          LCA.can_flow now (LCA.get_label higher_layer_key_usages msg) public /\
          (
            LCA.corrupt_id now (P sender) \/
            (exists j. later_than index_of_send_event j /\ send_predicates.authenticated_send_pred j msg)
          )
        | Conf -> (exists confidential_msg.
            is_confidential_message_sent_at index_of_send_event msg confidential_msg
          ) /\
          (is_publishable higher_level_preds.extended_higher_layer_gu now msg \/
            (exists j. later_than now j /\ send_predicates.confidential_send_pred j msg)
          )
        | AuthNConf -> is_authenticated_confidential_message_sent_at index_of_send_event msg /\
          // if the attacker corrupts the sender, it can send messages that are publishable
          ((LCA.corrupt_id now (P sender) /\ LCA.can_flow now (LCA.get_label higher_layer_key_usages msg) public) \/
          (exists j. later_than index_of_send_event j /\ send_predicates.authenticated_confidential_send_pred j msg))
        | _ -> True
      )
    )
    )



(*! Functions Providing One-Message Channels: The sender sends a request, the receiver can respond
to this message, and the original sender can receive the response to the request (if the response
was already sent out by the responder) *)


(**! The request functions are implemented in two different ways: The [pke] functions encrypt both
the symmetric key and the payload asymmetrically (i.e., as a single ciphertext). The [pke_aead]
functions implement a hybrid scheme, where only the symmetric key is encrypted asymmetrically, and
where the payload is encrypted symmetrically with the symmetric key.
*)

let pke_only = true


(**
  This function sends the message to the receiver and returns the session index at which the
  symmetric key is stored. When receiving the response, this session index must be provided.

  In addition to the session index, the function returns the symmetric key. In some cases, the
  responder might label some secret with the label of the symmetric key. In such cases, it is useful
  if the client can conclude that some part of the response has the label of the symmetric key.
*)

val initiator_send_request:
    #i:timestamp ->
    #higher_level_preds:send_layer_preds ->
    sender:principal ->
    receiver:principal ->
    message:msg (higher_level_preds.extended_higher_layer_gu) i (join (readers [P sender]) (readers [P receiver])) ->
    LCrypto (sym_key_session_state_idx:nat & sym_key:C.bytes & message_idx:timestamp) (pki (send_preds higher_level_preds))
    (requires (fun t0 ->
      let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
      (i <= trace_len t0) /\
      send_predicates.request_pred i message
    ))
    (ensures (fun t0 (|_, sym_key, message_idx|) t1 ->
      (is_request_at_idx message message_idx sym_key) /\
      is_aead_key (higher_level_preds.extended_higher_layer_gu) (trace_len t1) sym_key (join (readers [P sender]) (readers [P receiver])) "AEAD.Symmetric_Send_Key"
    ))


(**
  Function for the responder to receive a request.
*)

val responder_receive_request:
    #i:timestamp ->
    #higher_level_preds:send_layer_preds ->
    index_of_send_event_of_request:timestamp ->
    receiver:principal ->
    LCrypto (now:timestamp & sender:principal & sym_key:C.bytes & msg:msg (higher_level_preds.extended_higher_layer_gu) now (readers [P receiver])) (pki (send_preds higher_level_preds))
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,sender,sym_key,msg|) t1 ->
      let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
      t0 == t1 /\
      now = trace_len t0 /\
      (index_of_send_event_of_request < trace_len t0) /\
      (is_request_at_idx msg index_of_send_event_of_request sym_key) /\
      (
       (
         (is_publishable (higher_level_preds.extended_higher_layer_gu) now msg /\
         is_publishable (higher_level_preds.extended_higher_layer_gu) now sym_key) \/
         (
            (exists (real_sender:principal). is_aead_key (higher_level_preds.extended_higher_layer_gu) now sym_key (join (readers [P real_sender]) (readers [P receiver])) "AEAD.Symmetric_Send_Key") /\
            (exists j. later_than now j /\ send_predicates.request_pred j msg)
         )
       ) /\
       ( LCA.can_flow now (LCA.get_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).key_usages msg) (LCA.get_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).key_usages sym_key) // follows from the type of the result of [aead_dec]
       )
      )
    ))


(**
  This function sends an authenticated message to the receiver and returns the session index at which the
  symmetric key is stored. When receiving the response, this session index must be provided.
  In addition to the session index, the function returns the symmetric key. 
*)

val initiator_send_authn_request:
    #i:timestamp ->
    #higher_level_preds:send_layer_preds ->
    sender:principal ->
    receiver:principal ->
    message:msg (higher_level_preds.extended_higher_layer_gu) i (join (readers [P sender]) (readers [P receiver])) ->
    LCrypto (sym_key_session_state_idx:nat & sym_key:C.bytes & message_idx:timestamp) (pki (send_preds higher_level_preds))
    (requires (fun t0 ->
      let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
      (i <= trace_len t0) /\ send_predicates.request_pred i message
    ))
    (ensures (fun t0 (|_, sym_key, message_idx|) t1 ->
      (is_request_at_idx message message_idx sym_key) /\
      is_labeled (higher_level_preds.extended_higher_layer_gu) (trace_len t1) sym_key (join (readers [P sender]) (readers [P receiver]))
    ))

(**
  Functions for the responder to receive authenticated requests.
*)
val responder_receive_authn_request:
    #i:timestamp ->
    #higher_level_preds:send_layer_preds ->
    index_of_send_event_of_request:timestamp ->
    receiver:principal ->
    LCrypto (now:timestamp & sender:principal & sym_key:C.bytes & msg:msg (higher_level_preds.extended_higher_layer_gu) now (readers [P receiver])) (pki (send_preds higher_level_preds))
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,sender,sym_key,msg|) t1 ->
      let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
      let ku = ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).key_usages in 
      t0 == t1 /\
      now = trace_len t0 /\
      (index_of_send_event_of_request < trace_len t0) /\ 
      (is_request_at_idx msg index_of_send_event_of_request sym_key) /\
      (LabeledCryptoAPI.corrupt_id now (P sender) \/
         (is_publishable (higher_level_preds.extended_higher_layer_gu) now msg /\
         is_publishable (higher_level_preds.extended_higher_layer_gu) now sym_key) \/
         (
            (is_aead_key (higher_level_preds.extended_higher_layer_gu) now sym_key (join (readers [P sender]) (readers [P receiver])) "AEAD.Symmetric_Send_Key") /\
            (exists j. later_than now j /\ send_predicates.request_pred j msg) /\
	    LCA.can_flow now (LCA.get_label ku msg) (LCA.get_label ku sym_key)	    
         )
      )
    ))


(**
  Function for sending the response to a request.

  We require the label of the message to be the same as the label of the symmetric key. (It would be
  enough to require that the label of the key flows to the label of the message.)

  For example, if the key is public (= the request was sent by the attacker), then the data sent by
  the responder must also be publishable.

  On this layer, the responder cannot authenticate the sender when getting a request (as the request
  is sent over a confidential-only channel).
*)
val responder_send_response:
    #i:timestamp ->
    #l:label ->
    #higher_level_preds:send_layer_preds ->
    initiator:principal -> // the principal that sent the request
    responder:principal -> // the principal calling this function
    sym_key:lbytes (higher_level_preds.extended_higher_layer_gu) i l ->
    send_idx_of_request:timestamp ->
    request:C.bytes ->
    message:msg (higher_level_preds.extended_higher_layer_gu) i l ->
    LCrypto (message_idx:timestamp) (pki (send_preds higher_level_preds))
    (requires (fun t0 ->
      let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
      (i <= trace_len t0) /\
      (
        (
          is_publishable (higher_level_preds.extended_higher_layer_gu) (trace_len t0) message /\
          is_publishable (higher_level_preds.extended_higher_layer_gu) (trace_len t0) sym_key
          // [aead_enc] requires that, whenever using an aead key, the corresponding aead predicate is also fulfilled.
          // Thus, we when using the function with a publishable symmetric key, we require that the key is not an aead key.
        )  \/
        (
          send_predicates.response_pred i message request sym_key /\ is_request_at_idx request send_idx_of_request sym_key /\
          //the label of the message flows to the label of the symmetric-key, currently ensured by the type of message and sym_key
          (is_aead_key (higher_level_preds.extended_higher_layer_gu) (trace_len t0) sym_key l "AEAD.Symmetric_Send_Key")
        )
    )))
    (ensures (fun t0 message_idx t1 -> True))


(**
  Function for the initiator to receive the response.
*)
val initiator_receive_response:
    #higher_level_preds:send_layer_preds ->
    sym_key_state_session_idx:nat ->
    index_of_send_event_of_response:timestamp ->
    initiator:principal ->
    LCrypto (now:timestamp & responder:principal & response:msg (higher_level_preds.extended_higher_layer_gu) now (readers [P initiator]) & request_send_idx:timestamp) (pki (send_preds higher_level_preds))
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,responder,response,request_send_idx|) t1 ->
      let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
      let higher_layer_key_usages = higher_level_preds.extended_higher_layer_gu.higher_layer_gu.LabeledCryptoAPI.key_usages in
      t0 == t1 /\
      now = trace_len t0 /\
      //in some cases it is useful to know that the label of the response can flow to the responder principal id:
      is_msg (higher_level_preds.extended_higher_layer_gu) now response (readers [P responder]) /\
      (
        ((LCA.corrupt_id now (P initiator) \/ LCA.corrupt_id now (P responder)) /\
           LCA.can_flow now (LCA.get_label higher_layer_key_usages response) public
        ) \/
        (exists sym_key j request. later_than now j /\ send_predicates.response_pred j response request sym_key /\ is_request_at_idx request request_send_idx sym_key)
      )
    ))


/// API for state management
/// ------------------------

let new_session_number (#pr:send_layer_preds) (p:principal) :
  LCrypto nat (LabeledPKI.pki (send_preds pr))
  (requires fun t0 -> True)
  (ensures fun t0 r t1 -> t1 == t0) =
  LabeledPKI.new_session_number #(send_preds pr) p


val new_session: #pr:send_layer_preds -> #i:timestamp -> p:principal -> si:nat -> vi:nat -> st:C.bytes ->
  LCrypto unit (pki (send_preds pr))
  (requires fun t0 -> trace_len t0 == i /\ pr.session_st_inv i p si vi st /\ is_msg (pr.extended_higher_layer_gu) i st (readers [V p si vi]))
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)

val update_session: #pr:send_layer_preds -> #i:timestamp -> p:principal -> si:nat -> vi:nat -> st:C.bytes ->
  LCrypto unit (pki (send_preds pr))
  (requires fun t0 -> trace_len t0 == i /\ pr.session_st_inv i p si vi st /\ is_msg (pr.extended_higher_layer_gu) i st (readers [V p si vi]))
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)

val get_session: #pr:send_layer_preds -> #i:timestamp -> p:principal -> si:nat ->
  LCrypto (vi:nat & msg (pr.extended_higher_layer_gu) i (readers [V p si vi])) (pki (send_preds pr))
  (requires fun t0 -> trace_len t0 == i)
  (ensures fun t0 (|vi,st|) t1 -> t1 == t0 /\
                               pr.session_st_inv i p si vi st)

val find_session:
  #pr:send_layer_preds -> #i:timestamp -> p:principal -> f:(si:nat -> vi:nat -> st:C.bytes -> bool) ->
  LCrypto (option (si:nat & vi:nat & msg (pr.extended_higher_layer_gu) i (readers [V p si vi]))) (pki (send_preds pr))
  (requires fun t0 -> trace_len t0 == i)
  (ensures fun t0 r t1 -> t1 == t0 /\
                       (match r with
                        | None -> True
                        | Some (|si,vi,st|) -> f si vi st /\
                                              pr.session_st_inv i p si vi st))

/// Other overwritten functions from LabeledRuntimeAPI
/// --------------------------------------------------
/// To keep the API consistent in terms of what preds need to be passed to the trace APIs.

let rand_gen (#pr:send_layer_preds) (l:label) (u:C.usage) :
    LCrypto (i:timestamp & secret pr.extended_higher_layer_gu i l u) (pki (send_preds pr))
    (requires (fun t0 -> True))
    (ensures (fun t0 (|i,s|) t1 ->
        i == trace_len t0 /\
        trace_len t1 = trace_len t0 + 1 /\
        was_rand_generated_at (trace_len t0) s l u)) =
    let (|i,s|) = LabeledPKI.rand_gen #(send_preds pr) l u in
    (|i,s|)

type event = CryptoEffect.event

let trigger_event (#pr:send_layer_preds) (p:principal) (ev:event):
    LCrypto unit (pki (send_preds pr))
    (requires (fun t0 -> event_pred_at (pki (send_preds pr)) (trace_len t0) p ev))
    (ensures (fun t0 (s) t1 ->
         trace_len t1 = trace_len t0 + 1 /\
         did_event_occur_at (trace_len t0) p ev)) =
    LabeledPKI.trigger_event #(send_preds pr) p ev


/// Other overwritten functions from LabeledPKI
/// -------------------------------------------

let private_key (pr:send_layer_preds) (i:timestamp) (si:nat) (p:principal) (kt:key_type) (t:string) =
  LabeledPKI.private_key (send_preds pr) i si p kt t

let public_key (pr:send_layer_preds) (i:timestamp) (p:principal) (kt:key_type) (t:string) =
   LabeledPKI.public_key (send_preds pr) i p kt t

// Returns session index (of the session which stores the private key)
let gen_private_key (#pr:send_layer_preds) (#i:timestamp) (p:principal) (kt:key_type) (t:string):
    LCrypto (priv_key_session_id:nat) (pki (send_preds pr))
    (requires (fun t0 -> i == trace_len t0))
    (ensures (fun t0 _ t1 -> trace_len t1 = trace_len t0 + 2))
    = LabeledPKI.gen_private_key #(send_preds pr) #i p kt t

// Retrieve a private key for p, identified by its type and usage string. Returns the session index
// of the session in which the private key is stored, and of course the key itself.
let get_private_key (#pr:send_layer_preds) (#i:timestamp) (p:principal) (kt:key_type) (t:string):
    LCrypto (si:nat & private_key pr i si p kt t) (pki (send_preds pr))
    (requires (fun t0 -> i == trace_len t0))
    (ensures (fun t0 _ t1 -> t0 == t1))
    = LabeledPKI.get_private_key #(send_preds pr) #i p kt t

// Install public key of p (identified by type and usage string) at peer. Returns the session index
// at which the public key is stored in peer's state.
let install_public_key (#pr:send_layer_preds) (#i:timestamp) (key_owner:principal) (target:principal) (kt:key_type) (t:string):
    LCrypto nat (pki (send_preds pr))
    (requires (fun t0 -> i == trace_len t0))
    (ensures (fun t0 _ t1 -> trace_len t1 = trace_len t0 + 1))
    = LabeledPKI.install_public_key #(send_preds pr) #i key_owner target kt t

// Retrieve the public key or peer (identified by type and usage string) in p's state.
let get_public_key (#pr:send_layer_preds) (#i:timestamp) (p:principal) (peer:principal) (kt:key_type) (t:string):
    LCrypto (public_key pr i peer kt t) (pki (send_preds pr))
    (requires (fun t0 -> i == trace_len t0))
    (ensures (fun t0 pk t1 -> t0 == t1 /\ 
     (kt = OneTimeDH ==> (exists si. is_dh_public_key pr.extended_higher_layer_gu  i pk (readers [V peer si 0]) t))))
    = LabeledPKI.get_public_key #(send_preds pr) #i p peer kt t

// Delete a OneTimeDH key (identified by the usage string) from p's state. Note: in order to be able
// to still refer to the key value in proofs etc., the session in which the key is stored is
// overwritten by a DeletedOneTimeKey session.
let delete_one_time_key (#pr:send_layer_preds) (#i:timestamp) (p:principal) (t:string):
    LCrypto unit (pki (send_preds pr))
    (requires (fun t0 -> i == trace_len t0))
    (ensures (fun t0 _ t1 -> trace_len t1 == trace_len t0 + 1))
    = LabeledPKI.delete_one_time_key #(send_preds pr) #i p t


/// Helper functions for model execution
/// ------------------------------------

// Container type for session indices at which private keys for send layer functionality are stored.
type key_session_indices = {
    conf_send_key: nat;
    conf_authn_send_key: nat;
    conf_req_pke_send_key: nat;
    conf_req_hybrid_send_key: nat;
    authn_send_key: nat;
    conf_authn_sig_send_key: nat;
  }

// Generates all asymmetric keys for p needed to use the send layer
val gen_send_keys:
  #pr:send_layer_preds -> p:principal ->
  LCrypto key_session_indices (pki (send_preds pr))
  (requires fun t0 -> True)
  (ensures fun t0 r t1 -> trace_len t1 = trace_len t0 + 12)

// Installs all public keys needed for the send layer of p at peer.
val install_send_public_keys:
  #pr:send_layer_preds -> p:principal -> peer:principal ->
  LCrypto key_session_indices (pki (send_preds pr))
  (requires fun t0 -> True)
  (ensures fun t0 r t1 -> trace_len t1 = trace_len t0 + 6)

// Generate all keys required for send layer for all principals and distribute the public keys among all these principals. Returns the private key session indices (in the same order as the principals where given).
val generate_and_distribute_send_keys:
  #pr:send_layer_preds -> #len:nat -> (principals:list principal{List.Tot.length principals = len}) ->
  LCrypto (list key_session_indices) (pki (send_preds pr))
  (requires fun t0 -> len >= 1)
  (ensures fun t0 r t1 -> trace_len t1 = trace_len t0 + (12 `op_Multiply` len) + (6 `op_Multiply` len `op_Multiply` len))
