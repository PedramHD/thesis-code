module Protocol

open SecrecyLabels

open CryptoEffect
module C = CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI

let create_initiate_event (a:principal) (b:principal) (n:C.bytes) =
  ("initiated", [CryptoLib.string_to_bytes a; CryptoLib.string_to_bytes b; n])

let create_receive_event (receiver:principal) (initiator:principal) (n:C.bytes) =
  ("received", [CryptoLib.string_to_bytes receiver; CryptoLib.string_to_bytes initiator; n])

let pke_predicate (i:timestamp) (s:string) (pk:C.bytes) (plaintext:C.bytes) : prop =
  match s with
  | "enc_key" -> (
     exists  enc_priv_key' initiator_from_plaintext' shared_secret' receiver'.
       pk == C.pk enc_priv_key' /\
       get_label default_key_usages enc_priv_key' == (readers [P receiver']) /\
       plaintext == C.concat (C.string_to_bytes initiator_from_plaintext') shared_secret' /\
       did_event_occur_before i initiator_from_plaintext' (create_initiate_event initiator_from_plaintext' receiver' shared_secret')
  )
  | _ -> False

let sign_predicate (i:timestamp) (s:string) (verification_key:C.bytes) (msg:C.bytes) : prop =
  match s with
  | "running_example_sig_key" -> (
     exists plaintext' enc_priv_key' nonce' initiator_from_plaintext' shared_secret' receiver'.
       get_label default_key_usages enc_priv_key' == (readers [P receiver']) /\
       msg == C.pke_enc (C.pk enc_priv_key') nonce' plaintext' /\
       plaintext' == C.concat (C.string_to_bytes initiator_from_plaintext') shared_secret' /\
       was_rand_generated_before i shared_secret' (readers [P initiator_from_plaintext'; P receiver']) (C.nonce_usage "running_example_shared_secret") /\
       did_event_occur_before i initiator_from_plaintext' (create_initiate_event initiator_from_plaintext' receiver' shared_secret')
  )
  | _ -> False


let aead_predicate t s pk m ad : prop = False
let mac_predicate t s pk m : prop  = False


let usage_preds:usage_preds = {
  can_pke_encrypt = pke_predicate;
  can_aead_encrypt = aead_predicate;
  can_sign = sign_predicate;
  can_mac = mac_predicate
}

let global_crypto_usage:global_usage = {
  usage_preds = usage_preds;
  key_usages = default_key_usages;
}


noeq type example_session_st =
  |InitiatorSentMsg: recv:principal -> n:C.bytes -> example_session_st
  |ResponderReceivedMsg: init:principal -> n:C.bytes -> example_session_st


let parse_session_st (session:C.bytes) : result example_session_st =
  match C.split session with
  | Error _ -> Error "cannot split session (1)"
  | Success (tag_bytes, principal_nonce) -> (
    match C.split principal_nonce with
    | Error _ -> Error "cannot split session (2)"
    | Success (p_bytes, nonce) -> (
      match C.bytes_to_string p_bytes with
      | Error _ -> Error "expected string for principal"
      | Success p -> (
        match C.bytes_to_string tag_bytes with
        | Success "InitiatorSentMsgSession" -> Success (InitiatorSentMsg p nonce)
        | Success "ResponderReceivedMsgSession" -> Success (ResponderReceivedMsg p nonce)
        | _ -> Error "wrong session type"
      )
    )
  )


let initiator_stores_nonce_in_state (initiator:principal) (receiver:principal) (nonce:CryptoLib.bytes) (state_vec:state_vec) (si:nat) =
  si < Seq.Base.length state_vec /\ (
    let session_bytes = state_vec.[si] in
      match LabeledPKI.parse_session_st session_bytes with
      | Success (APP labeledpki_session_bytes) -> (
        match Protocol.parse_session_st labeledpki_session_bytes with
        | Success (InitiatorSentMsg receiver_stored_in_state shared_secret_stored_in_state) -> (
                    receiver_stored_in_state == receiver /\
                    shared_secret_stored_in_state == nonce
        )
        | _ -> False
      )
      | _ -> False
    )


let event_predicate (i:nat) p (e:event) : prop =
  match e with
  | ("initiated", [initiator_bytes; responder_bytes; nonce]) -> (
    match CryptoLib.bytes_to_string initiator_bytes, CryptoLib.bytes_to_string responder_bytes with
    | Success initiator, Success responder -> (
        i > 0 /\
        was_rand_generated_before i nonce (readers [P initiator; P responder]) (C.nonce_usage "running_example_shared_secret") /\
        (exists (state_vec:state_vec) (vvec:version_vec) (si:nat).
          si < Seq.Base.length state_vec /\
          state_was_set_at (i-1) initiator vvec state_vec /\
          initiator_stores_nonce_in_state initiator responder nonce state_vec si
        )
      )
    | _, _ -> False
  )
  | ("received", [receiver_bytes; initiator_bytes; nonce]) -> (
    match CryptoLib.bytes_to_string initiator_bytes, CryptoLib.bytes_to_string receiver_bytes with
    | Success initiator, Success receiver ->
        LabeledCryptoAPI.corrupt_id i (P initiator) \/
        did_event_occur_before i initiator (create_initiate_event initiator receiver nonce)
    | _, _ -> False
  )
  | _ -> True

let serialize_session_st (session:example_session_st) : C.bytes =
  match session with
  |InitiatorSentMsg receiver nonce -> C.concat (C.string_to_bytes "InitiatorSentMsgSession") (C.concat (C.string_to_bytes receiver) nonce)
  |ResponderReceivedMsg initiator nonce -> C.concat (C.string_to_bytes "ResponderReceivedMsgSession") (C.concat (C.string_to_bytes initiator) nonce)


let parse_serialize_session_st_lemma (st:example_session_st) :
    Lemma (
      match parse_session_st (serialize_session_st st) with
      | Error _ -> False
      | Success parsed_st -> parsed_st == st
      )
      = ()


let serialize_parse_session_st_lemma (b:C.bytes) :
    Lemma (
      match parse_session_st b with
      | Error _ -> True
      | Success session_state -> serialize_session_st session_state == b
      )
    =
    match C.split b with
    | Error _ -> ()
    | Success (tag_bytes, principal_nonce) -> (
      match C.split principal_nonce with
      | Error _ -> ()
      | Success (p_bytes, nonce) -> (
        match C.bytes_to_string p_bytes with
        | Error _ -> ()
        | Success p -> (
          C.bytes_to_string_lemma tag_bytes;
          C.bytes_to_string_lemma p_bytes;
          C.concat_split_lemma principal_nonce;
          C.concat_split_lemma b;
          (
          match C.bytes_to_string tag_bytes with
          | Success "InitiatorSentMsgSession" -> ()
          | Success "ResponderReceivedMsg" -> ()
          | _ -> ()
          )
        )
      )
    )

let valid_state_session (gu:global_usage) (i:timestamp) (p:principal) (st:example_session_st): prop =
  match st with
  | (InitiatorSentMsg receiver shared_secret) -> was_rand_generated_before i shared_secret (readers [P p; P receiver]) (C.nonce_usage "running_example_shared_secret")
  | (ResponderReceivedMsg initiator shared_secret) -> (corrupt_id i (P initiator) /\ is_publishable gu i shared_secret) \/ was_rand_generated_before i shared_secret (readers [P initiator; P p]) (C.nonce_usage "running_example_shared_secret")


let labeled_serialize_session_st (gu:global_usage) (i:timestamp) (p:principal) (si:nat) (vi:nat) (session:example_session_st{valid_state_session gu i p session}) : serialized_st:msg gu i (readers [V p si vi]) {serialized_st == serialize_session_st session}=
  match session with
  |InitiatorSentMsg receiver nonce -> (
    rand_is_secret #gu #i #(readers [P p; P receiver]) #(C.nonce_usage "running_example_shared_secret") nonce;
    assert(can_flow i (get_label gu.key_usages nonce) (readers [V p si vi]));
    concat (string_to_bytes #gu #i "InitiatorSentMsgSession") (concat (string_to_bytes #gu #i receiver) nonce)
  )
  |ResponderReceivedMsg initiator nonce -> (
    rand_is_secret #gu #i #(readers [P initiator; P p]) #(C.nonce_usage "running_example_shared_secret") nonce;
    assert(corrupt_id i (P initiator) \/ can_flow i (get_label gu.key_usages nonce) (readers [V p si vi]));
    concat (string_to_bytes #gu #i "ResponderReceivedMsgSession") (concat (string_to_bytes #gu #i initiator) nonce)
  )


let parse_labeled_serialize_session_st_lemma (gu:global_usage) (i:timestamp) (p:principal) (si:nat) (vi:nat) (st:example_session_st{valid_state_session gu i p st}) :
    Lemma (
      match parse_session_st (labeled_serialize_session_st gu i p si vi st) with
      | Error _ -> False
      | Success parsed_st -> parsed_st == st
      )
      = ()


let state_invariant (gu:global_usage) (i:timestamp) (p:principal) (si:nat) (vi:nat) (st:C.bytes) : prop =
  is_msg gu i st (readers [V p si vi]) /\
  (
    match parse_session_st st with
    | Success parsed_state -> valid_state_session gu i p parsed_state
    | _ -> False
  )


let trace_predicates (gu:global_usage) : trace_preds gu = {
  can_trigger_event = event_predicate;
  session_st_inv = state_invariant gu;
  session_st_inv_lemma = (fun i p si vi st -> ());
  session_st_inv_later = (fun i j p si vi st -> ());
}


let predicates:preds = {
  global_usage = global_crypto_usage;
  trace_preds = trace_predicates global_crypto_usage
}

let initiator_encrypt_then_sign_message
  (i:timestamp)
  (initiator: principal)
  (receiver:principal)
  (shared_secret:secret global_crypto_usage i (readers [P initiator; P receiver]) (C.nonce_usage "running_example_shared_secret"))
  (pub_key_of_b: public_enc_key global_crypto_usage i (readers [P receiver]) "enc_key")
  (sig_key_of_a: sign_key global_crypto_usage i (readers [P initiator]) "running_example_sig_key")
  :
  LCrypto (final_message:C.bytes) (pki predicates)
  (requires (fun t0 -> i <= trace_len t0 /\ was_rand_generated_before i shared_secret (readers [P initiator; P receiver]) (C.nonce_usage "running_example_shared_secret") /\
  (did_event_occur_before i initiator (create_initiate_event initiator receiver shared_secret))
  ))
  (ensures (fun t0 res t1 -> is_msg global_crypto_usage (trace_len t1) res public))
  =
  let initiator_bytes = string_to_bytes #global_crypto_usage #i initiator in
  let (initiator_bytes_nonce:msg global_crypto_usage i (readers [P initiator; P receiver])) = concat initiator_bytes shared_secret in

  let (|t1,enc_rand|) = rand_gen #predicates (readers [P initiator; P receiver]) (C.nonce_usage "PKE_NONCE") in

  assert(is_publishable global_crypto_usage i pub_key_of_b);
  assert(later_than t1 i);
  is_public_enc_key_later_lemma global_crypto_usage i pub_key_of_b (readers [P receiver]) "enc_key";
  assert(is_publishable global_crypto_usage t1 pub_key_of_b);
  rand_is_secret #global_crypto_usage #t1 #(readers [P initiator; P receiver]) #(C.nonce_usage "PKE_NONCE") enc_rand;

  sk_label_lemma global_crypto_usage t1 pub_key_of_b (readers [P receiver]);
  assert(get_sk_label global_crypto_usage.key_usages pub_key_of_b == readers [P receiver]);
  assert(can_flow t1 (readers [P initiator; P receiver]) (readers [P receiver]));
  assert(is_msg global_crypto_usage t1 initiator_bytes_nonce (readers [P receiver]));
  assert(can_flow t1 (get_label global_crypto_usage.key_usages initiator_bytes_nonce) (readers [P initiator; P receiver]));


  assert(exists sk. pub_key_of_b == C.pk sk);

    assert(exists  enc_priv_key'.
       get_label default_key_usages enc_priv_key' == (readers [P receiver]) /\
       get_usage default_key_usages enc_priv_key' == Some (C.pke_usage "enc_key") /\
       initiator_bytes_nonce == C.concat (C.string_to_bytes initiator) shared_secret /\
       was_rand_generated_before t1 shared_secret (readers [P initiator; P receiver]) (C.nonce_usage "running_example_shared_secret")
  );

  assert(pke_predicate t1 "enc_key" pub_key_of_b initiator_bytes_nonce);

  let (ciphertext:msg global_crypto_usage t1 public) = pke_enc #global_crypto_usage #t1 #(readers [P initiator; P receiver]) pub_key_of_b enc_rand initiator_bytes_nonce in

  let (|t2, sig_nonce|) = rand_gen #predicates (readers [P initiator]) (C.nonce_usage "SIG_NONCE") in

  assert(ciphertext == C.pke_enc pub_key_of_b enc_rand initiator_bytes_nonce);
  assert(exists plaintext' nonce' pubkey'. ciphertext == C.pke_enc pubkey' nonce' plaintext');
  assert(exists sk. pub_key_of_b == C.pk sk);
  assert(exists sk. ciphertext == C.pke_enc (C.pk sk) enc_rand initiator_bytes_nonce /\
    is_secret global_crypto_usage i sk (readers [P receiver]) (C.pke_usage "enc_key") /\
    get_label default_key_usages sk == (readers [P receiver]) /\
    get_usage default_key_usages sk == Some (C.pke_usage "enc_key")
  );
  assert(initiator_bytes_nonce == C.concat (C.string_to_bytes initiator) shared_secret);

  assert(was_rand_generated_before i shared_secret (readers [P initiator; P receiver]) (C.nonce_usage "running_example_shared_secret"));


  assert(
     exists plaintext' enc_priv_key' nonce' initiator_from_plaintext' shared_secret' receiver'.
       get_label default_key_usages enc_priv_key' == (readers [P receiver']) /\
       get_usage default_key_usages enc_priv_key' == Some (C.pke_usage "enc_key") /\
       ciphertext == C.pke_enc (C.pk enc_priv_key') nonce' plaintext' /\
       plaintext' == C.concat (C.string_to_bytes initiator_from_plaintext') shared_secret' /\
       was_rand_generated_before i shared_secret' (readers [P initiator_from_plaintext'; P receiver']) (C.nonce_usage "running_example_shared_secret")
  );


  assert(sign_predicate i "running_example_sig_key" (C.vk sig_key_of_a) ciphertext);
  assert(later_than t2 i);
  assert(was_rand_generated_before t2 shared_secret (readers [P initiator; P receiver]) (C.nonce_usage "running_example_shared_secret"));
  assert(sign_predicate t2 "running_example_sig_key" (C.vk sig_key_of_a) ciphertext);

  let signature_tag = sign #global_crypto_usage #t2 #(readers [P initiator]) #public sig_key_of_a sig_nonce ciphertext in

  let now = global_timestamp () in

  let signature_tag_and_ciphertext = concat #global_crypto_usage #now #public ciphertext signature_tag in
  signature_tag_and_ciphertext


let initiator_send_message (initiator:principal) (receiver:principal) :
  LCrypto (message_idx:nat) (pki predicates)
  (requires (fun _ -> True))
  (ensures (fun t0 output t1 ->
    output < trace_len t1 /\
    output >= trace_len t0
  ))
  =
  let (|t0, n_initiator|) = LabeledPKI.rand_gen #predicates (readers [P initiator; P receiver]) (C.nonce_usage "running_example_shared_secret") in
  let t_now = global_timestamp () in
  let pub_key_of_b = LabeledPKI.get_public_key #predicates #t_now initiator receiver PKE "enc_key" in

  let (|_, sig_key_of_a|) = LabeledPKI.get_private_key #predicates #t_now initiator SIG "running_example_sig_key" in

  let now = global_timestamp () in
  let session_state = InitiatorSentMsg receiver n_initiator in
  let si = LabeledPKI.new_session_number #predicates initiator in
  let serialized_st = (labeled_serialize_session_st global_crypto_usage now initiator si 0 session_state) in
  assert(is_msg global_crypto_usage now serialized_st (readers [V initiator si 0]));
  parse_labeled_serialize_session_st_lemma global_crypto_usage now initiator si 0 session_state;
  assert(
    match parse_session_st serialized_st with
    | Success (InitiatorSentMsg receiver shared_secret) -> valid_state_session global_crypto_usage now initiator (InitiatorSentMsg receiver shared_secret)
    | _ -> False
  );

  let t_before_setting_state = global_timestamp () in
  LabeledPKI.new_session #predicates #now initiator si 0 serialized_st;

  assert(exists (state_vec:state_vec) (vvec:version_vec) (app_state:CryptoLib.bytes).
        state_was_set_at t_before_setting_state initiator vvec state_vec /\
        si < Seq.Base.length state_vec /\
        state_vec.[si] == app_state /\
        LabeledPKI.parse_session_st app_state == Success (APP serialized_st)
    );


  assert(exists (state_vec:state_vec) (vvec:version_vec) (app_state:CryptoLib.bytes).
    si < Seq.Base.length state_vec /\
    state_was_set_at t_before_setting_state initiator vvec state_vec /\
    initiator_stores_nonce_in_state initiator receiver n_initiator state_vec si
  );

  assert(exists (state_vec:state_vec) (vvec:version_vec) (si:nat).
    si < Seq.Base.length state_vec /\
    state_was_set_at t_before_setting_state initiator vvec state_vec /\
    initiator_stores_nonce_in_state initiator receiver n_initiator state_vec si
  );

  let (sent_event:event) = create_initiate_event initiator receiver n_initiator in
  let now = global_timestamp () in

  assert(now-1 = t_before_setting_state);

  assert(event_predicate now initiator sent_event);

  LabeledPKI.trigger_event #predicates initiator sent_event;

  let t_now = global_timestamp () in
  assert(did_event_occur_before t_now initiator (create_initiate_event initiator receiver n_initiator));

  let message:C.bytes = initiator_encrypt_then_sign_message t_now initiator receiver n_initiator pub_key_of_b sig_key_of_a in
  let t_now = global_timestamp () in
  assert(is_msg global_crypto_usage t_now message public);
  let (message:msg global_crypto_usage t_now public) = message in
  let send_index = LabeledPKI.send #predicates #t_now initiator receiver message in
  send_index


let sign_predicate_true_later_forall vk m : Lemma (forall i j. later_than j i /\ (sign_predicate i "running_example_sig_key" vk m) ==> (sign_predicate j "running_example_sig_key" vk m)) =
  let sign_predicate_true_later_forall_helper i j vk m :
      Lemma
      (requires (later_than j i /\ (sign_predicate i "running_example_sig_key" vk m)))
      (ensures (sign_predicate j "running_example_sig_key" vk m))
      [SMTPat (later_than j i); SMTPat (sign_predicate i "running_example_sig_key" vk m)] =
      assert(later_than j i);
      assert(forall a b c k l. later_than l k /\ was_rand_generated_before k a b c ==> was_rand_generated_before l a b c);
      assert_norm(
       exists plaintext' enc_priv_key' nonce' initiator_from_plaintext' shared_secret' receiver'.
         m == C.pke_enc (C.pk enc_priv_key') nonce' plaintext' /\
         plaintext' == C.concat (C.string_to_bytes initiator_from_plaintext') shared_secret' /\
         was_rand_generated_before j shared_secret' (readers [P initiator_from_plaintext'; P receiver']) (C.nonce_usage "running_example_shared_secret")
      );
      ()
  in
()


let receiver_process_message
  (i:timestamp)
  (receiver:principal)
  (initiator: principal)
  (nw_message:msg global_crypto_usage i public)
  :
  LCrypto (shared_secret:C.bytes) (pki predicates)
  (requires (fun t0 -> i <= trace_len t0))
  (ensures (fun t0 res t1 ->
    (corrupt_id (trace_len t1) (P initiator) /\ is_publishable global_crypto_usage (trace_len t1) res) \/
    (
      was_rand_generated_before (trace_len t1) res (readers [P initiator; P receiver]) (C.nonce_usage "running_example_shared_secret") /\
      did_event_occur_before (trace_len t1) initiator (create_initiate_event initiator receiver res)
    )))
  =
  let t_now = global_timestamp () in
  let verification_key_of_a = LabeledPKI.get_public_key #predicates #t_now receiver initiator SIG "running_example_sig_key" in
  let (|_, priv_key_of_b|) = LabeledPKI.get_private_key #predicates #t_now receiver PKE "enc_key" in
  assert(later_than t_now i);
  (
  match split nw_message with
  | Error _ -> error "cannot split the message into ciphertext and signature tag"
  | Success (ciphertext, signature) -> (
    if(verify #global_crypto_usage #t_now #public #public verification_key_of_a ciphertext signature) then (
      assert(can_flow t_now (readers [P initiator]) public \/ sign_pred global_crypto_usage.usage_preds t_now "running_example_sig_key" verification_key_of_a ciphertext);
      assert(corrupt_id t_now (P initiator) \/ sign_pred global_crypto_usage.usage_preds t_now "running_example_sig_key" verification_key_of_a ciphertext);

      match pke_dec #global_crypto_usage #t_now #(readers [P receiver]) priv_key_of_b ciphertext with
      | Error _ -> error "cannot decrypt message"
      | Success plaintext ->
        assert(forall s. is_private_dec_key global_crypto_usage t_now priv_key_of_b (readers [P receiver]) s ==> (is_publishable global_crypto_usage t_now plaintext \/ pke_pred global_crypto_usage.usage_preds t_now s (C.pk priv_key_of_b) plaintext));
        assert(is_private_dec_key global_crypto_usage t_now priv_key_of_b (readers [P receiver]) "enc_key");
        assert(is_publishable global_crypto_usage t_now plaintext \/ pke_pred global_crypto_usage.usage_preds t_now "enc_key" (C.pk priv_key_of_b) plaintext);

        match split plaintext with
        | Error _ -> error "cannot split plaintext"
        | Success (initiator_bytes, shared_secret) -> (

              C.split_based_on_split_len_prefixed_lemma plaintext;
              assert(C.is_succ2 (C.split_len_prefixed 4 plaintext) initiator_bytes shared_secret);
              splittable_term_publishable_implies_components_publishable_forall global_crypto_usage;
              assert(is_publishable global_crypto_usage t_now plaintext ==> is_publishable global_crypto_usage t_now shared_secret);
         (


          match bytes_to_string initiator_bytes with
          | Error _ -> error "cannot parse initiator information in plaintext"
          | Success initiator_from_plaintext -> (
            if (initiator_from_plaintext <> initiator) then error "wrong sender in plaintext"
            else (
              let t_now = global_timestamp () in

              assert(corrupt_id t_now (P initiator) \/ sign_pred global_crypto_usage.usage_preds t_now "running_example_sig_key" verification_key_of_a ciphertext);
              assert(is_publishable global_crypto_usage t_now plaintext \/ pke_pred global_crypto_usage.usage_preds t_now "enc_key" (C.pk priv_key_of_b) plaintext);
              assert(can_flow t_now (get_label global_crypto_usage.key_usages plaintext) (readers [P receiver]));


              assert(sign_pred global_crypto_usage.usage_preds t_now "running_example_sig_key" verification_key_of_a ciphertext ==>
                (exists t_earlier. later_than t_now t_earlier /\ sign_predicate t_earlier "running_example_sig_key" verification_key_of_a ciphertext)
                );

              sign_predicate_true_later_forall verification_key_of_a ciphertext;

              assert(sign_pred global_crypto_usage.usage_preds t_now "running_example_sig_key" verification_key_of_a ciphertext ==>
                (sign_predicate t_now "running_example_sig_key" verification_key_of_a ciphertext)
                );


              assert(
                pke_pred global_crypto_usage.usage_preds t_now "enc_key" (C.pk priv_key_of_b) plaintext ==>
                sign_pred global_crypto_usage.usage_preds t_now "running_example_sig_key" verification_key_of_a ciphertext
                );


              assert(is_private_dec_key global_crypto_usage t_now priv_key_of_b (readers [P receiver]) "enc_key");

              readers_is_injective receiver;

              assert(corrupt_id t_now (P initiator) \/
                  (
                      was_rand_generated_before t_now shared_secret (readers [P initiator_from_plaintext; P receiver]) (C.nonce_usage "running_example_shared_secret")
                  )
              );


              assert(is_publishable global_crypto_usage t_now shared_secret \/
                  (
                      was_rand_generated_before t_now shared_secret (readers [P initiator_from_plaintext; P receiver]) (C.nonce_usage "running_example_shared_secret")
                  )
              );
              assert((corrupt_id t_now (P initiator) /\ is_publishable global_crypto_usage t_now shared_secret) \/ was_rand_generated_before t_now shared_secret (readers [P initiator; P receiver]) (C.nonce_usage "running_example_shared_secret"));
              shared_secret
            )
          )
        )
  )
    )
    else error "invalid signature"
  )
  )

let receiver_receive_message (receiver:principal) (message_idx:nat) :
  LCrypto unit (pki predicates)
  (requires (fun t0 -> message_idx < trace_len t0))
  (ensures (fun _ _ _ -> True))
  =
  let (|t0, sender_from_message_entry, message|) = receive_i #predicates message_idx receiver in
  let shared_secret = receiver_process_message t0 receiver sender_from_message_entry message in

  let (received_event:event) = create_receive_event receiver sender_from_message_entry shared_secret in
  let now = global_timestamp () in
  assert(corrupt_id now (P sender_from_message_entry) \/ did_event_occur_before now sender_from_message_entry (create_initiate_event sender_from_message_entry receiver shared_secret));
  assert(event_predicate now receiver received_event);
  LabeledPKI.trigger_event #predicates receiver received_event;

  let now = global_timestamp () in
  let session_state = ResponderReceivedMsg sender_from_message_entry shared_secret in
  let si = LabeledPKI.new_session_number #predicates receiver in
  assert(corrupt_id now (P sender_from_message_entry) \/ was_rand_generated_before now shared_secret (readers [P sender_from_message_entry; P receiver]) (C.nonce_usage "running_example_shared_secret"));
  assert(valid_state_session global_crypto_usage now receiver session_state);
  let serialized_st = (labeled_serialize_session_st global_crypto_usage now receiver si 0 session_state) in
  parse_labeled_serialize_session_st_lemma global_crypto_usage now receiver si 0 session_state;
  LabeledPKI.new_session #predicates #now receiver si 0 serialized_st
