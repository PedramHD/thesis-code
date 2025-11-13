module Protocol

open SecrecyLabels
open CryptoEffect
module C = CryptoLib
open GlobalRuntimeLib
open SimplePKI

let create_initiate_event (a:principal) (b:principal) (n:C.bytes) =
  ("initiated", [CryptoLib.string_to_bytes a; CryptoLib.string_to_bytes b; n])

let create_receive_event (receiver:principal) (initiator:principal) (n:C.bytes) =
  ("received", [CryptoLib.string_to_bytes receiver; CryptoLib.string_to_bytes initiator; n])

noeq type example_session_st =
  |InitiatorSentMsg: recv:principal -> n:C.bytes -> example_session_st
  |ReceiverReceivedMsg: init:principal -> n:C.bytes -> example_session_st

val parse_session_st: (session:C.bytes) -> result example_session_st

let parse_session_st session : result example_session_st =
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
        | Success "ReceiverReceivedMsgSession" -> Success (ReceiverReceivedMsg p nonce)
        | _ -> Error "wrong session type"
      )
    )
  )

val serialize_session_st: (session:example_session_st) -> C.bytes

let serialize_session_st session : C.bytes =
  match session with
  |InitiatorSentMsg receiver nonce ->
    C.concat (C.string_to_bytes "InitiatorSentMsgSession") (C.concat (C.string_to_bytes receiver) nonce)
  |ReceiverReceivedMsg initiator nonce ->
    C.concat (C.string_to_bytes "ReceiverReceivedMsgSession") (C.concat (C.string_to_bytes initiator) nonce)

let parse_serialize_session_st_lemma (st:example_session_st) :
    Lemma (
      match parse_session_st (serialize_session_st st) with
      | Error _ -> False
      | Success parsed_st -> parsed_st == st
      )
      = ()

let initiator_encrypt_then_sign_message
  (initiator: principal)
  (receiver:principal)
  (shared_secret: C.bytes)
  (pub_key_of_b: C.bytes)
  (sig_key_of_a: C.bytes)
  :
  Crypto (final_message:C.bytes)
  (requires (fun t0 -> True))
  (ensures (fun t0 r t1 -> match r with |Error _ -> True | Success _ -> trace_len t1 > trace_len t0))
  =
  let initiator_bytes = C.string_to_bytes initiator in
  let initiator_bytes_nonce = C.concat initiator_bytes shared_secret in
  let enc_rand = gen public (C.nonce_usage "PKE_NONCE") in
  let ciphertext = C.pke_enc  pub_key_of_b enc_rand initiator_bytes_nonce in
  let sig_nonce = gen (readers [P initiator]) (C.nonce_usage "SIG_NONCE") in
  let signature_tag = C.sign sig_key_of_a sig_nonce ciphertext in
  let signature_tag_and_ciphertext = C.concat ciphertext signature_tag in
  signature_tag_and_ciphertext


let initiator_send_message (initiator:principal) (receiver:principal) :
  Crypto (message_idx:nat)
  (requires (fun _ -> True))
  (ensures (fun t0 res t1 ->
    match res with
    | Error _ -> True
    | Success output -> (
        output < trace_len t1 /\
        output >= trace_len t0
    )
  ))
  =
  let n_initiator = gen public (C.nonce_usage "running_example_shared_secret") in
  let pub_key_of_b = get_public_key initiator receiver PKE "enc_key" in

  let (|_, sig_key_of_a|) = SimplePKI.get_private_key initiator SIG "running_example_sig_key" in

  let session_state = InitiatorSentMsg receiver n_initiator in
  let si = SimplePKI.new_session_number initiator in
  let serialized_st = serialize_session_st session_state in

  SimplePKI.new_session initiator si 0 serialized_st;

  let (sent_event:event) = create_initiate_event initiator receiver n_initiator in
  trigger_event initiator sent_event;

  let message:C.bytes = initiator_encrypt_then_sign_message initiator receiver n_initiator pub_key_of_b sig_key_of_a in
  let send_index = send initiator receiver message in
  send_index


let receiver_process_message
  (receiver:principal)
  (initiator: principal)
  (nw_message:C.bytes)
  :
  Crypto (shared_secret:C.bytes)
  (requires (fun t0 -> True))
  (ensures (fun t0 res t1 -> True))
  =
  let verification_key_of_a = SimplePKI.get_public_key receiver initiator SIG "running_example_sig_key" in
  let (|_, priv_key_of_b|) = SimplePKI.get_private_key receiver PKE "enc_key" in (
  match C.split nw_message with
  | Error _ -> error "cannot split the message into ciphertext and signature tag"
  | Success (ciphertext, signature) -> (
    if(C.verify verification_key_of_a ciphertext signature) then (
      match C.pke_dec priv_key_of_b ciphertext with
      | Error _ -> error "cannot decrypt message"
      | Success plaintext ->
        match C.split plaintext with
        | Error _ -> error "cannot split plaintext"
        | Success (initiator_bytes, shared_secret) -> (
          match C.bytes_to_string initiator_bytes with
          | Error _ -> error "cannot parse initiator information in plaintext"
          | Success initiator_from_plaintext -> (
            if (initiator_from_plaintext <> initiator) then error "wrong sender in plaintext"
            else shared_secret
          )
        )
      )
    else error "invalid signature"
    )
  )

let receiver_receive_message (receiver:principal) (message_idx:nat) :
  Crypto unit
  (requires (fun t0 -> message_idx < trace_len t0))
  (ensures (fun _ _ _ -> True))
  =
  let (sender_from_message_entry, message) = receive_i message_idx receiver in
  let shared_secret = receiver_process_message receiver sender_from_message_entry message in
  let (received_event:event) = create_receive_event receiver sender_from_message_entry shared_secret in
  trigger_event receiver received_event;
  let session_state = ReceiverReceivedMsg sender_from_message_entry shared_secret in
  let si = SimplePKI.new_session_number receiver in
  let serialized_st = (serialize_session_st session_state) in
  SimplePKI.new_session receiver si 0 serialized_st
