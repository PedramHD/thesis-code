/// BA.Protocol
/// ==============

module BA.Protocol
open SecrecyLabels
open CryptoLib
open GlobalRuntimeLib
module LCA = LabeledCryptoAPI
open Communication.CryptoLib

open LabeledRuntimeAPI
open LabeledPKI
module A = AttackerAPI
module S = Communication.Layer

open BA.Messages
open BA.Sessions
open BA.Preds
open BA.Labeled.SerializingParsing

(*! Account Registration Phase *)

(**
    This function stores the responder and password into the [app_data_session_idx] of the state of the initiator.
    The initiator function for sending the access request uses this session index to find the password used for this session.
*)
val initiator_send_account_registration_request:
  #i:timestamp ->
  initiator:principal ->
  responder:principal ->
  password:secret gu i (readers [P initiator; P responder]) (nonce_usage "BA.Password") ->
  LCrypto (result (sym_key_state_session_idx:nat & app_data_session_idx:nat & send_index:nat)) (pki (Communication.Layer.send_preds ba_preds))
  (requires fun t0 -> i <= trace_len t0 /\
  (was_rand_generated_before (trace_len t0) password (readers [(P initiator); (P responder)]) (nonce_usage "BA.Password")))
  (ensures fun t0 _ t1 -> True)


val responder_receive_account_registration_request_and_respond:
  receiver:principal ->
  recv_idx:nat ->
  LCrypto (result (send_index:nat & state_index:nat)) (pki (Communication.Layer.send_preds ba_preds))
  (requires fun t0 -> True)
  (ensures fun t0 _ t1 -> True)

val initiator_process_account_registration_response:
  initiator:principal ->
  sym_key_state_session_idx:nat ->
  send_idx:nat ->
  LCrypto (msg_status:result string) (pki (Communication.Layer.send_preds ba_preds))
  (requires fun t0 -> True)
  (ensures fun t0 _ t1 -> True)


(*! Access Phase *)

(** The initator uses the password stored in the [app_data_session_idx] 
    (returned by the initiator function for generating the account generation request)
*)
val initiator_send_get_secret_request:
  #i:timestamp ->
  initiator:principal ->
  app_data_session_idx:nat ->
  LCrypto (result (sym_key_state_session_idx:nat & send_index:nat)) (pki (Communication.Layer.send_preds ba_preds))
  (requires fun t0 -> i <= trace_len t0)
  (ensures fun t0 _ t1 -> True)

val responder_receive_get_secret_request_and_respond:
  receiver:principal ->
  recv_idx:nat ->
  LCrypto (result (send_index:nat)) (pki (Communication.Layer.send_preds ba_preds))
  (requires fun t0 -> True)
  (ensures fun t0 _ t1 -> True)


val initiator_process_response_with_secret:
  initiator:principal ->
  sym_key_state_session_idx:nat ->
  send_idx:nat ->
  LCrypto (result unit) (pki (Communication.Layer.send_preds ba_preds))
  (requires fun t0 -> True)
  (ensures fun t0 _ t1 -> True)
