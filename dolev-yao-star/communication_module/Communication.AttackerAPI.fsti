/// Communication.AttackerAPI
/// ==========================
///
/// API for attacker

module Communication.AttackerAPI


open SecrecyLabels
open CryptoLib
module C = CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI
open Communication.MessageStructurePredicates
open Communication.UsagePredicates
open Communication.Sessions
open Communication.Preds
open Communication.Sessions.Lemmas
open Communication.CoreFunctions



(**
  This does the same as [initiator_send_request], but with a symmetric key that is public and
  returning the key (instead of storing it into some state).
*)
val initiator_send_request_attacker_function:
    #i:timestamp ->
    #higher_level_preds:send_layer_preds ->
    sender:principal ->
    receiver:principal ->
    message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) i public ->
    LCrypto (message_idx:timestamp & sym_key:bytes) (pki (send_preds higher_level_preds))
    (requires (fun t0 ->
      (i <= trace_len t0) /\
      (trace_len t0 > 0)
    ))
    (ensures (fun t0 message_idx t1 -> True
    ))
