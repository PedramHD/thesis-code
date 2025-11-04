/// Communication.Sessions.Lemmas
/// =============================

module Communication.Sessions.Lemmas

open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib
open Communication.UsagePredicates
open Communication.Sessions
open Communication.Preds

module LC = LabeledCryptoAPI
module LR = LabeledRuntimeAPI


(**
  If a CommunicationState session is valid (according to [valid_session]), then the serialized session
  state flows to the sender and the responder, and the serialized state is valid.
*)
val serialized_session_st_flows_to_principal_state_session:
  (pr:send_layer_preds) ->
  (gu:LC.global_usage) ->
  (i:timestamp) ->
  (p:principal) ->
  (si:nat) ->
  (vi:nat) ->
  (st:session_st) ->
  Lemma
  (requires (
    valid_session pr i p si vi st
  ))
  (ensures (
   match st with
   | CommunicationState request_send_idx sym_key _ -> (
     let serialized_session_st = (serialize_session_st st) in
     LC.can_flow i (LC.get_label gu.LC.key_usages serialized_session_st) (readers [V p si vi]) /\
     LC.is_valid gu i serialized_session_st
   )
   | APP _ -> True
  ))


val parse_serialize_session_st_lemma : ss:session_st ->
    Lemma (Success ss == parse_session_st (serialize_session_st ss))
          [SMTPat (parse_session_st (serialize_session_st ss))]


(**
  Serialization and parsing of APP states preserve [is_msg]:
*)

val serialized_session_st_is_msg: (extended_gu:extended_global_usage) -> (i:timestamp) -> (l:label) -> (ss:bytes) ->
  Lemma
  (requires (
    LC.is_msg (send_preds_global_usage extended_gu) i ss l
  ))
  (ensures (
    LC.is_msg (send_preds_global_usage extended_gu) i (serialize_session_st (APP ss)) l
  ))


val parsed_app_session_st_is_msg: (extended_gu:extended_global_usage) -> (i:timestamp) -> (l:label) -> (ss:bytes) ->
  Lemma
  (requires (
    LC.is_msg (send_preds_global_usage extended_gu) i ss l
  ))
  (ensures (
    match parse_session_st ss with
    | Success (APP app_state) -> (
      LC.is_msg (send_preds_global_usage extended_gu) i app_state l
    )
    | _ -> True
  ))

