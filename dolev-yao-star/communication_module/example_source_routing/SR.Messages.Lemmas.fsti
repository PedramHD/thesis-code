/// SR.Messages.Lemmas (interface)
/// ==============================

module SR.Messages.Lemmas

open SecrecyLabels
open CryptoLib
module A = LabeledCryptoAPI
module LAPI = LabeledRuntimeAPI
module LPKI = LabeledPKI
open Communication.Layer
open SR.HelperFunctions
module SL = SecurityLemmas

open SR.Messages
open SR.Preds
open SR.LabeledSerializingParsing

(**
  If a byte can be parsed successfully using [parse_list_of_principals], then it is also publishable.
*)
val parse_list_of_principals_successful_implies_publishable: (b:bytes) -> (i:nat) -> (gu:extended_global_usage) ->
  Lemma
  (requires (Success? (parse_list_of_principals b)))
  (ensures (is_publishable gu i b))
  (decreases (term_depth b))

(**
  Lemma stating the main property of the [principal_in_list_corrupted_and_nonce_flows_to_public] predicate.
*)
val principal_in_list_corrupted_and_nonce_flows_to_public_lemma:
  (trace_length:timestamp) ->
  (i:timestamp) ->
  (principal_list:list principal) ->
  (nonce:bytes) ->
  Lemma (ensures (
    ((i <= trace_length) /\ (forall p. List.Tot.mem p principal_list ==> ~ (SL.corrupt_at trace_length (P p))))
     ==>
    ~ (principal_in_list_corrupted_and_nonce_flows_to_public i principal_list nonce)
  ))


(**
  If [principal_in_list_corrupted_and_nonce_flows_to_public] does not hold true for a trace index,
  it does not hold true for all previous trace indices. (If all principals in the principal list are
  honest at a given trace index, they must have been honest previously.)
*)
val principal_in_list_corrupted_and_nonce_flows_to_public_later_forall:
  (trace_idx:timestamp) ->
  (principal_list:list principal) ->
  (nonce:bytes) ->
  Lemma (ensures (forall (i:timestamp).
    (
      (~(principal_in_list_corrupted_and_nonce_flows_to_public trace_idx principal_list nonce)) /\
      later_than trace_idx i
    )
      ==> (~ (principal_in_list_corrupted_and_nonce_flows_to_public i principal_list nonce))
  ))


val parse_msg_preserves_is_msg: (#gu:extended_global_usage) -> (#i:timestamp) -> (#l:label) -> (m:msg gu i l) ->
  Lemma (ensures (
    match parse_msg m with
    | Success (Msg _ secret_nonce) -> is_msg gu i secret_nonce l
    | Success (MsgWithCounter _ _ secret_nonce) -> is_msg gu i secret_nonce l
    | _ -> True
  ))


val parse_msg_preserves_is_publishable: m:bytes ->
  Lemma (ensures (forall gu i. is_publishable gu i m ==>
  (
    let b:msg gu i public = m in
    (
      match parse_msg b with
      | Success (Msg _ secret_nonce) -> is_publishable gu i secret_nonce
      | Success (MsgWithCounter _ _ secret_nonce) -> is_publishable gu i secret_nonce
      | _ -> True
    )
  )
  ))


(**
  If a message can be parsed successfully and the corresponding list of principals contains the
  principals p1 and p2, then the send predicates imply that the label of the message can flow to
  (readers [P p1; P p2]).
*)
val parse_msg_label_lemma:
  #i:nat ->
  #l:label ->
  (msg:msg gu i l) ->
  p1:principal ->
  p2:principal ->
  Lemma
  (requires (
    match parse_msg msg with
    | Success (Msg principal_list secret_nonce) -> (
      List.Tot.mem p1 principal_list /\
      List.Tot.mem p2 principal_list
    )
    | Success (MsgWithCounter principal_list counter secret_nonce) -> (
      List.Tot.mem p1 principal_list /\
      List.Tot.mem p2 principal_list
    )
    | Error e -> False
  ))
  (ensures (
    match parse_msg msg with
    | Success (Msg principal_list secret_nonce) -> (
      (confidential_send_pred i msg) ==>
      LabeledCryptoAPI.can_flow i (LabeledCryptoAPI.get_label key_usages msg) (readers [P p1; P p2])
    )
    | Success (MsgWithCounter principal_list counter secret_nonce) -> (
      (authenticated_confidential_send_pred i msg) ==>
      LabeledCryptoAPI.can_flow i (LabeledCryptoAPI.get_label key_usages msg) (readers [P p1; P p2])
    )
    | Error e -> False
  ))




val principal_in_list_corrupted_and_nonce_flows_to_public_implies_nonce_flows_to_public:
  trace_idx:timestamp ->
  principal_list:list principal ->
  nonce:bytes ->
  Lemma (ensures (
    principal_in_list_corrupted_and_nonce_flows_to_public trace_idx  principal_list nonce ==>
    A.can_flow trace_idx (A.get_label key_usages nonce) public
  ))


(**
  Given a list of principals, a nonce that has a label corresponding to these principals, and two
  principals contained in the list of principals, the nonce can also flow to a readers-label
  containing just the two principals.
*)
val nonce_flows_to_principals_contained_in_principal_list:
  (i:timestamp) ->
  (gu:extended_global_usage) ->
  (p1:principal) ->
  (p2:principal) ->
  (nonce:bytes) ->
  (principal_list: list principal) ->
  Lemma
  (requires (
    is_labeled gu i nonce (readers (create_id_list_from_principal_list principal_list)) /\
    List.Tot.mem p1 principal_list /\
    List.Tot.mem p2 principal_list
  ))
  (ensures (
    is_msg gu i nonce (readers [P p1; P p2])
  ))


val authenticated_send_pred_holds_later: (i:timestamp) -> (j:timestamp) -> (m:bytes) ->
  Lemma (requires (
    (authenticated_send_pred i m) /\ (later_than j i)
  ))
  (ensures (
    authenticated_send_pred j m
  ))


val authenticated_confidential_send_pred_holds_later: (i:timestamp) -> (j:timestamp) -> (m:bytes) ->
  Lemma (requires (
    (authenticated_confidential_send_pred i m) /\ (later_than j i)
  ))
  (ensures (
    authenticated_confidential_send_pred j m
  ))


(**
  This lemma combines the guarantees provided by the authenticated channels with the
  authenticated_send_pred.
*)
val authn_send_pred_lemma: (i:nat) -> (p:principal) -> (received_serialized_msg:bytes) -> LAPI.LCrypto unit (LPKI.pki (Communication.Layer.send_preds sr_preds))
  (requires fun t0 ->
    (match parse_msg_raw received_serialized_msg with
    | Success (MsgWithCounter principal_list counter nonce) ->
      (List.Tot.mem p principal_list) /\
      (
        is_publishable gu i nonce /\
        (A.corrupt_id i (P p)  \/ (exists j. later_than i j /\ authenticated_send_pred j received_serialized_msg))
      )
    | _ -> False)
  )
  (ensures fun t0 _ t1 -> (t0 == t1 /\ authenticated_send_pred i received_serialized_msg))

(**
  This lemma combines the guarantees provided by the authenticated+confidential channels with the
  authenticated_confidential_send_pred.
*)
val authn_conf_send_pred_lemma: (i:nat) -> (p:principal) -> (received_serialized_msg:bytes) -> LAPI.LCrypto unit (LPKI.pki (Communication.Layer.send_preds sr_preds))
  (requires fun t0 ->
    (match parse_msg_raw received_serialized_msg with
    | Success (MsgWithCounter principal_list counter nonce) ->
      (List.Tot.mem p principal_list) /\
      (
        (A.corrupt_id i (P p) /\ is_publishable  gu i nonce) \/
        (exists j. later_than i j /\ authenticated_confidential_send_pred j received_serialized_msg)
      )
    | _ -> False)
  )
  (ensures fun t0 _ t1 -> (t0 == t1 /\ authenticated_confidential_send_pred i received_serialized_msg))
