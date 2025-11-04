/// Communication.Preds
/// ===================
module Communication.Preds

open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib
open Communication.UsagePredicates
open Communication.Sessions

module LC = LabeledCryptoAPI
module LR = LabeledRuntimeAPI

(**
  Global usage defined on the send layer: The usage preds of the upper layer are enriched (see
  [send_layer_usage_preds]), the send predicates are mapped to the predicates on cryptographic
  functions. The key usages are not modified by this layer.
*)
let send_preds_global_usage (extended_gu:extended_global_usage) = {
    LC.usage_preds = send_layer_usage_preds extended_gu;
    LC.key_usages = extended_gu.higher_layer_gu.LC.key_usages;
}


noeq type send_layer_preds = {
  extended_higher_layer_gu:extended_global_usage;
  epred:timestamp -> principal -> event -> Type0;
  session_st_inv: trace_idx:timestamp -> principal -> session:nat -> version:nat -> bytes -> Type0;
  session_st_inv_later: i:timestamp -> j:timestamp -> p:principal -> si:nat -> vi:nat -> st:bytes ->
                   Lemma ((session_st_inv i p si vi st /\ later_than j i) ==>
                           session_st_inv j p si vi st);
} 

// let send_layer_preds = p:send_layer_preds_{TLS13.Handshake.Messages.key_usage_preds p.extended_higher_layer_gu.higher_layer_gu.key_usages /\
// 					   TLS13.Handshake.Messages.usage_pred_cond_ (send_preds_global_usage p.extended_higher_layer_gu).usage_preds}

(**
  A CommunicationState state session is valid if the symmetric key is an aead key labeled with the
  sender and the responder.
*)
let valid_session (pr:send_layer_preds) (i:nat) (p:principal) (si:nat) (vi:nat) (st:session_st) : Type0 =
  match st with
  | CommunicationState request_send_idx sym_key responder -> (
    was_rand_generated_before i sym_key (join (readers [P p]) (readers [P responder])) (aead_usage "AEAD.Symmetric_Send_Key")
  )
  | APP app_st -> pr.session_st_inv i p si vi app_st


val valid_session_later: (pr:send_layer_preds) -> (p:principal) ->
    Lemma (forall i j si vi st. (valid_session pr i p si vi st /\ later_than j i) ==>
			    valid_session pr j p si vi st)



let session_st_inv (pr:send_layer_preds) (gu:LC.global_usage) i p si vi st =
  LC.is_msg (send_preds_global_usage pr.extended_higher_layer_gu) i st (readers [V p si vi]) /\
  (match parse_session_st st with
   | Success s -> valid_session pr i p si vi s
   | _ -> False)


let send_preds (pr:send_layer_preds) : LR.preds = {
  LR.global_usage = send_preds_global_usage pr.extended_higher_layer_gu;
  LR.trace_preds = {
    LR.can_trigger_event = pr.epred;
    LR.session_st_inv = session_st_inv pr (send_preds_global_usage pr.extended_higher_layer_gu);
    LR.session_st_inv_later = (fun i j p si vi st -> valid_session_later pr p);
    LR.session_st_inv_lemma = (fun i p si vi st -> ())
  }
}
