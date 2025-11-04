/// Communication.Preds
/// ===================
module Communication.Preds

let valid_session_later pr p =
  let valid_session_later_params (pr:send_layer_preds) (p:principal) (i:timestamp) (j:timestamp) (si:nat) (vi:nat) (st:session_st) :
      Lemma ( (valid_session pr i p si vi st /\ later_than j i) ==>
			    valid_session pr j p si vi st)
      [SMTPat (valid_session pr i p si vi st); SMTPat (later_than j i) ]
      =
      match st with
      | CommunicationState _ _ _ -> ()
      | APP app_st -> pr.session_st_inv_later i j p si vi app_st in
      ()
