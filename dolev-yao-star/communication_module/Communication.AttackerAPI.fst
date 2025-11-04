/// Communication.AttackerAPI (Implementation)
/// ==========================================
///

module Communication.AttackerAPI

let initiator_send_request_attacker_function #i #higher_level_preds sender receiver message =
  let (|t0, sym_key|) = LabeledPKI.rand_gen #(send_preds higher_level_preds) public (aead_usage "AEAD.Symmetric_Send_Key") in
  assert(later_than t0 i);
  let sym_key:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) t0 public = sym_key in
  let final_message = concat sym_key message in

  let (|now, confidential_message|) = create_conf_message_for_request_pke #t0 #higher_level_preds sender receiver final_message in
  let send_idx = LabeledPKI.send #(send_preds higher_level_preds) #now sender receiver confidential_message in

  // instead of storing (send_idx, sym_key), we directly return the values
  (|send_idx, sym_key|)

