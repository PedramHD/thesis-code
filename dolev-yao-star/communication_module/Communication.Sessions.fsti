/// Communication.Sessions
/// ======================
///
/// This layer adds one session type to the state, storing information on connections (used for
///  request/response functions).

module Communication.Sessions

open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib

noeq type session_st =
  | CommunicationState: request_send_idx:nat -> sym_key:bytes -> responder:principal -> session_st
  | APP: st:bytes -> session_st

val serialize_session_st: session_st -> bytes

val parse_session_st: (serialized_session_st:bytes) -> result session_st

// open TLS13.Messages
// open TLS13.Sessions

// let tls13_preds : send_layer_preds = {
//   //higher_layer_gu = tls13_global_usage;
//   layer_preds = tls13;
//   epred = epred;
//   session_st_inv = session_st_inv;
//   session_st_inv_later = (fun i j p si vi st -> valid_session_later p);
//   confidential_send_pred = (fun i m -> True);
//   confidential_send_pred_later = (fun i j m -> ());
//   authenticated_send_pred = (fun i m -> True);
//   authenticated_confidential_send_pred = (fun i m -> True);
//   request_pred = (fun i m -> True);
//   response_pred = (fun i m -> True);
// }
