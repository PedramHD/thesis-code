/// NSL.SecurityProperties (implementation)
/// ========================================
module NSL.SecurityProperties

open NSL.Protocol
friend LabeledPKI
open LabeledRuntimeAPI
open NSL.Sessions

let is_n_b_in_b_state a b idx_setstate v_b state_b idx_sess n_b =
  state_was_set_at idx_setstate b v_b state_b /\
  idx_sess < Seq.length state_b /\
  (match LabeledPKI.parse_session_st (state_b.[idx_sess]) with
  | Success (APP s) -> (
    match NSL.Sessions.parse_session_st s with
    | Success (ResponderReceivedMsg3 a' n_b') -> n_b==n_b' /\ a = a'
    | _ -> False
  )
  | _ -> False
  )


let n_b_is_secret a b idx_setstate v_b state_b idx_sess n_b =
  let t0= get () in
  assert(valid_trace (pki nsl) t0);
  assert(idx_setstate < trace_len t0);
  assert(is_n_b_in_b_state a b idx_setstate v_b state_b idx_sess n_b);
  assert(state_inv (pki nsl) idx_setstate b v_b state_b);
  assert(is_labeled (pki nsl).global_usage (idx_setstate) n_b (readers ([P a; P b])));
  assert(later_than (trace_len t0) idx_setstate);
  assert(is_labeled (pki nsl).global_usage (trace_len t0) n_b (readers ([P a; P b])));
  secrecy_lemma #(pki nsl) n_b


let is_n_b_in_a_state a b idx_setstate v_a state_a idx_sess n_b =
  state_was_set_at idx_setstate a v_a state_a /\
  idx_sess < Seq.length state_a /\
  (match LabeledPKI.parse_session_st (state_a.[idx_sess]) with
  | Success (APP s) -> (
    match NSL.Sessions.parse_session_st s with
    |Success (InitiatorSentMsg3 b' n_a n_b') -> n_b==n_b' /\ b=b'
    | _ -> False
  )
  | _ -> False
  )


let n_b_in_a_state_is_secret a b idx_setstate v_b state_a idx_sess n_b =
  let t0= get () in
  assert(later_than (trace_len t0) idx_setstate);
  secrecy_lemma #(pki nsl) n_b

let initiator_authentication i = ()

let responder_authentication i = ()
