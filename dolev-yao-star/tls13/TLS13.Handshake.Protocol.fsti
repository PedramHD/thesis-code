/// TLS13.Handshake.Protocol
/// ==========================
module TLS13.Handshake.Protocol

open SecrecyLabels
open RelaxLabels
open CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI
open TLS13.Handshake.Messages
open TLS13.Handshake.Sessions

module A = LabeledCryptoAPI
(* Protocol API *)

val initiator_send_msg_1:
  pred:tls_preds ->
  a:principal ->
  b:principal ->
  LCrypto (idx_msg:nat * idx_session:nat) (tls pred)
  (requires (fun _ -> True))
  (ensures (fun t0 (i,si) t1 ->
	    trace_len t1 > trace_len t0 /\
	    i == trace_len t1 - 1))

val responder_send_msg_2:
  pred:tls_preds ->
  b:principal ->
  idx_msg:nat ->
  LCrypto (idx_msg':nat * idx_session:nat) (tls pred)
  (requires (fun _ -> True))
  (ensures (fun t0 (i,si) t1 ->
	   trace_len t1 > trace_len t0 /\
	    i == trace_len t1 - 1 ))

val initiator_send_msg_3:
  pred:tls_preds ->
  a:principal ->
  idx_session:nat ->
  idx_msg:nat ->
  LCrypto (idx_msg':nat) (tls pred)
  (requires (fun _ -> True))
  (ensures (fun t0 i t1 ->
    trace_len t1 > trace_len t0 /\
    i == trace_len t1 - 1))

val responder_accept_msg_3:
  pred:tls_preds ->
  b:principal ->
  idx_session:nat ->
  idx_msg:nat ->
  LCrypto unit (tls pred)
  (requires (fun _ -> True))
  (ensures (fun _ _ _ -> True))

let new_session_number (#pred:tls_preds) (p:principal) :
    LCrypto nat (tls pred) (requires fun t0 -> True)
			 (ensures fun t0 r t1 -> t1 == t0) =
    LabeledPKI.new_session_number #(tls13 pred) p

val new_session: #pred:tls_preds -> #i:timestamp -> p:principal -> si:nat -> vi:nat -> st:bytes ->
    LCrypto unit (tls pred)
		 (requires fun t0 -> trace_len t0 == i /\ A.is_msg (tls13_gu pred) i st (readers [V p si vi]) /\ 
				  pred.trace_preds.session_st_inv i p si vi st)
		 (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)

val update_session: #pred:tls_preds -> #i:timestamp -> p:principal -> si:nat -> vi:nat -> st:bytes ->
    LCrypto unit (tls pred)
		 (requires fun t0 -> trace_len t0 == i /\ A.is_msg (tls13_gu pred) i st (readers [V p si vi]) /\ 
				  pred.trace_preds.session_st_inv i p si vi st)
		 (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)

val get_session: #pred:tls_preds -> #i:timestamp -> p:principal -> si:nat ->
    LCrypto (vi:nat & msg pred i (readers [V p si vi])) (tls pred)
	    (requires fun t0 -> trace_len t0 == i)
	    (ensures fun t0 (|vi,st|) t1 -> t1 == t0 /\ A.is_msg (tls13_gu pred) i st (readers [V p si vi]) /\
					 pred.trace_preds.session_st_inv i p si vi st)

val find_session: #pred:tls_preds -> #i:timestamp -> p:principal -> f:(si:nat -> vi:nat -> st:bytes -> bool) ->
    LCrypto (option (si:nat & vi:nat & msg pred i (readers [V p si vi]))) (tls pred)
	    (requires fun t0 -> trace_len t0 == i)
	    (ensures fun t0 r t1 -> t1 == t0 /\
		     (match r with | None -> True
		     | Some (|si,vi,st|) -> f si vi st /\ A.is_msg (tls13_gu pred) i st (readers [V p si vi]) /\ 
							pred.trace_preds.session_st_inv i p si vi st))
