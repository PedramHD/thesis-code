/// TLS13.App.Sessions
/// ====================
module TLS13.App.Sessions

open SecrecyLabels
open RelaxLabels
open GlobalRuntimeLib
open CryptoLib
open LabeledPKI
open TLS13.Handshake.Messages
open TLS13.Handshake.Sessions
open TLS13.App.Messages
module A = LabeledCryptoAPI
module R = LabeledRuntimeAPI

let is_app_aead_conf_key pred i k a b = 
    (exists si si' vi'. 
       let l' = (join (readers [V a si 0]) (readers [V b si' vi'])) in 
       let l = (join (meet l' public) (unsession l')) in      
       A.is_aead_key (tls13_app_global_usage pred) i k l "TLS13.aead_key_conf")

let is_app_aead_rr_key pred i k a b = 
    (exists si si' vi'. 
       let l' = (join (readers [V a si 0]) (readers [V b si' vi'])) in 
       let l = (join (meet l' public) (unsession l')) in      
       A.is_aead_key (tls13_app_global_usage pred) i k l "TLS13.aead_key_req_resp")

(* Session States *)
noeq type session_st =
  | InitiatorState: b:principal -> ak:bytes -> akrr:bytes -> session_st
  | InitiatorStSymKey: b:principal -> ak:bytes -> akrr:bytes -> sym_key:bytes -> session_st
  | ResponderState: a:principal -> ak:bytes -> akrr:bytes -> session_st
  
val parse_session_st: bytes -> result session_st

let valid_session (pred:tls13_layer_preds) (i:nat) (p:principal) (si:nat) (vi:nat) (st:session_st) : Type0 =
  match st with
  | InitiatorState b akc akrr -> b <> p /\
				(A.corrupt_id i (P b) \/ (is_app_aead_conf_key pred i akc p b /\ is_app_aead_rr_key pred i akrr p b)) /\
				is_msg pred i akc (readers [P p]) /\ is_msg pred i akrr (readers [P p]) /\
				is_msg pred i akc (readers [P b]) /\ is_msg pred i akrr (readers [P b]) /\
				A.can_flow i (readers [P p]) (A.get_label (tls13_app_key_usages pred) akc) /\
				A.can_flow i (readers [P p]) (A.get_label (tls13_app_key_usages pred) akrr) 
  | InitiatorStSymKey b akc akrr sym_key -> b <> p /\ 
				 (A.corrupt_id i (P b) \/ (is_app_aead_conf_key pred i akc p b /\ is_app_aead_rr_key pred i akrr p b)) /\
				is_msg pred i akc (readers [P p]) /\ is_msg pred i akrr (readers [P p]) /\
				is_msg pred i akc (readers [P b]) /\ is_msg pred i akrr (readers [P b]) /\
				A.can_flow i (readers [P p]) (A.get_label (tls13_app_key_usages pred) akc) /\
				A.can_flow i (readers [P p]) (A.get_label (tls13_app_key_usages pred) akrr) /\
				 (was_rand_generated_before i sym_key (join (readers [P b]) (readers [P p])) (aead_usage "AEAD.Symmetric_Send_Key"))
  | ResponderState a akc akrr -> a <> p /\ (A.corrupt_id i (P a) \/ (is_app_aead_conf_key pred i akc p a /\ is_app_aead_rr_key pred i akrr p a)) /\
				is_msg pred i akc (readers [P p]) /\ is_msg pred i akrr (readers [P p]) /\
				is_msg pred i akc (readers [P a]) /\ is_msg pred i akrr (readers [P a]) /\
				A.can_flow i (readers [P p]) (A.get_label (tls13_app_key_usages pred) akc) /\
				A.can_flow i (readers [P p]) (A.get_label (tls13_app_key_usages pred) akrr) 
				
				
let valid_session_later (pred:tls13_layer_preds) (p:principal) :
    Lemma (forall i j si vi st. (valid_session pred i p si vi st /\ later_than j i) ==>
			    valid_session pred j p si vi st) = ()

val serialize_valid_session_st (pred:tls13_layer_preds) (i:nat) (p:principal) (si:nat) (vi:nat)
			       (st:session_st{valid_session pred i p si vi st}) :
			       msg pred i (readers [V p si vi])

val parse_valid_serialize_session_st_lemma : pred:tls13_layer_preds -> i:nat -> p:principal -> si:nat -> vi:nat -> ss:session_st ->
    Lemma (requires (valid_session pred i p si vi ss))
	  (ensures (Success ss == parse_session_st (serialize_valid_session_st pred i p si vi ss)))
	  [SMTPat (parse_session_st (serialize_valid_session_st pred i p si vi ss))]

let epred (pred:tls13_layer_preds) i s e =
    match e with
    | ("Request",[c;si;s;m]) -> True
    | ("Response",[s;si;c;m]) -> True
    | _ -> False
    
let session_st_inv (pred:tls13_layer_preds) i p si vi st =
    A.is_msg (tls13_app_global_usage pred) i st (readers [V p si vi]) /\
    (match parse_session_st st with
     | Success s -> valid_session pred i p si vi s
     | _ -> False)

let tls13_app (pred:tls13_layer_preds) : tls_preds = {
  R.global_usage = tls13_app_global_usage pred;
  R.trace_preds = {
    R.can_trigger_event = epred pred;
    R.session_st_inv = session_st_inv pred;
    R.session_st_inv_later = (fun i j p si vi st -> valid_session_later pred p);
    R.session_st_inv_lemma = (fun i p si vi st -> ());
  }
}


