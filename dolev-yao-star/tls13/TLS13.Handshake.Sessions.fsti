/// TLS13.Handshake.Sessions
/// =========================
module TLS13.Handshake.Sessions

open SecrecyLabels
open RelaxLabels
open GlobalRuntimeLib
open CryptoLib
open TLS13.Handshake.Messages
open LabeledPKI
module A = LabeledCryptoAPI
module R = LabeledRuntimeAPI

(* Instantiated Protocol Usages and Keys *)
let is_eph_priv_key pred i k p si vi = A.is_dh_private_key (tls13_gu pred) i k (readers [V p si vi]) "TLS13.dh_key"
let is_eph_pub_key pred i k p si vi = A.is_dh_public_key (tls13_gu pred) i k (readers [V p si vi]) "TLS13.dh_key"
let is_kdf_un_key pred i k p si vi gy = 
    A.is_kdf_key (tls13_gu pred) i k (join (readers [V p si vi]) (A.get_dhkey_label (tls13_key_usages pred) gy)) "TLS13.kdf_key"
let is_aead_un_key pred i k p si _ gy = 
    let l' = (join (readers [V p si 0]) (A.get_dhkey_label (tls13_key_usages pred) gy)) in 
    let l = (join (meet l' public) (unsession l')) in      
    A.is_aead_key (tls13_gu pred) i k l "TLS13.aead_key_conf"
let is_aead_conf_key pred i k a b = 
    (exists si si' vi'. 
       let l' = (join (readers [V a si 0]) (readers [V b si' vi'])) in 
       let l = (join (meet l' public) (unsession l')) in      
       A.is_aead_key (tls13_gu pred) i k l "TLS13.aead_key_conf")

let is_aead_un_rr_key pred i k p si _ gy = 
    let l' = (join (readers [V p si 0]) (A.get_dhkey_label (tls13_key_usages pred) gy)) in 
    let l = (join (meet l' public) (unsession l')) in      
    A.is_aead_key (tls13_gu pred) i k l "TLS13.aead_key_req_resp"
let is_aead_rr_key pred i k a b = 
    (exists si si' vi'. 
       let l' = (join (readers [V a si 0]) (readers [V b si' vi'])) in 
       let l = (join (meet l' public) (unsession l')) in      
       A.is_aead_key (tls13_gu pred) i k l "TLS13.aead_key_req_resp")
    
let is_mac_un_key pred i k p si _ gy = 
    let l' = (join (readers [V p si 0]) (A.get_dhkey_label (tls13_key_usages pred) gy)) in 
    let l = (join (meet l' public) (unsession l')) in      
    A.is_mac_key (tls13_gu pred) i k l "TLS13.mac_key"

let eph_pub_key pred i p si vi = A.dh_public_key (tls13_gu pred) i (readers [V p si vi]) "TLS13.dh_key"
let eph_priv_key pred i p si vi = A.dh_private_key (tls13_gu pred) i (readers [V p si vi]) "TLS13.dh_key"

(* Session States *)

noeq type session_st =
  | InitiatorSentMsg1: b:principal -> x:bytes -> session_st
  | ResponderSentMsg2: a:principal -> gx:bytes -> gy:bytes -> k:bytes -> session_st
  | InitiatorSentMsg3: b:principal -> gy:bytes -> mk:bytes -> akc:bytes -> akrr:bytes -> session_st
  | ResponderReceivedMsg3: a:principal -> gx:bytes -> gy:bytes -> k:bytes -> krr:bytes -> session_st
  | TLSApp: s:bytes -> session_st
  
val parse_session_st: bytes -> result session_st

let valid_session (pred:tls_preds) (i:nat) (p:principal) (si:nat) (vi:nat) (st:session_st) : Type0 =
  match st with
  | InitiatorSentMsg1 b x -> is_eph_priv_key pred i x p si vi
  | ResponderSentMsg2 a gx gy y -> A.is_publishable (tls13_gu pred) i gx /\
				  A.is_publishable (tls13_gu pred) i gy /\
				  is_msg pred i y (readers [V p si vi]) /\
				  is_eph_priv_key pred i y p si vi /\
				  gy == dh_pk y
  | InitiatorSentMsg3 b gy mk akc akrr -> A.is_publishable (tls13_gu pred) i gy /\
				  (is_aead_un_key pred i akc p si vi gy) /\ (is_aead_un_rr_key pred i akrr p si vi gy) /\ (is_mac_un_key pred i mk p si vi gy) /\
				  is_msg pred i akc (readers [V p si vi]) /\
				  is_msg pred i akrr (readers [V p si vi]) /\
				  is_msg pred i mk (readers [V p si vi]) /\
				  (A.corrupt_id i (P b) \/ (is_aead_conf_key pred i akc p b /\ is_aead_rr_key pred i akrr p b))
  | ResponderReceivedMsg3 a gx gy akc akrr -> A.is_publishable (tls13_gu pred) i gx /\ A.is_publishable (tls13_gu pred) i gy /\
				      (is_aead_un_key pred i akc p si vi gx) /\ (is_aead_un_rr_key pred i akrr p si vi gx) /\
				      is_msg pred i akc (readers [V p si vi]) /\
				      is_msg pred i akrr (readers [V p si vi]) /\
				      (A.corrupt_id i (P a) \/ (is_aead_conf_key pred i akc p a /\ is_aead_rr_key pred i akrr p a))
  | TLSApp s -> (pred.trace_preds.session_st_inv i p si vi s) /\ A.is_msg (tls13_gu pred) i s (readers [V p si vi]) 

let valid_session_later (pred:tls_preds) (p:principal) :
    Lemma (forall i j si vi st. (valid_session pred i p si vi st /\ later_than j i) ==>
			    valid_session pred j p si vi st) = ()

val serialize_valid_session_st (pred:tls_preds) (i:nat) (p:principal) (si:nat) (vi:nat)
			       (st:session_st{valid_session pred i p si vi st}) :
			       A.msg (tls13_gu pred) i (readers [V p si vi])

val parse_valid_serialize_session_st_lemma : pred:tls_preds -> i:nat -> p:principal -> si:nat -> vi:nat -> ss:session_st ->
    Lemma (requires (valid_session pred i p si vi ss))
	  (ensures (Success ss == parse_session_st (serialize_valid_session_st pred i p si vi ss)))
	  [SMTPat (parse_session_st (serialize_valid_session_st pred i p si vi ss))]

let epred pred i s e =
    match e with
    | ("Initiate",[ta;tb;gx]) -> True
    | ("Respond",[tb;gx;gy;y]) ->
      (match bytes_to_string tb with
       | Success (b) -> A.is_publishable (tls13_gu pred) i gx /\ A.is_publishable (tls13_gu pred) i gy /\ 
		       (exists si vi. is_eph_priv_key pred i y b si vi) /\ gy == dh_pk y 
       | _ -> False )
    | ("FinishI",[ta;tb;gx;gy;k;ak]) ->
      (match bytes_to_string tb, bytes_to_string ta with
       | Success (b), Success (a) -> 
	 A.is_publishable (tls13_gu pred) i gx /\ A.is_publishable (tls13_gu pred) i gy /\ 
	 (exists x si vi. gx == dh_pk x /\ is_eph_priv_key pred i x a si vi /\ is_aead_un_key pred i ak s si vi gy)
       | _, _ -> False )
    | ("FinishR",[tb;gx;gy;k]) ->
      (match bytes_to_string tb with
	| Success (b) -> (exists si. is_aead_un_key pred i k b si 0 gx)
       |  _ -> False )
    | _ -> False
    
let session_st_inv pred i p si vi st =
    A.is_msg (tls13_gu pred) i st (readers [V p si vi]) /\
    (match parse_session_st st with
     | Success s -> valid_session pred i p si vi s
     | _ -> False)

let tls13 (pred:tls_preds) : R.preds = {
  R.global_usage = (tls13_gu pred);
  R.trace_preds = {
    R.can_trigger_event = epred pred;
    R.session_st_inv = session_st_inv pred;
    R.session_st_inv_later = (fun i j p si vi st -> valid_session_later pred p);
    R.session_st_inv_lemma = (fun i p si vi st -> ());
  }
}

let tls pred = (pki (tls13 pred))

open LabeledRuntimeAPI

val get_responder_session_tls: pred:tls_preds -> i:nat -> initiator:principal -> responder:principal ->
    LCrypto (option (nat * nat * session_st)) (tls pred)
		(requires (fun t0 -> i == trace_len t0))
		(ensures (fun t0 r t1 -> t0 == t1 /\ 
				      (match r with | Some (sid, vi, st) -> valid_session pred i initiator sid vi st /\
						      (match st with | InitiatorSentMsg3 b gy mk ak akrr -> b = responder
								     | InitiatorSentMsg1 b x -> b = responder
								     | _ -> False)
						    | None -> True)))

val get_initiator_session_tls: pred:tls_preds -> i:nat -> initiator:principal -> responder:principal ->
    LCrypto (option (nat * nat * session_st)) (tls pred)
		(requires (fun t0 -> i == trace_len t0))
		(ensures (fun t0 r t1 -> t0 == t1 /\ 
				      (match r with | Some (sid, vi, st) -> valid_session pred i responder sid vi st /\
						      (match st with | ResponderReceivedMsg3 b _ _ _ _
								     | ResponderSentMsg2 b _ _ _ -> b = initiator
								     | _ -> False)
						    | None -> True)))

let get_session_st_tls = parse_session_st

