/// TLS13.Handshake.Messages
/// ==========================
module TLS13.Handshake.Messages

open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib
open RelaxLabels

module A = LabeledCryptoAPI
module R = LabeledRuntimeAPI

(* Events *)

let initiate (a:principal) (b:principal) (gx:bytes) : event = ("Initiate",[(string_to_bytes a);(string_to_bytes b);gx])
let respond (b:principal) (gx:bytes) (gy:bytes) (y:bytes): event = ("Respond",[(string_to_bytes b);gx;gy;y])
let finishI (a:principal) (b:principal) (gx:bytes) (gy:bytes) (k:bytes) (ak:bytes): event = ("FinishI",[(string_to_bytes a);(string_to_bytes b);gx;gy;k;ak])
let finishR (b:principal) (gx:bytes) (gy:bytes) (k:bytes): event = ("FinishR",[(string_to_bytes b);gx;gy;k])

(* Formats of Signed Values *)
noeq type sigval =
  | SigMsg2: a:principal -> gx:bytes -> gy:bytes -> sigval
  | SigMsg3: b:principal -> gx:bytes -> gy:bytes -> sigval

val parse_sigval: bytes -> result sigval

(* Formats of MACed Values *)
noeq type macval =
  | MacMsg2: b:principal -> macval
  | MacMsg3: b:principal -> macval

val parse_macval: bytes -> result macval

let sig_key_label = "TLS13.sig_key"
let mac_key_label = "TLS13.mac_key"
let aead_key_c_label = "TLS13.aead_key_conf"
let aead_key_rr_label = "TLS13.aead_key_req_resp"
let dh_key_label = "TLS13.dh_key"
let kdf_key_label = "TLS13.kdf_key"

let zz =
    let zb = Seq.create 32 0uy in
    bytestring_to_bytes zb

let on =
    let zb = Seq.create 32 0uy in
    let ob' = zb.[31] <- 1uy in
    bytestring_to_bytes ob'

let tw =
    let zb = Seq.create 32 0uy in
    let tb' = zb.[30] <- 1uy in
    bytestring_to_bytes tb'

let info_disjoint_lemma () :
  Lemma (on <> zz /\ zz <> tw /\ on <> tw) =
  let zzb = Seq.create 32 0uy in
  let onb = zzb.[31] <- 1uy in
  let twb = zzb.[30] <- 1uy in 
  assert(Seq.index zzb 31 == 0uy);
  assert(Seq.index zzb 30 == 0uy);
  assert(Seq.index onb 31 == 1uy);
  assert(Seq.index onb 30 == 0uy);
  assert(Seq.index twb 31 == 0uy);
  assert(Seq.index twb 30 == 1uy);
  assert(~(Seq.equal zzb onb));
  bytestring_to_bytes_lemma zzb;
  bytestring_to_bytes_lemma onb;
  bytestring_to_bytes_lemma twb

(* Global Key Usages *)
let dh_usage_pred (pred:R.preds) = 
    (forall s1 s2 ss. (s1 == dh_key_label \/ s2 == dh_key_label) ==> (pred.global_usage.key_usages.dh_shared_secret_usage s1 s2 ss == None)) /\
    (forall ss. pred.global_usage.key_usages.dh_unknown_peer_usage dh_key_label ss == None)
    
let kdf_usage_pred (pred:R.preds) = 
    (forall s k info. s == kdf_key_label ==> pred.global_usage.key_usages.kdf_expand_usage s k info == None) /\
    (forall k info. pred.global_usage.key_usages.kdf_extract_usage kdf_key_label k info == None) /\
    (forall k slt kl sl. pred.global_usage.key_usages.kdf_extend_label kdf_key_label k slt kl sl == None)

let usage_pred_cond (pred:R.preds) = 
  (forall i s k m. s == sig_key_label ==> pred.global_usage.usage_preds.can_sign i s k m == False) /\
  (forall i s k m. s == mac_key_label ==> pred.global_usage.usage_preds.can_mac i s k m == False)

let kdf_extend_label_flows_to_meet (pred:R.preds) = 
    (forall i s k slt kl sl. (match (pred.global_usage.key_usages.kdf_extend_label s k slt kl sl) with | None -> True | Some kdfl -> A.can_flow i kdfl (meet kl sl)))

let key_usages_are_unique (pred:R.preds) = 
  (forall m. A.get_usage pred.global_usage.key_usages m <> Some (dh_usage dh_key_label) /\
	A.get_usage pred.global_usage.key_usages m <> Some (kdf_usage kdf_key_label) /\
	A.get_usage pred.global_usage.key_usages m <> Some (sig_usage sig_key_label) /\
	A.get_usage pred.global_usage.key_usages m <> Some (mac_usage mac_key_label) 
	// /\
	// A.get_usage pred.global_usage.key_usages m <> Some (aead_usage aead_key_c_label) /\
	// A.get_usage pred.global_usage.key_usages m <> Some (aead_usage aead_key_rr_label)
  )

type tls_preds = p:R.preds{dh_usage_pred p /\ kdf_usage_pred p /\ usage_pred_cond p /\ kdf_extend_label_flows_to_meet p /\ key_usages_are_unique p}

(* Global Key Usages Conditions *)
let dh_usage_pred_ (ku:A.key_usages) = 
    (forall s1 s2 ss. (s1 == dh_key_label \/ s2 == dh_key_label) ==> (ku.dh_shared_secret_usage s1 s2 ss == None)) /\
    (forall ss. ku.dh_unknown_peer_usage dh_key_label ss == None)
    
let kdf_usage_pred_ (ku:A.key_usages) = 
    (forall s k info. s == kdf_key_label ==> ku.kdf_expand_usage s k info == None) /\
    (forall k info. ku.kdf_extract_usage kdf_key_label k info == None) /\
    (forall k slt kl sl. ku.kdf_extend_label kdf_key_label k slt kl sl == None)

let usage_pred_cond_ (up:A.usage_preds) = 
  (forall i s k m. s == sig_key_label ==> up.can_sign i s k m == False) /\
  (forall i s k m. s == mac_key_label ==> up.can_mac i s k m == False)

let kdf_extend_label_flows_to_meet_ (ku:A.key_usages) = 
    (forall i s k slt kl sl. (match (ku.kdf_extend_label s k slt kl sl) with | None -> True | Some kdfl -> A.can_flow i kdfl (meet kl sl)))

let key_usages_are_unique_ (ku:A.key_usages) = 
  (forall m. A.get_usage ku m <> Some (dh_usage dh_key_label) /\
	A.get_usage ku m <> Some (kdf_usage kdf_key_label) /\
	A.get_usage ku m <> Some (sig_usage sig_key_label) /\
	A.get_usage ku m <> Some (mac_usage mac_key_label) 
  )

let key_usage_preds (ku:A.key_usages) = dh_usage_pred_ ku /\ kdf_usage_pred_ ku /\ kdf_extend_label_flows_to_meet_ ku /\ key_usages_are_unique_ ku

let dh_shared_secret_usage (pred:tls_preds) s1 s2 ss =
  if s1 = dh_key_label then Some (kdf_usage kdf_key_label)
  else if s2 = dh_key_label then Some (kdf_usage kdf_key_label)
  else pred.global_usage.key_usages.dh_shared_secret_usage s1 s2 ss

let dh_usage_commutes_lemma (pred:tls_preds) : Lemma (forall s1 s2 ss. dh_shared_secret_usage pred s1 s2 ss == dh_shared_secret_usage pred s2 s1 ss) =
  pred.global_usage.key_usages.dh_usage_commutes_lemma ()

let dh_unknown_peer_usage (pred:tls_preds) s ss = 
  if s = dh_key_label then Some (kdf_usage kdf_key_label) 
  else pred.global_usage.key_usages.dh_unknown_peer_usage s ss

let dh_unknown_peer_usage_lemma (pred:tls_preds) : 
    Lemma (forall s1 ss u. dh_unknown_peer_usage pred s1 ss == Some u ==> (forall s2. dh_shared_secret_usage pred s1 s2 ss == Some u)) =
  pred.global_usage.key_usages.dh_unknown_peer_usage_lemma ()

let kdf_expand_usage (pred:tls_preds) s k info = 
  if (s = kdf_key_label && info = zz) then Some (mac_usage mac_key_label) 
  else if (s = kdf_key_label && info = on) then Some (aead_usage aead_key_c_label) 
  else if (s = kdf_key_label && info = tw) then Some (aead_usage aead_key_rr_label) 
  else if s = kdf_key_label then None
  else pred.global_usage.key_usages.kdf_expand_usage s k info

let kdf_extract_usage (pred:tls_preds) s k info = 
  if (s = kdf_key_label) then Some (kdf_usage kdf_key_label) 
  else pred.global_usage.key_usages.kdf_extract_usage s k info

let kdf_extend_label (pred:tls_preds) s k slt kl sl = 
  if (s = kdf_key_label) then Some (unsession kl)
  else pred.global_usage.key_usages.kdf_extend_label s k slt (A.get_label (pred.global_usage.key_usages) k) (A.get_label (pred.global_usage.key_usages) slt)

let tls13_key_usages (pred:tls_preds) : A.key_usages = {
  A.dh_shared_secret_usage = dh_shared_secret_usage pred;
  A.dh_unknown_peer_usage = dh_unknown_peer_usage pred;
  A.dh_usage_commutes_lemma = (fun () -> dh_usage_commutes_lemma pred);
  A.dh_unknown_peer_usage_lemma = (fun () -> dh_unknown_peer_usage_lemma pred);
  A.kdf_extend_label = kdf_extend_label pred;
  A.kdf_extract_usage = kdf_extract_usage pred;
  A.kdf_expand_usage = kdf_expand_usage pred;
}

let ppred (pred:tls_preds) i s pk m = pred.global_usage.usage_preds.can_pke_encrypt i s pk m
let apred (pred:tls_preds) i s k m ad = pred.global_usage.usage_preds.can_aead_encrypt i s k m ad
let spred (pred:tls_preds) i s k m =
    if s = sig_key_label then
    (exists p. A.get_signkey_label (tls13_key_usages pred) k == readers [P p] /\
	(match parse_sigval m with
	 | Success (SigMsg2 a gx gy) ->
	   (exists y. gy == (dh_pk y) /\ (A.can_flow i (readers [P p]) (A.get_dhkey_label (tls13_key_usages pred) gy))  /\ 
		  did_event_occur_before i p (respond p gx gy y))
	 | Success (SigMsg3 b gx gy) ->
	   (exists x k ak. gx == (dh_pk x) /\ (A.can_flow i (readers [P p]) (A.get_dhkey_label (tls13_key_usages pred) gx))  /\ 
		  did_event_occur_before i p (finishI p b gx gy k ak))
	 | _ -> False))
    else pred.global_usage.usage_preds.can_sign i s k m
let mpred (pred:tls_preds) i s k m = 
    if s = mac_key_label then
	(match parse_macval m with
	 | Success (MacMsg2 b) -> True
	 | Success (MacMsg3 b) -> True	 
	 | _ -> False)
    else pred.global_usage.usage_preds.can_mac i s k m

let tls13_usage_preds pred : A.usage_preds = {
  A.can_pke_encrypt = ppred pred;
  A.can_aead_encrypt =  apred pred;
  A.can_sign = spred pred;
  A.can_mac = mpred pred
}

let tls13_global_usage pred : A.global_usage = {
  A.key_usages = tls13_key_usages pred;
  A.usage_preds = tls13_usage_preds pred;
}

let tls13_gu pred = tls13_global_usage pred

(*** Messages and Serialization *)

let msg pred i l = A.msg (tls13_global_usage pred) i l
let is_msg pred i b l = A.is_msg (tls13_global_usage pred) i b l 

val sigval_msg2 (#pred:tls_preds) (#i:nat) (a:principal) (gx:msg pred i public) (gy:msg pred i public) :
		r:msg pred i public{parse_sigval r == Success (SigMsg2 a gx gy)}

val sigval_msg3 (#pred:tls_preds) (#i:nat) (b:principal) (gx:msg pred i public) (gy:msg pred i public) :
		r:msg pred i public{parse_sigval r == Success (SigMsg3 b gx gy)}

val macval_msg2 (#pred:tls_preds) (i:nat) (b:principal) :
		r:msg pred i public{parse_macval r == Success (MacMsg2 b)}

val macval_msg3 (#pred:tls_preds) (i:nat) (b:principal) :
		r:msg pred i public{parse_macval r == Success (MacMsg3 b)}

noeq type tls13_msg (pred:tls_preds) (i:nat) =
  |Msg1: gx:msg pred i public -> tls13_msg pred i
  |Msg2: b:principal -> gy:msg pred i public -> sg:msg pred i public -> m:msg pred i public -> tls13_msg pred i 
  |Msg3: gx:msg pred i public -> sg:msg pred i public -> m:msg pred i public -> tls13_msg pred i 

val serialize_msg: #pred:tls_preds -> #i:nat -> tls13_msg pred i -> msg pred i public
val parse_msg: #pred:tls_preds -> #i:nat -> msg pred i public -> result (tls13_msg pred i)

open LabeledCryptoAPI

val is_valid_term_in_layer: pr:tls_preds -> m:bytes -> Type0

val get_usage_pred : pr:tls_preds -> m:bytes ->
    Lemma (requires (is_valid_term_in_layer pr m))
	  (ensures (get_usage (tls13_key_usages pr) m == get_usage pr.global_usage.key_usages m))
	  [SMTPat (is_valid_term_in_layer pr m)]

val get_label_pred : pr:tls_preds -> m:bytes ->
    Lemma (requires (is_valid_term_in_layer pr m)) 
	  (ensures ((get_label (tls13_key_usages pr) m) == (get_label pr.global_usage.key_usages m)))
	  [SMTPat (is_valid_term_in_layer pr m)]

val is_valid_in_layer: pr:tls_preds -> i:nat -> m:bytes -> 
    Lemma (requires (is_valid pr.global_usage i m))
	  (ensures (is_valid_term_in_layer pr m))
	  [SMTPat (is_valid pr.global_usage i m)]
	  
val is_valid_pred_lemma: pr:tls_preds -> i:nat -> m:bytes -> 
    Lemma (requires (is_valid pr.global_usage i m))
	  (ensures (is_valid (tls13_global_usage pr) i m)) 
	  [SMTPat (is_valid pr.global_usage i m)]

val is_valid_pred_inv_lemma: pr:tls_preds -> i:nat -> m:bytes -> 
    Lemma (requires (is_valid (tls13_global_usage pr) i m))
	  (ensures (is_valid pr.global_usage i m)) 
	  [SMTPat (is_valid (tls13_global_usage pr) i m)]
