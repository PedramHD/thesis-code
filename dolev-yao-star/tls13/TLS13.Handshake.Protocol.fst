/// TLS13.Handshake.Protocol (implementation)
/// ==========================================
module TLS13.Handshake.Protocol

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0" 

module A = LabeledCryptoAPI

let initiator_send_msg_1 pred a b = 
  print_string ("initiator "^a^" sending first message to "^b^"\n");
  let si = new_session_number #(tls13 pred) a in
  let (|t0,x|) = rand_gen #(tls13 pred) (readers [V a si 0]) (dh_usage "TLS13.dh_key") in
  let gx = dh_pk #(tls13_gu pred) #t0 #(readers [V a si 0]) x in
  let ev = initiate a b gx in
  trigger_event #(tls13 pred) a ev;
  let t1 = global_timestamp () in
  let new_ss_st = InitiatorSentMsg1 b x in
  let new_ss = serialize_valid_session_st pred t1 a si 0 new_ss_st in
  new_session #(tls13 pred) #t1 a si 0 new_ss;
  let t2 = global_timestamp () in
  let msg1 = Msg1 gx in
  let w_msg1 = serialize_msg #pred #t2 msg1 in
  let i = send #(tls13 pred) #t2 a b w_msg1 in
  i,si

val receive_msg_1_helper: pred:tls_preds -> b:principal -> idx_msg:nat -> LCrypto (now:nat & a:principal &
 gx:msg pred now public) (tls pred)
			  (requires (fun _ -> True))
			  (ensures (fun t0 (|now,_, _|) t1 -> t0 == t1 /\ now == trace_len t0))

let receive_msg_1_helper pred b idx_msg =
  print_string ("responder "^b^" processing first message to \n");
  let (|now,a,w_msg1|) = receive_i #(tls13 pred) idx_msg b in
  let msg1 = parse_msg w_msg1 in
  match msg1 with
   | Success (Msg1 gx) -> (|now,a,gx|)
   | _ -> error "responder_send_msg_2: not a msg1"

val send_msg_2_helper: #pred:tls_preds -> #idx:nat -> b:principal -> a:principal -> gx:msg pred idx public -> LCrypto (nat*nat) (tls pred)
			  (requires (fun t0 -> later_than (trace_len t0) idx))
			  (ensures (fun t0 (i,si) t1 -> trace_len t1 > trace_len t0 /\ i == trace_len t1 - 1))
let send_msg_2_helper #pred #idx b a gx =
  print_string ("responder "^b^" sending second message to "^a^"\n");
  let t0 = global_timestamp () in
  let si = new_session_number #(tls13 pred) b in
  let (|_, skb|) = get_private_key #(tls13 pred) #t0 b SIG sig_key_label in
  let kl = (readers [V b si 0]) in
  let (|t1, y|) = rand_gen #(tls13 pred) kl (dh_usage "TLS13.dh_key") in
  let y: lbytes (tls13_gu pred) t0 kl = y in
  let gy = dh_pk #(tls13_gu pred) #(t1+1) #kl y in
  let new_ss_st = (ResponderSentMsg2 a gx gy y) in
  let new_ss = serialize_valid_session_st pred (t1+1) b si 0 new_ss_st in
  assert (is_eph_priv_key pred (t1+1) y b si 0); assert (exists si vi. is_eph_priv_key pred (t1+1) y b si vi);
  assert (is_publishable (tls13_gu pred) (t1+1) gx /\ is_publishable (tls13_gu pred) (t1+1) gy /\ 
						  (exists si vi. is_eph_priv_key pred (t1+1) y b si vi) /\ gy == CryptoLib.dh_pk y );
  trigger_event #(tls13 pred) b (respond b gx gy y);
  let t2 = global_timestamp () in
  assert (t2 == t1+2);
  assert (did_event_occur_at (t1+1) b (respond b gx gy y)); 
  new_session #(tls13 pred) #t2 b si 0 new_ss;
  let t3 = global_timestamp () in
  assert (t3 == t2+1);
  let sv: msg pred t3 public = sigval_msg2 #pred #t3 a gx gy in 
  let vkb = vk #(tls13_gu pred) #t3 #(readers [P b]) skb in
  let (|t4,n_sig|) = rand_gen #(tls13 pred) (readers [P b]) (nonce_usage "SIG_NONCE") in
  
  assert(get_signkey_label (tls13_key_usages pred) (CryptoLib.vk skb) == (readers [P b]));
  assert(is_dh_public_key (tls13_gu pred) t4 gy kl "TLS13.dh_key");
  dh_key_label_lemma (tls13_gu pred) t4 gy;
  assert(get_dhkey_label (tls13_key_usages pred) gy == kl);
  can_flow_principal t4 b;
  assert(can_flow t4 (readers [P b]) kl);
  assert(gy == dh_pk #(tls13_gu pred) #t4 #kl y /\ (did_event_occur_before t4 b (respond b gx gy y)));
  assert (spred pred t4 sig_key_label (CryptoLib.vk skb) sv);
  let sg = sign #(tls13_gu pred) #t4 #(readers [P b]) #public skb n_sig sv in
  let k = dh #(tls13_gu pred) #t4 #(readers [V b si 0]) y gx in 
  assert (is_kdf_un_key pred t4 k b si 0 gx);
  let zb = Seq.create 32 0uy in
  let zz = bytestring_to_bytes #(tls13_gu pred) #t4 zb in 
  let mk = expand #(tls13_gu pred) #t4 #_ #public k zz in 
  let m = mac #(tls13_gu pred) #t4 #_ #public mk (macval_msg2 t4 b) in
  let gy:msg pred t4 public = gy in
  let msg2 = Msg2 b gy sg m in
  let w_msg2 = serialize_msg #pred #t4 msg2 in
  let i = send #(tls13 pred) #t4 b a w_msg2 in
  i,si

let responder_send_msg_2 pred b idx_msg =
  let (|now,a,gx|) = receive_msg_1_helper pred b idx_msg in
  send_msg_2_helper #pred #now b a gx

let dh_shared_secret_lemma__ (x:bytes) (y:bytes) : Lemma ((CryptoLib.dh x (CryptoLib.dh_pk y)) == (CryptoLib.dh y (CryptoLib.dh_pk x))) 
    [SMTPat (CryptoLib.dh x (CryptoLib.dh_pk y)); SMTPat (CryptoLib.dh y (CryptoLib.dh_pk x))] 
= CryptoLib.dh_shared_secret_lemma x y 

val receive_msg_2_helper: 
  pred:tls_preds ->
  i:nat -> si:nat -> vi:nat -> 
  a:principal ->
  b:principal ->
  pkb:public_key (tls13 pred) i b SIG "TLS13.sig_key" ->
  x:eph_priv_key pred i a si 0 ->
  gx:eph_pub_key pred i a si 0{gx == dh_pk #(tls13_gu pred) #i #(readers [V a si 0]) x} ->
  gy:msg pred i public ->
  sg:msg pred i public ->
  LCrypto (bytes * bytes * bytes) (tls pred)
  (requires (fun t0 -> i == trace_len t0))
  (ensures (fun t0 (mk, ak, akrr) t1 -> trace_len t0 == trace_len t1 /\
			       is_aead_un_key pred i ak a si vi gy /\ is_mac_un_key pred i mk a si vi gy /\ is_aead_un_rr_key pred i akrr a si vi gy /\
			       (A.verify #(tls13_gu pred) #i #(readers [P b]) #public pkb (sigval_msg2 a gx gy) sg) /\
				  (A.can_flow i (readers [P b]) public \/ 
				    // A.can_flow i (readers [P b]) (A.get_dhkey_label (tls13_key_usages pred) gy)
				    (is_aead_conf_key pred i ak a b /\ is_aead_rr_key pred i akrr a b)))) 

let receive_msg_2_helper pred i si vi a b pkb x gx gy sg =
   let sv = sigval_msg2 a gx gy in
   if A.verify #(tls13_gu pred) #i #(readers [P b]) #public pkb sv sg then (
     can_flow_to_public_implies_corruption i (P b);
     verification_key_label_lemma (tls13_gu pred) i pkb (readers [P b]);
     let k = dh #(tls13_gu pred) #i #(readers [V a si 0]) x gy in 
     assert (is_kdf_un_key pred i k a si 0 gy);
     let salt: lbytes (tls13_gu pred) i public = empty in 
     let l' = (join (readers [V a si 0]) (get_dhkey_label (tls13_key_usages pred) gy)) in 
     let k = extract k salt in 
     let l = (join (meet l' public) (unsession l')) in      
     assert ( is_publishable (tls13_gu pred) i k \/ is_kdf_key (tls13_gu pred) i k l "TLS13.kdf_key"); 
     let zb = Seq.create 32 0uy in
     let zz = bytestring_to_bytes #(tls13_gu pred) #i zb in 
     let mk = expand #(tls13_gu pred) #i #l #public k zz in 
     let ob = zb.[31] <- 1uy in
     let on = bytestring_to_bytes #(tls13_gu pred) #i ob in 
     let ak = expand #(tls13_gu pred) #i #l #public k on in 
     let tb = zb.[30] <- 1uy in
     let tw = bytestring_to_bytes #(tls13_gu pred) #i tb in 
     let akrr = expand #(tls13_gu pred) #i #l #public k tw in 
     info_disjoint_lemma (); 
     readers_is_injective b;
     assert (is_aead_un_key pred i ak a si vi gy);
     assert (forall y si vi. gy == (CryptoLib.dh_pk y) /\ is_eph_priv_key pred i y b si vi ==> is_eph_pub_key pred i gy b si vi); 
     assert (forall y idx si vi. is_eph_priv_key pred idx y b si vi /\ later_than i idx ==> is_eph_priv_key pred i y b si vi);
     assert (spred pred i "TLS13.sig_key" pkb sv ==> (exists y idx si vi. gy == (CryptoLib.dh_pk y) /\ is_eph_priv_key pred idx y b si vi /\ 
					     later_than i idx /\ did_event_occur_before i b (respond b gx gy y)));
     assert (spred pred i "TLS13.sig_key" pkb sv ==> (exists y si vi. gy == (CryptoLib.dh_pk y) /\ is_eph_pub_key pred i gy b si vi /\ did_event_occur_before i b (respond b gx gy y))); 
     dh_key_label_lemma (tls13_gu pred) i gy; 
     can_flow_join_public_lemma i;
     (mk, ak, akrr))
   else error "sig verification failed"
 
let initiator_send_msg_3 pred a idx_session idx_msg =
  print_string ("initiator "^a^" processing second message and sending third message\n");
  let t0 = global_timestamp () in
  let (|vi,st|) = get_session #(tls13 pred) #t0 a idx_session in
  if vi=0 then (
    match parse_session_st st with
    | Success (InitiatorSentMsg1 b x) ->
      let (|si, ska|) = get_private_key #(tls13 pred) #t0 a SIG "TLS13.sig_key" in
      let pkb = get_public_key #(tls13 pred) #t0 a b SIG "TLS13.sig_key" in
      let (|t1,_,w_msg2|) = receive_i #(tls13 pred) idx_msg a in
      assert (later_than t1 t0);
      (match parse_msg w_msg2 with
      | Success (Msg2 b'' gy sg m) ->
        if b = b'' then (
          let gx = dh_pk #(tls13_gu pred) #t1 #(readers [V a idx_session vi]) x in
          let pkb : public_key (tls13 pred) t1 b SIG "TLS13.sig_key" = pkb in
          let (mk, ak, akrr) = receive_msg_2_helper pred t1 idx_session vi a b pkb x gx gy sg in
          ///////////////////////*****/////////////////////
          assert(A.verify #(tls13_gu pred) #t1 #(readers [P b]) #public pkb (sigval_msg2 a gx gy) sg);
          assert (is_mac_un_key pred t1 mk a idx_session vi gy);
          assert( is_aead_un_key pred t1 ak a idx_session vi gy);
          let mv = macval_msg2 t1 b in 
          let l' =  join (readers [V a idx_session 0]) (get_dhkey_label (tls13_key_usages pred) gy) in 
          let l = join (meet l' public) (unsession l') in 
          unsession_of_si_vi a idx_session 0;        
          can_flow_unsession_to_label l';
          can_flow_join_unsession t1 (readers [V a idx_session 0]) (get_dhkey_label (tls13_key_usages pred) gy);        
          can_flow_from_join t1 (readers [V a idx_session 0]) (get_dhkey_label (tls13_key_usages pred) gy);
          assert (can_flow t1 l' (readers [V a idx_session 0]));
          can_flow_from_join t1 (meet l' public) (unsession l');
          can_flow_transitive t1 l (unsession l') (readers [P a]);   
          assert(can_flow t1 (get_label (tls13_key_usages pred) ak) (readers [P a]));
          assert(can_flow t1 (get_label (tls13_key_usages pred) mk) (readers [P a]));
          can_flow_principal t1 a;
          assert(can_flow t1 (readers [P a]) (readers [V a idx_session (vi+1)]));
          can_flow_transitive t1 (get_label (tls13_key_usages pred) ak) (readers [P a]) (readers [V a idx_session (vi+1)]);
          can_flow_transitive t1 (get_label (tls13_key_usages pred) akrr) (readers [P a]) (readers [V a idx_session (vi+1)]);
          assert(can_flow t1 (get_label (tls13_key_usages pred) ak) (readers [V a idx_session (vi+1)]));
          assert(can_flow t1 (get_label (tls13_key_usages pred) mk) (readers [V a idx_session (vi+1)]));
          ///////////////////////*****/////////////////////
          assert( is_publishable (tls13_gu pred) t1 mk \/ is_mac_key (tls13_gu pred) t1 mk l "TLS13.mac_key");
          if verify_mac #(tls13_gu pred) #t1 #l #public mk mv m then (
            let new_ss_st = (InitiatorSentMsg3 b gy mk ak akrr) in
            assert(can_flow t1 (get_label (tls13_key_usages pred) ak) (readers [P a]));
            assert(can_flow t1 (get_label (tls13_key_usages pred) ak) (readers [V a idx_session (vi+1)]));
            assert(valid_session pred t1 a idx_session (vi+1) new_ss_st);
            let new_ss = serialize_valid_session_st pred t1 a idx_session (vi+1) new_ss_st in
            assert (is_eph_pub_key pred t1 gx a idx_session vi); assert (later_than (t1+1) t1);
            trigger_event #(tls13 pred) a (finishI a b gx gy mk ak);
            let t2 = global_timestamp () in
            update_session #(tls13 pred) #t2 a idx_session (vi+1) new_ss;
            let t3 = global_timestamp () in
            let m : msg pred t3 public = mac #(tls13_gu pred) #t3 #l #public mk (macval_msg3 t3 b) in
	    let (|t4,n_sig|) = rand_gen #(tls13 pred) (readers [P a]) (nonce_usage "SIG_NONCE") in
            assert (is_signing_key (tls13_gu pred) t0 ska (readers [P a]) sig_key_label);
	    vk_lemma #(tls13_gu pred) #t4 #(readers [P a]) ska;
	    assert (get_signkey_label (tls13_key_usages pred) (CryptoLib.vk ska) == (readers [P a]));
	    assert (is_dh_public_key (tls13_gu pred) t4 gx (get_label (tls13_key_usages pred) x) "TLS13.dh_key");
	    dh_key_label_lemma (tls13_gu pred) t4 gx;
	    can_flow_principal t4 a;
	    assert(gx == dh_pk #(tls13_gu pred) #t4 #(get_label (tls13_key_usages pred) x) x /\ (did_event_occur_before t4 a (finishI a b gx gy mk ak)));
	    let sv: msg pred t4 public = sigval_msg3 b gx gy in
	    assert (spred pred t4 sig_key_label (CryptoLib.vk ska) sv);
	    let sg = sign #(tls13_gu pred) #t4 #(readers [P a]) #public ska n_sig sv in

            let msg3 = Msg3 gx sg m in
            let w_msg3 : msg pred t3 public = serialize_msg #pred #t3 msg3 in
            let i = send #(tls13 pred) a b w_msg3 in
            i)
          else error "initiator_send_msg_3: incorrect mac")
        else error "initiator_send_msg_3: incorrect sender"
      | _ -> error "initiator_send_msg_3: not a msg2")
  | _ -> error  "initiator_send_msg_3: wrong session states"
  )
  else error "initiator_send_msg_3: wrong version in state"

val receive_msg_3_helper: 
  pred:tls_preds ->
  i:nat -> si:nat -> vi:nat -> 
  a:principal ->
  b:principal ->
  pka:public_key (tls13 pred) i a SIG "TLS13.sig_key" ->
  y:eph_priv_key pred i b si 0 ->
  gy:eph_pub_key pred i b si 0{gy == dh_pk #(tls13_gu pred) #i #(readers [V b si 0]) y} ->
  gx:msg pred i public ->
  sg:msg pred i public ->
  LCrypto (bytes * bytes * bytes) (tls pred)
  (requires (fun t0 -> i == trace_len t0))
  (ensures (fun t0 (mk, ak, akrr) t1 -> trace_len t0 == trace_len t1 /\
			       is_aead_un_key pred i ak b si vi gx /\ is_mac_un_key pred i mk b si vi gx /\ is_aead_un_rr_key pred i akrr b si vi gx /\
			       (A.verify #(tls13_gu pred) #i #(readers [P a]) #public pka (sigval_msg3 b gx gy) sg) /\
				  (A.corrupt_id i (P a) \/ 
				    // A.can_flow i (readers [P a]) (A.get_dhkey_label (tls13_key_usages pred) gx)
				    (is_aead_conf_key pred i ak b a /\ is_aead_rr_key pred i akrr b a))
	     
             )) 

let receive_msg_3_helper pred i si vi a b pka y gy gx sg =
   let sv = sigval_msg3 b gx gy in
   if A.verify #(tls13_gu pred) #i #(readers [P a]) #public pka sv sg then (
     can_flow_to_public_implies_corruption i (P a);
     verification_key_label_lemma (tls13_gu pred) i pka (readers [P a]);
     let k = dh #(tls13_gu pred) #i #(readers [V b si 0]) y gx in 
     assert (is_kdf_un_key pred i k b si 0 gx);
     let salt: lbytes (tls13_gu pred) i public = empty in 
     let l' = (join (readers [V b si 0]) (get_dhkey_label (tls13_key_usages pred) gx)) in 
     let k = extract k salt in 
     let l = (join (meet l' public) (unsession l')) in      
     assert ( is_publishable (tls13_gu pred) i k \/ is_kdf_key (tls13_gu pred) i k l "TLS13.kdf_key"); 
     let zb = Seq.create 32 0uy in
     let zz = bytestring_to_bytes #(tls13_gu pred) #i zb in 
     let mk = expand #(tls13_gu pred) #i #l #public k zz in 
     let ob = zb.[31] <- 1uy in
     let on = bytestring_to_bytes #(tls13_gu pred) #i ob in 
     let ak = expand #(tls13_gu pred) #i #l #public k on in 
     let tb = zb.[30] <- 1uy in
     let tw = bytestring_to_bytes #(tls13_gu pred) #i tb in 
     let akrr = expand #(tls13_gu pred) #i #l #public k tw in 
     info_disjoint_lemma (); 
     readers_is_injective a;
     assert (is_aead_un_key pred i ak b si vi gx);
     assert (forall x si vi. gx == (CryptoLib.dh_pk x) /\ is_eph_priv_key pred i x a si vi ==> is_eph_pub_key pred i gx a si vi); 
     assert (forall x idx si vi. is_eph_priv_key pred idx x a si vi /\ later_than i idx ==> is_eph_priv_key pred i x a si vi);
     assert (spred pred i "TLS13.sig_key" pka sv ==> 
		   (exists x. gx == (CryptoLib.dh_pk x) /\ (A.can_flow i (readers [P a]) (A.get_dhkey_label (tls13_key_usages pred) gx)) /\
			 (exists b k ak. did_event_occur_before i a (finishI a b gx gy k ak)))); 
     assert (spred pred i "TLS13.sig_key" pka sv ==> (exists x idx si vi. gx == (CryptoLib.dh_pk x) /\ is_eph_priv_key pred idx x a si vi /\ 
					     later_than i idx /\ (exists b k ak. did_event_occur_before i a (finishI a b gx gy k ak))));
     assert (spred pred i "TLS13.sig_key" pka sv ==> 
		   (exists x si vi. gx == (CryptoLib.dh_pk x) /\ is_eph_pub_key pred i gx a si vi /\ (exists b k ak. did_event_occur_before i a (finishI a b gx gy k ak))));
     dh_key_label_lemma (tls13_gu pred) i gx;  
     can_flow_join_public_lemma i;
     (mk, ak, akrr))
   else error "sig verification failed"

let responder_accept_msg_3 pred b idx_session idx_msg =
  print_string ("responder "^b^" processing third message\n");
  let t0 = global_timestamp () in
  let (|vi,st|) = get_session #(tls13 pred) #t0 b idx_session in
  if vi=0 then (
  match parse_session_st st with
  | Success (ResponderSentMsg2 a gx gy y) ->
    let (|t1,a',w_msg3|) = receive_i #(tls13 pred) idx_msg b in
    assert (t1 == t0); 
    if a = a' then // the stored principal and the current principal are the same. they may not be the actual principal
    (match parse_msg w_msg3 with
       | Success (Msg3 gx sg m) ->
	  let pka = get_public_key #(tls13 pred) #t0 b a SIG "TLS13.sig_key" in
          let pka : public_key (tls13 pred) t1 a SIG "TLS13.sig_key" = pka in
          let (mk, ak, akrr) = receive_msg_3_helper pred t1 idx_session vi a b pka y gy gx sg in
          ///////////////////////*****/////////////////////
          assert(A.verify #(tls13_gu pred) #t1 #(readers [P a]) #public pka (sigval_msg3 b gx gy) sg);
	  assert (is_mac_un_key pred t1 mk b idx_session vi gx);
	  assert (is_aead_un_key pred t1 ak b idx_session vi gx);
	  dh_key_label_lemma (tls13_gu pred) t1 gx;
	  let mv = macval_msg3 t1 b in 
	  let l' =  join (readers [V b idx_session 0]) (get_dhkey_label (tls13_key_usages pred) gx) in 
          let l = join (meet l' public) (unsession l') in 
          unsession_of_si_vi b idx_session 0;        
          can_flow_unsession_to_label l';
          can_flow_join_unsession t1 (readers [V b idx_session 0]) (get_dhkey_label (tls13_key_usages pred) gx);        
          can_flow_from_join t1 (readers [V b idx_session 0]) (get_dhkey_label (tls13_key_usages pred) gx);
          assert (can_flow t1 l' (readers [V b idx_session 0]));
          can_flow_from_join t1 (meet l' public) (unsession l');
          can_flow_transitive t1 l (unsession l') (readers [P b]);  
	  assert(can_flow t1 (get_label (tls13_key_usages pred) ak) (readers [P b]));
	  assert(can_flow t1 (get_label (tls13_key_usages pred) mk) (readers [P b]));
	  can_flow_principal t1 b;
	  assert(can_flow t1 (readers [P b]) (readers [V b idx_session (vi+1)]));
	  can_flow_transitive t1 (get_label (tls13_key_usages pred) ak) (readers [P b]) (readers [V b idx_session (vi+1)]);
	  can_flow_transitive t1 (get_label (tls13_key_usages pred) akrr) (readers [P b]) (readers [V b idx_session (vi+1)]);
	  assert(can_flow t1 (get_label (tls13_key_usages pred) ak) (readers [V b idx_session (vi+1)]));
	  assert(can_flow t1 (get_label (tls13_key_usages pred) mk) (readers [V b idx_session (vi+1)]));
	  if verify_mac #(tls13_gu pred) #t1 #(get_label (tls13_key_usages pred) mk) mk mv m then (
  	     let new_ss_st = (ResponderReceivedMsg3 a gx gy ak akrr) in
	     assert(can_flow t1 (get_label (tls13_key_usages pred) ak) (readers [P b]));
	     assert(can_flow t1 (get_label (tls13_key_usages pred) ak) (readers [V b idx_session (vi+1)]));
	     assert (A.is_publishable (tls13_gu pred) t1 gx /\ A.is_publishable (tls13_gu pred) t1 gy /\
				      (is_aead_un_key pred t1 ak b idx_session (vi+1) gx) /\ (is_aead_un_rr_key pred t1 akrr b idx_session (vi+1) gx) /\
				      A.can_flow t1 (A.get_label (tls13_key_usages pred) ak) (readers [V b idx_session (vi+1)]) /\
				      A.can_flow t1 (A.get_label (tls13_key_usages pred) akrr) (readers [V b idx_session (vi+1)]) /\
				      (A.corrupt_id t1 (P a) \/ (is_aead_conf_key pred t1 ak b a /\ is_aead_rr_key pred t1 akrr b a)));
	     assert(valid_session pred t1 b idx_session (vi+1) new_ss_st);
	     let new_ss = serialize_valid_session_st pred t1 b idx_session (vi+1) new_ss_st in
	     let ev = finishR b gx gy ak in
	     trigger_event #(tls13 pred) b ev;
	     let t2 = global_timestamp () in
	     update_session #(tls13 pred) #t2 b idx_session (vi+1) new_ss;
	     ())
	  else error "responder_accept_msg_3: invalid mac"
       | _ -> error "responder_accept_msg_3: not a msg2")
    else error  "responder_accept_msg_3: incorrect principal"
  | _ -> error  "responder_accept_msg_3: wrong session states"
  )
  else error "responder_accept_msg_3: wrong version in state"

open TLS13.Handshake.Sessions
friend TLS13.Handshake.Sessions
let new_session #pr #i p si vi ss =
  assert (pr.trace_preds.session_st_inv i p si vi ss /\ A.is_msg (tls13_gu pr) i ss (readers [V p si vi]));
  let st = concat #(tls13_gu pr) #i #(readers [V p si vi]) (string_to_bytes #(tls13_gu pr) #i "TLSApp") ss in
  assert (parse_session_st st == Success (TLSApp ss));
  assert ((tls13 pr).trace_preds.session_st_inv i p si vi st);
  new_session #(tls13 pr) #i p si vi st

let update_session #pr #i p si vi ss =
  assert (pr.trace_preds.session_st_inv i p si vi ss /\ A.is_msg (tls13_gu pr) i ss (readers [V p si vi]));
  let st = concat #(tls13_gu pr) #i #(readers [V p si vi]) (string_to_bytes #(tls13_gu pr) #i "TLSApp") ss in
  assert (parse_session_st st == Success (TLSApp ss));
  assert ((tls13 pr).trace_preds.session_st_inv i p si vi st);  
  update_session #(tls13 pr) #i p si vi st

let get_session #pr #i p si =
  let (|vi,s|) = get_session #(tls13 pr) #i p si in
  match parse_session_st s with
  | Success (TLSApp s') ->
    assert (valid_session pr i p si vi (TLSApp s'));
    (tls13 pr).trace_preds.session_st_inv_lemma i p si vi s'; 
    (|vi,s'|)
  | _ -> error "get_session: not an application state"

let find_session #pr #i p f =
  let f' si vi st =
    match parse_session_st st with
    | Success (TLSApp s) -> f si vi s
    | _ -> false in
  match find_session #(tls13 pr) #i p f' with
  | None -> None
  | Some (|si,vi,st|) -> (
    (match parse_session_st st with
     | Success (TLSApp s') ->
       assert (valid_session pr i p si vi (TLSApp s'));
       (tls13 pr).trace_preds.session_st_inv_lemma i p si vi s';
       Some (|si,vi,s'|)
     | _ -> error "find_session: not an application state")
)
