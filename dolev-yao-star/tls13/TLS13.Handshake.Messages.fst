/// TLS13.Handshake.Messages (implementation)
/// ==========================================
module TLS13.Handshake.Messages

module A = LabeledCryptoAPI

let parse_sigval t : result sigval =
  let? (ttag,agxgy) = split t in
  let? (a,gxgy) = split agxgy in 
  match bytes_to_string a with 
  | Success a -> (let? (gx,gy) = split gxgy in
    match? bytes_to_string ttag with
    | "msg2" -> Success (SigMsg2 a gx gy)
    | "msg3" -> Success (SigMsg3 a gx gy)
    | _ -> Error "incorrect tag")
  | _ -> Error "incorrect principal"

let parse_macval t : result macval =
  let? (ttag,p) = split t in
  let? ttag = bytes_to_string ttag in 
  let? p = bytes_to_string p in
  match ttag, p with
  | "msg2", b -> Success (MacMsg2 b)
  | "msg3", b -> Success (MacMsg3 b)  
  | _ -> Error "incorrect tag"

let sigval_msg2 (#pred:tls_preds) (#i:nat) (a:principal) (gx:msg pred i public) (gy:msg pred i public) : msg pred i public =
    A.concat #(tls13_gu pred) #i #public (A.string_to_bytes #(tls13_gu pred) #i "msg2") 
      (A.concat #(tls13_gu pred) #i #public (A.string_to_bytes #(tls13_gu pred) #i a) 
	(A.concat #_ #i #public gx gy))

let sigval_msg3 (#pred:tls_preds) (#i:nat) (a:principal) (gx:msg pred i public) (gy:msg pred i public) : msg pred i public =
    A.concat #(tls13_gu pred) #i #public (A.string_to_bytes #(tls13_gu pred) #i "msg3") 
    (A.concat #(tls13_gu pred) #i #public (A.string_to_bytes #(tls13_gu pred) #i a) 
      (A.concat #_ #i #public gx gy))

let macval_msg2 (#pred:tls_preds) (i:nat) (b:principal) : msg pred i public =
    A.concat #(tls13_gu pred) #i #public (A.string_to_bytes #(tls13_gu pred) #i "msg2") (A.string_to_bytes #(tls13_gu pred) #i b)

let macval_msg3 (#pred:tls_preds) (i:nat) (b:principal) : msg pred i public =
    A.concat #(tls13_gu pred) #i #public (A.string_to_bytes #(tls13_gu pred) #i "msg3") (A.string_to_bytes #(tls13_gu pred) #i b)

let serialize_msg (#pred:tls_preds) (#i:nat) (m:tls13_msg pred i) : msg pred i public =
  match m with
  | Msg1 gx -> A.concat #_ #i #public (A.string_to_bytes #(tls13_gu pred) #i "msg1") gx
  | Msg2 b gy sg m -> A.concat #_  #i #public (A.string_to_bytes #(tls13_gu pred) #i "msg2") (A.concat #_  #i #public (A.string_to_bytes #(tls13_gu pred) #i b) (A.concat #_  #i #public gy (A.concat sg m)))
  | Msg3 gx sg m -> A.concat #_ #i #public (A.string_to_bytes #(tls13_gu pred) #i "msg3") 
		   (A.concat #_  #i #public gx (A.concat sg m))

let parse_msg (#pred:tls_preds) (#i:nat) (w:msg pred i public) : 
    (r:result (tls13_msg pred i){match r with 
 			   | Success (Msg2 b gy sg m) -> 
			     (match A.split #(tls13_gu pred) #i w with
			     | Success (ttag, rest) ->
			       (A.bytes_to_string #(tls13_gu pred) #i ttag == Success "msg2") /\
			       (match A.split #(tls13_gu pred) #i rest with 
			       | Success (tb, gysgm) -> (Success b) == (A.bytes_to_string #(tls13_gu pred) #i tb) /\
    				 (match A.split #(tls13_gu pred) #i gysgm with 
    				 | Success (gy', sgm) -> (match A.split #(tls13_gu pred) #i sgm with 
    							| Success (sg', m') -> (gy == gy' /\ sg == sg' /\ m == m')
							| _ -> False)
				 | _ -> False)
			       | _ -> False)
			     | _ -> False)
			   | _ -> True}) = 
  let? (ttag,rest) = A.split #(tls13_gu pred) #i w in
  match? A.bytes_to_string #(tls13_gu pred) #i ttag with
  | "msg1" -> Success (Msg1 rest)
  | "msg2" -> (match A.split #(tls13_gu pred) #i rest with 
	     | Success (tb, gysgm) -> 
	       (match (A.bytes_to_string #(tls13_gu pred) #i tb) with
	       | Success b ->	       
    	       (match A.split #(tls13_gu pred) #i gysgm with 
    	       | Success (gy, sgm) -> (match A.split #(tls13_gu pred) #i sgm with 
    				      | Success (sg, m) -> Success (Msg2 b gy sg m) // (gy == gy' /\ sg == sg' /\ m == m')
				      | _ -> Error ("incorrect sg m"))
	       | _ -> Error ("incorrect gy sg m"))
	       | _ -> Error ("incorrect principal"))
	     | _ -> Error ("incorrect rest"))   
	     // let? (tb,gysgm) = A.split #(tls13_gu pred) #i rest in 
	     // let? b = A.bytes_to_string #(tls13_gu pred) #i tb in 
	     // let? (gy,sgm) = A.split #(tls13_gu pred) #i gysgm in 
	     // let? (sg,m) = A.split #(tls13_gu pred) #i sgm in 
	     // Success (Msg2 b gy sg m)
  | "msg3" -> let? (gx,sgm) = A.split #(tls13_gu pred) #i rest in let? (sg,m) = A.split #(tls13_gu pred) #i sgm in Success (Msg3 gx sg m)
  | _ -> Error "unknown message tag"

#push-options "--z3rlimit 100"
let parse_serialize_msg_lemma (#pred:tls_preds) #i m : Lemma (parse_msg #pred #i (serialize_msg #pred #i m) == Success m) = 
  match m with
  | Msg1 gx -> ()
  | Msg2 b gy sg m -> 
    let sm = (A.concat #(tls13_gu pred) #i #public (A.string_to_bytes #(tls13_gu pred) #i "msg2") 
			    (A.concat #(tls13_gu pred) #i #public (A.string_to_bytes #(tls13_gu pred) #i b) 
			    (A.concat #(tls13_gu pred) #i #public gy (A.concat sg m)))) in
    assert (serialize_msg (Msg2 b gy sg m) == sm);
    (match A.split #(tls13_gu pred) #i sm with
    | Success (ttag, rest) ->
      assert (A.bytes_to_string #(tls13_gu pred) #i ttag == Success "msg2");    
      (match A.split #(tls13_gu pred) #i rest with 
      | Success (tb, gysgm) -> assert (A.bytes_to_string #(tls13_gu pred) #i tb == Success b);
	(match A.split #(tls13_gu pred) #i gysgm with 
	| Success (gy', sgm) -> assert (gy' == gy);
	  (match A.split #(tls13_gu pred) #i sgm with 
	  | Success (sg', m') -> assert (sg' == sg /\ m' == m))
	)
      );
    let pm = (match A.split #(tls13_gu pred) #i sm with
    | Success (ttag, rest) ->
      assert (A.bytes_to_string #(tls13_gu pred) #i ttag == Success "msg2");    
      (match A.split #(tls13_gu pred) #i rest with 
      | Success (tb, gysgm) -> 
    	let (Success b) = (A.bytes_to_string #(tls13_gu pred) #i tb) in 
    	(match A.split #(tls13_gu pred) #i gysgm with 
    	| Success (gy', sgm) -> 
    	  (match A.split #(tls13_gu pred) #i sgm with 
    	  | Success (sg', m') -> Success (Msg2 b gy' sg' m'))
    	)
      )) in 
      assert (parse_msg sm  == pm); 
      assert (parse_msg sm  == Success (Msg2 b gy sg m))
    | _ -> assert (False))
  | Msg3 gx sg m -> 
    let sm = (A.concat #(tls13_gu pred) #i #public (A.string_to_bytes #(tls13_gu pred) #i "msg3") 
			    (A.concat #(tls13_gu pred) #i #public gx (A.concat sg m))) in
    (match A.split #(tls13_gu pred) #i sm with
    | Success (ttag, rest) ->
      assert (A.bytes_to_string #(tls13_gu pred) #i ttag == Success "msg3");    
      (match A.split #(tls13_gu pred) #i rest with 
	| Success (gx', sgm) -> assert (gx' == gx);
	  (match A.split #(tls13_gu pred) #i sgm with 
	  | Success (sg', m') -> assert (sg' == sg /\ m' == m)));
      assert (parse_msg sm  == Success (Msg3 gx sg m))
    | _ -> assert (False))
#pop-options

#restart-solver
#push-options "--z3rlimit 15 --max_fuel 2 --max_ifuel 2"

open LabeledCryptoAPI
friend LabeledCryptoAPI

let rec is_valid_term_in_layer (pr:tls_preds) (m:bytes) =
  match m with 
  | Literal _ -> True
  | Rand n l u -> (match u with 
		 | (DHKey s) -> if s = dh_key_label then False else True
		 | (KDF s) -> if s = kdf_key_label then False else True
		 | (MAC s) -> if s = mac_key_label then False else True
		 | (CryptoLib.SIG s) -> if s = sig_key_label then False else True
		 // | (AE s) -> if s <> aead_key_c_label && s <> aead_key_rr_label then True else False
		 | _ -> True)
  | Concat b1 b2 -> is_valid_term_in_layer pr b1 /\ is_valid_term_in_layer pr b2
  | PK s | VK s | DH_PK s -> is_valid_term_in_layer pr s
  | PKEnc pk n msg -> is_valid_term_in_layer pr pk /\ is_valid_term_in_layer pr msg /\ is_valid_term_in_layer pr n
  | Extract key salt -> 
    (match get_usage (tls13_key_usages pr) key with 
      // If the term has usage KDF kdf_key_label in tls layer, it is invalid in higher layer (tls13_key_usages pr)
    | Some (KDF s) -> if s = kdf_key_label then False else True
    | _ -> True) /\ is_valid_term_in_layer pr key /\ is_valid_term_in_layer pr salt
  | Expand key info -> is_valid_term_in_layer pr key /\ is_valid_term_in_layer pr info
  | AEnc k iv msg ad -> is_valid_term_in_layer pr k /\ is_valid_term_in_layer pr iv /\ is_valid_term_in_layer pr msg /\ is_valid_term_in_layer pr ad
  | Sig sk n m -> is_valid_term_in_layer pr sk /\ is_valid_term_in_layer pr n /\ is_valid_term_in_layer pr m
  | Mac k m -> is_valid_term_in_layer pr k /\ is_valid_term_in_layer pr m
  | Hash m -> is_valid_term_in_layer pr m
  | DH sk (DH_PK sk') -> is_valid_term_in_layer pr sk /\ is_valid_term_in_layer pr sk' /\
    (match A.get_usage (tls13_key_usages pr) sk, A.get_usage (tls13_key_usages pr) sk' with
    // The terms have dh_key_label usage in tls layer (tls13_key_usages)
    | Some (DHKey s), Some (DHKey s') -> if s = dh_key_label then pr.global_usage.key_usages.dh_unknown_peer_usage s' m == None
					else if s' = dh_key_label then pr.global_usage.key_usages.dh_unknown_peer_usage s m == None
					else True
    | _ -> True)
  | DH sk pk -> is_valid_term_in_layer pr sk /\ is_valid_term_in_layer pr pk 

let rec get_usage_pred (pr:tls_preds) (m:bytes)
	  // (match get_usage pr.global_usage.key_usages m with 
	  // | Some u -> get_usage (tls13_key_usages pr) m == Some u
	  // | None -> (match get_usage (tls13_key_usages pr) m with 
	  // 	   | None -> True
	  // 	   | Some (DHKey s) -> s = dh_key_label
	  // 	   | Some (KDF s) -> s = kdf_key_label
	  // 	   | Some (MAC s) -> s = mac_key_label
	  // 	   | Some (CryptoLib.SIG s) -> s = sig_key_label
	  // 	   | Some (AE s) -> s = aead_key_c_label \/ s = aead_key_rr_label
	  // 	   | _ -> False))) = 
=    match m with 
    | Rand n l u -> () 
    | Extract key _ -> get_usage_pred pr key
    | Expand key info -> get_usage_pred pr key; ()
      // (match get_usage pr.global_usage.key_usages key with 
      // 	| Some (KDF s) -> assert (s <> kdf_key_label); assert (get_usage (tls13_key_usages pr) key == Some (KDF s));
      // 	assert (get_usage pr.global_usage.key_usages m == pr.global_usage.key_usages.kdf_expand_usage s key info);
      // 	assert (get_usage (tls13_key_usages pr) m == pr.global_usage.key_usages.kdf_expand_usage s key info)
      // 	| Some u -> assert (match get_usage (tls13_key_usages pr) m with 
      // 		   | None -> True
      // 		   | Some (DHKey s) -> False
      // 		   | Some (KDF s) -> s = kdf_key_label
      // 		   | Some (MAC s) -> False
      // 		   | Some (CryptoLib.SIG s) -> False 
      // 		   | _ -> False); ()
      // 	| _ -> assert (get_usage pr.global_usage.key_usages m == None);
      // 	      assert (match get_usage (tls13_key_usages pr) key with 
      // 		   | None -> get_usage (tls13_key_usages pr) m == None
      // 		   | Some (DHKey s) -> get_usage (tls13_key_usages pr) m == None
      // 		   | Some (KDF s) -> get_usage (tls13_key_usages pr) m == Some (AE aead_key_c_label) \/
      // 				    get_usage (tls13_key_usages pr) m == Some (AE aead_key_rr_label) \/
      // 				    get_usage (tls13_key_usages pr) m == Some (MAC mac_key_label) \/
      // 				    get_usage (tls13_key_usages pr) m == None
      // 		   | Some (MAC s) -> get_usage (tls13_key_usages pr) m == None
      // 		   | Some (CryptoLib.SIG s) -> get_usage (tls13_key_usages pr) m == None
      // 		   | Some (AE s) -> get_usage (tls13_key_usages pr) m == None
      // 		   | _ -> False); ())
    | CryptoLib.DH sk (DH_PK sk') -> 
      get_usage_pred pr sk; get_usage_pred pr sk'; dh_usage_commutes_lemma pr; dh_unknown_peer_usage_lemma pr; 
      (match get_usage pr.global_usage.key_usages sk, get_usage pr.global_usage.key_usages sk' with
	| Some _, Some _ -> ()
	| Some u, None -> 
	  assert (get_usage pr.global_usage.key_usages sk == get_usage (tls13_global_usage pr).key_usages sk); 
	  (match u with 
	  | DHKey s -> (match get_usage (tls13_key_usages pr) sk, get_usage (tls13_key_usages pr) sk' with 
		      | Some (DHKey s'), None -> ()
		      | Some (DHKey s'), Some (DHKey s'') -> assert (s'' = dh_key_label); assert (s' <> dh_key_label);
			assert (pr.global_usage.key_usages.dh_unknown_peer_usage s m == None); ()
		      | _ -> ())
	  | _ -> ())
	| None, Some (DHKey s) -> ();
	  if s = dh_key_label then () 
	  else 
	    (assert (get_usage pr.global_usage.key_usages m == pr.global_usage.key_usages.dh_unknown_peer_usage s m); 
	    (match get_usage (tls13_key_usages pr) sk, get_usage (tls13_key_usages pr) sk' with 
	    | Some (DHKey s'), Some (DHKey s'') -> assert (s' = dh_key_label); assert (s = s''); assert (s'' <> dh_key_label); 
	      assert (get_usage pr.global_usage.key_usages sk' == get_usage (tls13_key_usages pr) sk');
	      assert (Some (DHKey s) == get_usage (tls13_key_usages pr) sk');
	      assert (get_usage (tls13_key_usages pr) m == (tls13_key_usages pr).dh_shared_secret_usage s' s'' m); 
	      assert (get_usage (tls13_key_usages pr) m == Some (kdf_usage kdf_key_label));
	      assert (pr.global_usage.key_usages.dh_unknown_peer_usage s'' m == None); () 
	    | None, Some (DHKey s'') -> ()
	    | Some u, Some (DHKey s'') -> ()))
        | None, Some u -> 
	  assert (get_usage pr.global_usage.key_usages sk' == get_usage (tls13_global_usage pr).key_usages sk'); 
	  (match u with 
	  | DHKey s -> (match get_usage (tls13_key_usages pr) sk', get_usage (tls13_key_usages pr) sk with 
		      | Some (DHKey s'), None -> ()
		      | Some (DHKey s'), Some (DHKey s'') -> assert (s'' = dh_key_label); assert (s' <> dh_key_label);
			assert (pr.global_usage.key_usages.dh_unknown_peer_usage s m == None); ()
		      | _ -> ())
	  | _ -> ())
	| None, None -> ()) 
    | CryptoLib.DH sk pk -> get_usage_pred pr sk; ()
    | _ -> ()

let rec get_label_pred (pr:tls_preds) (m:bytes) =
  match m with
  | Concat b1 b2 -> get_label_pred pr b1; get_label_pred pr  b2
  | Expand key info -> get_label_pred pr key
  | Sig sk n m -> get_label_pred pr m
  | Mac k m -> get_label_pred pr m
  | Hash m -> get_label_pred pr m
  | CryptoLib.DH sk (DH_PK sk') -> get_label_pred pr sk; get_label_pred pr sk'
  | CryptoLib.DH sk pk -> get_label_pred pr sk 
  | Extract key salt -> get_usage_pred pr key; get_label_pred pr key; get_label_pred pr salt;
		       let kl = (get_label pr.global_usage.key_usages key) in
		       let kl' = (get_label (tls13_key_usages pr) key) in
		       let sl = (get_label pr.global_usage.key_usages salt) in
		       let sl' = (get_label (tls13_key_usages pr) salt) in
		       let l = (meet kl sl) in 
		       let l' = (meet kl' sl') in 
		       assert (l = l');
		       (match get_usage pr.global_usage.key_usages key, get_usage (tls13_key_usages pr) key with 
		       | Some (KDF s), Some (KDF s') -> assert (s = s');
		       	   assert ((get_label (tls13_key_usages pr) m) == (get_label pr.global_usage.key_usages m))
		       | None, Some (KDF s) -> assert (s = kdf_key_label); 
			 assert ((get_label (tls13_key_usages pr) m) == (get_label pr.global_usage.key_usages m))
		       | _ -> assert ((get_label (tls13_key_usages pr) m) == (get_label pr.global_usage.key_usages m))
		       ); () 
  | _ -> ()

 let rec is_valid_in_layer pr i m =  	  
  match m with 
  | Literal _ -> ()
  | Rand n l u -> ()
  | Concat b1 b2 -> is_valid_in_layer pr i b1; is_valid_in_layer pr i b2
  | PK s | VK s | DH_PK s -> is_valid_in_layer pr i s
  | PKEnc pk n msg -> is_valid_in_layer pr i pk; is_valid_in_layer pr i msg; is_valid_in_layer pr i n 
  | Extract key salt -> 
    assert (dh_usage_pred pr /\ kdf_usage_pred pr /\ usage_pred_cond pr /\ kdf_extend_label_flows_to_meet pr /\ key_usages_are_unique pr);
    is_valid_in_layer pr i key; is_valid_in_layer pr i salt;
    get_usage_pred pr key
  | Expand key info -> 
    is_valid_in_layer pr i key; is_valid_in_layer pr i info; get_usage_pred pr key  
  | AEnc k iv msg ad -> is_valid_in_layer pr i k; is_valid_in_layer pr i iv; is_valid_in_layer pr i msg; is_valid_in_layer pr i ad  
  | Sig sk n m -> is_valid_in_layer pr i sk; is_valid_in_layer pr i n; is_valid_in_layer pr i m
  | Mac k m -> is_valid_in_layer pr i k; is_valid_in_layer pr i m
  | Hash m -> is_valid_in_layer pr i m
  | DH sk (DH_PK sk') -> is_valid_in_layer pr i sk; is_valid_in_layer pr i sk';
    get_usage_pred pr sk; get_usage_pred pr sk'
  | DH sk pk -> is_valid_in_layer pr i sk; is_valid_in_layer pr i pk 

let rec is_valid_pred_lemma (pr:tls_preds) (i:nat) (m:bytes) : 
    Lemma (requires (is_valid pr.global_usage i m))
	  (ensures (is_valid (tls13_global_usage pr) i m)) = 
  match m with
  | Literal s -> ()
  | Rand i l u -> ()  
  | PK s | VK s | DH_PK s -> is_valid_pred_lemma pr i s
  | Concat t1 t2 -> is_valid_pred_lemma pr i t1; is_valid_pred_lemma pr i t2
  | PKEnc pk n msg -> is_valid_pred_lemma pr i pk; is_valid_pred_lemma pr i msg; is_valid_pred_lemma pr i n;
    get_label_pred pr n; get_label_pred pr pk; get_label_pred pr msg; 
    let nl = get_label pr.global_usage.key_usages n in let pkl = get_sk_label pr.global_usage.key_usages pk in let ml = get_label pr.global_usage.key_usages msg in
    let npl = get_label (tls13_gu pr).key_usages n in let pkpl = get_sk_label (tls13_gu pr).key_usages pk in let mpl = get_label (tls13_gu pr).key_usages msg in
    let ts = i in 
    assert (can_flow ts ml nl /\ can_flow ts ml pkl); 
    assert (can_flow ts npl nl); assert (can_flow ts mpl ml);
    (match pk with 
    | PK s -> get_usage_pred pr s
    | _ ->  assert (can_flow ts mpl public));
    ()
  | AEnc k iv msg ad -> 
    let ts = i in 
    is_valid_pred_lemma pr ts k; is_valid_pred_lemma pr ts msg; is_valid_pred_lemma pr ts ad; is_valid_pred_lemma pr ts iv;
    get_label_pred pr k; get_label_pred pr ad; get_label_pred pr msg; get_label_pred pr iv;
    let nl = get_label pr.global_usage.key_usages ad in let kl = get_label pr.global_usage.key_usages k in 
    let ml = get_label pr.global_usage.key_usages msg in let ivl = get_label pr.global_usage.key_usages iv in 
    let npl = get_label (tls13_gu pr).key_usages ad in let kpl = get_label (tls13_gu pr).key_usages k in 
    let mpl = get_label (tls13_gu pr).key_usages msg in let ivpl = get_label (tls13_gu pr).key_usages iv in 
    assert (can_flow ts ml kl); assert (can_flow ts mpl kpl);
    assert (can_flow ts nl public);    assert (can_flow ts npl public);
    assert (can_flow ts ivl public);    assert (can_flow ts ivpl public);
    (match get_usage pr.global_usage.key_usages k with
    | Some (AE s) -> get_usage_pred pr k; () | _ -> assert (can_flow ts kpl public); ())
  | Sig sk n msg -> is_valid_pred_lemma pr i sk; is_valid_pred_lemma pr i msg; is_valid_pred_lemma pr i n;
    get_label_pred pr sk; get_label_pred pr msg; get_label_pred pr n;    
    let nl = get_label pr.global_usage.key_usages n in let kl = get_label pr.global_usage.key_usages sk in 
    let ml = get_label pr.global_usage.key_usages msg in 
    let npl = get_label (tls13_gu pr).key_usages n in let kpl = get_label (tls13_gu pr).key_usages sk in 
    let mpl = get_label (tls13_gu pr).key_usages msg in 
    (match get_usage pr.global_usage.key_usages sk with
    | Some (SIG s) -> get_usage_pred pr sk | _ -> assert (can_flow i kpl Public))
  | Mac k msg -> is_valid_pred_lemma pr i k; is_valid_pred_lemma pr i msg; 
    get_label_pred pr k; get_label_pred pr msg; 
    let kpl = get_label (tls13_gu pr).key_usages k in 
    (match get_usage pr.global_usage.key_usages k with
    | Some (MAC s) -> get_usage_pred pr k | _ -> assert (can_flow i kpl public))   
  | Hash msg -> is_valid_pred_lemma pr i msg
  | Expand k1 k2 -> is_valid_pred_lemma pr i k1; is_valid_pred_lemma pr i k2;
    get_label_pred pr k1; get_label_pred pr k2;
    let k1l = get_label pr.global_usage.key_usages k1 in let k2l = get_label pr.global_usage.key_usages k2 in 
    let k1pl = get_label (tls13_gu pr).key_usages k1 in let k2pl = get_label (tls13_gu pr).key_usages k2 in 
    assert (can_flow i k1l public ==> can_flow i k1pl public);
    (match get_usage pr.global_usage.key_usages k1 with | Some (KDF _) -> get_usage_pred pr k1 | _ -> ())
  | Extract k1 k2 -> is_valid_pred_lemma pr i k1; is_valid_pred_lemma pr i k2;
    get_label_pred pr k1; get_label_pred pr k2;
    let k1l = get_label pr.global_usage.key_usages k1 in let k2l = get_label pr.global_usage.key_usages k2 in 
    let k1pl = get_label (tls13_gu pr).key_usages k1 in let k2pl = get_label (tls13_gu pr).key_usages k2 in 
    assert (can_flow i k1l public ==> can_flow i k1pl public);
    assert (can_flow i k2l public ==> can_flow i k2pl public);
    (match get_usage pr.global_usage.key_usages k1 with | Some (KDF _) -> get_usage_pred pr k1 | _ -> ())
  | DH k1 (DH_PK k2) -> is_valid_pred_lemma pr i k1; is_valid_pred_lemma pr i k2;
    get_label_pred pr k1; get_label_pred pr k2;
    let k1l = get_label pr.global_usage.key_usages k1 in let k2l = get_label pr.global_usage.key_usages k2 in 
    let k1pl = get_label (tls13_gu pr).key_usages k1 in let k2pl = get_label (tls13_gu pr).key_usages k2 in 
    assert (can_flow i k1l public ==> can_flow i k1pl public);
    assert (can_flow i k2l public ==> can_flow i k2pl public);
    get_usage_pred pr k1; get_usage_pred pr k2
  | DH k1 k2 -> is_valid_pred_lemma pr i k1; is_valid_pred_lemma pr i k2;
    get_label_pred pr k1; get_label_pred pr k2;
    let k1l = get_label pr.global_usage.key_usages k1 in let k2l = get_label pr.global_usage.key_usages k2 in 
    let k1pl = get_label (tls13_gu pr).key_usages k1 in let k2pl = get_label (tls13_gu pr).key_usages k2 in 
    assert (can_flow i k1l public ==> can_flow i k1pl public);
    assert (can_flow i k2l public /\ can_flow i k2pl public);
    get_usage_pred pr k1; get_usage_pred pr k2

let rec is_valid_pred_inv_lemma (pr:tls_preds) (i:nat) (m:bytes) : 
    Lemma (requires (is_valid (tls13_global_usage pr) i m))
	  (ensures (is_valid pr.global_usage i m)) = 
  match m with
  | Literal s -> ()
  | Rand i l u -> ()  
  | PK s | VK s | DH_PK s -> is_valid_pred_inv_lemma pr i s
  | Concat t1 t2 -> is_valid_pred_inv_lemma pr i t1; is_valid_pred_inv_lemma pr i t2
  | PKEnc pk n msg -> is_valid_pred_inv_lemma pr i pk; is_valid_pred_inv_lemma pr i msg; is_valid_pred_inv_lemma pr i n;
    get_label_pred pr n; get_label_pred pr pk; get_label_pred pr msg; 
    let nl = get_label pr.global_usage.key_usages n in let pkl = get_sk_label pr.global_usage.key_usages pk in let ml = get_label pr.global_usage.key_usages msg in
    let npl = get_label (tls13_gu pr).key_usages n in let pkpl = get_sk_label (tls13_gu pr).key_usages pk in let mpl = get_label (tls13_gu pr).key_usages msg in
    let ts = i in 
    assert (can_flow ts ml nl /\ can_flow ts ml pkl); 
    assert (can_flow ts npl nl); assert (can_flow ts mpl ml);
    (match pk with 
    | PK s -> get_usage_pred pr s
    | _ ->  assert (can_flow ts mpl public));
    ()
  | AEnc k iv msg ad -> 
    let ts = i in 
    is_valid_pred_inv_lemma pr ts k; is_valid_pred_inv_lemma pr ts msg; is_valid_pred_inv_lemma pr ts ad; is_valid_pred_inv_lemma pr ts iv;
    get_label_pred pr k; get_label_pred pr ad; get_label_pred pr msg; get_label_pred pr iv;
    let nl = get_label pr.global_usage.key_usages ad in let kl = get_label pr.global_usage.key_usages k in 
    let ml = get_label pr.global_usage.key_usages msg in let ivl = get_label pr.global_usage.key_usages iv in 
    let npl = get_label (tls13_gu pr).key_usages ad in let kpl = get_label (tls13_gu pr).key_usages k in 
    let mpl = get_label (tls13_gu pr).key_usages msg in let ivpl = get_label (tls13_gu pr).key_usages iv in 
    assert (can_flow ts ml kl); assert (can_flow ts mpl kpl);
    assert (can_flow ts nl public);    assert (can_flow ts npl public);
    assert (can_flow ts ivl public);    assert (can_flow ts ivpl public);
    (match get_usage pr.global_usage.key_usages k with
    | Some (AE s) -> get_usage_pred pr k; () | _ -> assert (can_flow ts kpl public); ())
  | Sig sk n msg -> is_valid_pred_inv_lemma pr i sk; is_valid_pred_inv_lemma pr i msg; is_valid_pred_inv_lemma pr i n;
    get_label_pred pr sk; get_label_pred pr msg; get_label_pred pr n;    
    let nl = get_label pr.global_usage.key_usages n in let kl = get_label pr.global_usage.key_usages sk in 
    let ml = get_label pr.global_usage.key_usages msg in 
    let npl = get_label (tls13_gu pr).key_usages n in let kpl = get_label (tls13_gu pr).key_usages sk in 
    let mpl = get_label (tls13_gu pr).key_usages msg in 
    (match get_usage pr.global_usage.key_usages sk with
    | Some (SIG s) -> get_usage_pred pr sk | _ -> assert (can_flow i kpl Public))
  | Mac k msg -> is_valid_pred_inv_lemma pr i k; is_valid_pred_inv_lemma pr i msg; 
    get_label_pred pr k; get_label_pred pr msg; 
    let kpl = get_label (tls13_gu pr).key_usages k in 
    (match get_usage pr.global_usage.key_usages k with
    | Some (MAC s) -> get_usage_pred pr k | _ -> assert (can_flow i kpl public))   
  | Hash msg -> is_valid_pred_inv_lemma pr i msg
  | Expand k1 k2 -> is_valid_pred_inv_lemma pr i k1; is_valid_pred_inv_lemma pr i k2;
    get_label_pred pr k1; get_label_pred pr k2;
    let k1l = get_label pr.global_usage.key_usages k1 in let k2l = get_label pr.global_usage.key_usages k2 in 
    let k1pl = get_label (tls13_gu pr).key_usages k1 in let k2pl = get_label (tls13_gu pr).key_usages k2 in 
    assert (can_flow i k1l public ==> can_flow i k1pl public);
    (match get_usage pr.global_usage.key_usages k1 with | Some (KDF _) -> get_usage_pred pr k1 | _ -> ())
  | Extract k1 k2 -> is_valid_pred_inv_lemma pr i k1; is_valid_pred_inv_lemma pr i k2;
    get_label_pred pr k1; get_label_pred pr k2;
    let k1l = get_label pr.global_usage.key_usages k1 in let k2l = get_label pr.global_usage.key_usages k2 in 
    let k1pl = get_label (tls13_gu pr).key_usages k1 in let k2pl = get_label (tls13_gu pr).key_usages k2 in 
    assert (can_flow i k1l public ==> can_flow i k1pl public);
    assert (can_flow i k2l public ==> can_flow i k2pl public);
    (match get_usage pr.global_usage.key_usages k1 with | Some (KDF _) -> get_usage_pred pr k1 | _ -> ())
  | DH k1 (DH_PK k2) -> is_valid_pred_inv_lemma pr i k1; is_valid_pred_inv_lemma pr i k2;
    get_label_pred pr k1; get_label_pred pr k2;
    let k1l = get_label pr.global_usage.key_usages k1 in let k2l = get_label pr.global_usage.key_usages k2 in 
    let k1pl = get_label (tls13_gu pr).key_usages k1 in let k2pl = get_label (tls13_gu pr).key_usages k2 in 
    assert (can_flow i k1l public ==> can_flow i k1pl public);
    assert (can_flow i k2l public ==> can_flow i k2pl public);
    get_usage_pred pr k1; get_usage_pred pr k2
  | DH k1 k2 -> is_valid_pred_inv_lemma pr i k1; is_valid_pred_inv_lemma pr i k2;
    get_label_pred pr k1; get_label_pred pr k2;
    let k1l = get_label pr.global_usage.key_usages k1 in let k2l = get_label pr.global_usage.key_usages k2 in 
    let k1pl = get_label (tls13_gu pr).key_usages k1 in let k2pl = get_label (tls13_gu pr).key_usages k2 in 
    assert (can_flow i k1l public ==> can_flow i k1pl public);
    assert (can_flow i k2l public /\ can_flow i k2pl public);
    get_usage_pred pr k1; get_usage_pred pr k2
#pop-options


