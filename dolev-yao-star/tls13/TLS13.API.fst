/// TLS13.API (implementation of the transport phase)
/// =================================================
module TLS13.API

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0" 

module A = LabeledCryptoAPI

val get_responder_session: #preds:tls13_layer_preds -> i:nat -> initiator:principal -> responder:principal ->
    LCrypto (nat * nat * session_st) (tls_app preds)
		(requires (fun t0 -> i == trace_len t0))
		(ensures (fun t0 (sid, vi, st) t1 -> t0 == t1 /\ valid_session preds i initiator sid vi st /\
					     (match st with 
					       | InitiatorState b ak akrr -> b = responder
					       | InitiatorStSymKey b ak akrr sk -> b = responder
					       | _ -> False)))

let get_responder_session #preds i initiator responder = 
  let filter si vi st = match parse_session_st st with
    | Success (InitiatorState b _ _) 
    | Success (InitiatorStSymKey b _ _ _) -> b = responder
    | _ -> false in
  match find_session #(tls13_app preds) #i initiator filter with
  | Some (|si,vi,st|) ->
    (match parse_session_st st with
    | Success (InitiatorState b ak akrr) -> (si, vi, InitiatorState b ak akrr)
    | Success (InitiatorStSymKey b ak akrr sk) -> (si, vi, InitiatorStSymKey b ak akrr sk)
    |_ -> error "not the right state")
  | None -> error "no responder session exists"

val get_initiator_session: #preds:tls13_layer_preds -> i:nat -> initiator:principal -> responder:principal ->
    LCrypto (nat * nat * session_st) (tls_app preds)
		(requires (fun t0 -> i == trace_len t0))
		(ensures (fun t0 (sid, vi, st) t1 -> t0 == t1 /\ valid_session preds i responder sid vi st /\
						  (match st with | ResponderState b _ _  -> b = initiator | _ -> False)))

let get_initiator_session #preds i initiator responder = 
  let filter si vi st = match parse_session_st st with
    | Success (ResponderState a _ _) -> a = initiator
    | _ -> false in
  match find_session #(tls13_app preds) #i responder filter with
  | Some (|si,vi,st|) ->
    (match parse_session_st st with
    | Success (ResponderState a ak akrr) -> (si, vi, ResponderState a ak akrr)
    | _ -> error "not the right state")
  | None -> error "no initiator session exists"

let send #i #preds sender receiver m = 
  let t0 = global_timestamp () in   
  assert (later_than t0 i);
  let (si, vi, st) = get_responder_session #preds t0 sender receiver in
  (match st with
  | (InitiatorState b ak akrr) -> 
      begin
      // b = receiver
        can_flow_readers_to_join t0 (P sender) (P b);
        can_flow_from_join t0 (readers [P sender]) (readers [P b]);
        unsession_of_si_vi sender si 0;        
        can_flow_principal t0 sender;
        can_flow_from_join  t0 (readers[P b]) (readers [P sender ]);
        can_flow_to_join_forall t0; can_flow_to_meet_forall t0;
        unsession_of_join (readers[P b]) (readers [P sender]);
        unsession_of_si_vi b 0 0;
        can_flow_to_join_forall t0; 
	let m:msg preds t0 (join (readers [P receiver]) (readers [P sender])) = m in 
	assert (can_flow t0 (join (readers [P receiver]) (readers [P sender])) (readers [P receiver]));
	let m = restrict m (get_label (tls13_app_key_usages preds) ak) in 
	let m:msg preds t0 (get_label (tls13_app_key_usages preds) ak) = m in 
	// send the message
        let iv = empty #(tls13_app_global_usage preds) #t0 in
        let ad = empty #(tls13_app_global_usage preds) #t0 in
	can_flow_transitive t0 (get_label (tls13_app_key_usages preds) ak) (readers [P b]) public;
        let m = aead_enc ak iv m ad in 
	get_label_pred (tls13_app preds) m;
        let mi = send #(tls_app preds) #t0 sender receiver m in 
        (|si, m, mi|)
      end
  | _ -> error "wrong session state") 
 
let receive_i (#preds:tls13_layer_preds) (index_of_send_event:timestamp) (receiver:principal):
    LCrypto (now:timestamp & sender:principal & msg preds now public) (tls_app preds)
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,sender,t|) t1 ->  t0 == t1 /\
          now = trace_len t0 /\
          index_of_send_event < trace_len t0 /\
          (exists sender receiver. was_message_sent_at index_of_send_event sender receiver t))) =
    let (|now,sender,msg|) = receive_i #(tls_app preds) index_of_send_event receiver in
    assert (A.is_msg (tls13_global_usage (tls13_app preds)) now msg public);
    assert (A.is_msg (tls13_app_global_usage preds) now msg public);
    (|now,sender,msg|)

let recv #preds index_of_send_event receiver = 
  let (|t, sender, m|) =  receive_i #preds index_of_send_event receiver in
  let t0 = global_timestamp () in 
  let (si, vi, st) = get_initiator_session #preds t0 sender receiver in 
  (match st with
  | ResponderState a ak akrr ->
    let v0 = 0 in assert (a = sender);
    assert (A.corrupt_id t0 (P a) \/ (is_app_aead_conf_key preds t0 ak receiver a));
    can_flow_readers_to_join t0 (P receiver) (P a);
    can_flow_from_join t0 (readers [P receiver]) (readers [P a]);
    unsession_of_si_vi receiver si 0;        
    can_flow_principal t0 receiver;
    can_flow_from_join  t0 (readers[P receiver]) (readers [P a]);
    can_flow_to_join_forall t0; can_flow_to_meet_forall t0;
    unsession_of_join (readers[P receiver]) (readers [P a]);
    unsession_of_si_vi a 0 0;
    can_flow_to_join_forall t0; 
    assert ( can_flow t0 (get_label (tls13_app_key_usages preds) ak) (readers [P a]));
    assert (A.corrupt_id t0 (P a) ==> can_flow t0 (readers [P a]) public);
    assert (A.corrupt_id t0 (P a) ==> can_flow t0 (get_label (tls13_app_key_usages preds) ak) public);
    assert (A.corrupt_id t0 (P a) ==> is_publishable (tls13_app_global_usage preds) t0 ak);
    (match aead_dec ak (empty #(tls13_app_global_usage preds) #t0) m (empty #(tls13_app_global_usage preds) #t0) with 
      | Success msg -> 
	CryptoLib.aead_dec_lemma ak (empty #(tls13_app_global_usage preds) #t0) m (empty #(tls13_app_global_usage preds) #t0);
	// preds.extended_higher_layer_gu.send_function_predicates.confidential_send_pred_later msg;
        // prove that label of 'msg' can flow to [S s si], for some si 
	let msg = restrict #_ #_ #(get_label (tls13_app_key_usages preds) ak) msg (readers [P receiver]) in 
	let t1 = global_timestamp () in
	(|t1, sender, msg|)
      | _ -> error "decryption error")
  | _ -> error "wrong session state")

let send_request #i #preds sender receiver message = 
let t0 = global_timestamp () in   
  assert (later_than t0 i);
  let (si, vi, st) = get_responder_session #preds t0 sender receiver in
    (match st with
    | InitiatorState b ak akrr -> 
      begin
      // b = receiver
	let (|t0, sym_key|) = rand_gen #(tls_app preds) (join (readers [P receiver]) (readers [P sender])) (aead_usage "AEAD.Symmetric_Send_Key") in
	let t0 = global_timestamp () in     
	assert(later_than t0 i);
	let sym_key:msg preds t0 (join (readers [P receiver]) (readers [P sender])) = sym_key in
	// let receiver_bytes = string_to_bytes #(tls13_app_global_usage preds) #t0 receiver in
	// let sender_bytes = string_to_bytes #(tls13_app_global_usage preds) #t0 sender in
	let final_message = concat sym_key message in // (concat sym_key (concat sender_bytes receiver_bytes)) message in
	rand_is_secret #(tls13_app_global_usage preds) #t0 #(join (readers [P receiver]) (readers [P sender])) #(aead_usage "AEAD.Symmetric_Send_Key") sym_key;

        can_flow_readers_to_join t0 (P sender) (P b);
        can_flow_from_join t0 (readers [P sender]) (readers [P b]);
        unsession_of_si_vi sender si 0;        
        can_flow_principal t0 sender; 
        can_flow_from_join  t0 (readers [P b]) (readers [P sender]);
        can_flow_to_join_forall t0; can_flow_to_meet_forall t0;
        unsession_of_join (readers[P b]) (readers [P sender]);
        unsession_of_si_vi b 0 0;
        can_flow_to_join_forall t0;
	let m:msg preds t0 (join (readers [P b]) (readers [P sender])) = final_message in 
	let m = restrict m (get_label (tls13_app_key_usages preds) akrr) in 

        // store the state in trace
        let new_ss_st = InitiatorStSymKey b ak akrr sym_key in
        let new_ss = serialize_valid_session_st preds t0 sender si 0 new_ss_st in
        new_session #(tls13_app preds) #t0 sender si 0 new_ss;

        // send the message
        let iv = empty #(tls13_app_global_usage preds) #t0 in
        let ad = empty #(tls13_app_global_usage preds) #t0 in
        assert ((exists p. can_flow t0 (get_label (tls13_app_key_usages preds) m) (readers [P p])));

	assert (A.corrupt_id t0 (P b) \/ is_app_aead_rr_key preds t0 akrr sender b);
	assert ( can_flow t0 (get_label (tls13_app_key_usages preds) akrr) (readers [P b]));
	assert (A.corrupt_id t0 (P b) ==> can_flow t0 (readers [P b]) public);
	assert (A.corrupt_id t0 (P b) ==> can_flow t0 (get_label (tls13_app_key_usages preds) akrr) public);
	assert (A.corrupt_id t0 (P b) ==> is_publishable (tls13_app_global_usage preds) t0 akrr);
        let m = aead_enc akrr iv m ad in 
        let mi = LabeledRuntimeAPI.send #(tls_app preds) #t0 sender b m in
	is_request_at_idx_injective_forall ();  
        (|si, sym_key, mi|)
      end 
    | _ -> error "wrong session state")   


let receive_request #i #preds index_of_send_event receiver = 
  let (|t, sender, m|) =  LabeledRuntimeAPI.receive_i #(tls_app preds) index_of_send_event receiver in
  let t0 = global_timestamp () in 
  let (si, vi, st) = get_initiator_session #preds t0 sender receiver in 
  (match st with
  | ResponderState b ak akrr ->
    let v0 = 0 in 
    assert (b = sender);
    assert (can_flow t0 (get_label (tls13_app_key_usages preds) akrr) (readers [P b]));
    assert (can_flow t0 (get_label (tls13_app_key_usages preds) akrr) (readers [P receiver]));
    assert (A.corrupt_id t0 (P b) ==> can_flow t0 (readers [P b]) public);
    assert (A.corrupt_id t0 (P b) ==> can_flow t0 (get_label (tls13_app_key_usages preds) akrr) public);
    assert (A.corrupt_id t0 (P b) ==> is_publishable (tls13_app_global_usage preds) t0 akrr);
    (match aead_dec #(tls13_app_global_usage preds) #t0 #(get_label (tls13_app_key_usages preds) akrr) akrr (empty #(tls13_app_global_usage preds) #t0) m (empty #(tls13_app_global_usage preds) #t0) with 
      | Success msg -> 
	CryptoLib.aead_dec_lemma akrr (empty #(tls13_app_global_usage preds) #t0) m (empty #(tls13_app_global_usage preds) #t0);
	// preds.extended_higher_layer_gu.send_function_predicates.confidential_send_pred_later msg;
	let plaintext = msg in 
	let now = t0 in 
	(match split plaintext with
	| Error _ -> error "Incorrect request format."
	| Success (sym_key, payload) -> ( 
	  splittable_term_publishable_implies_components_publishable_forall ((tls13_app_global_usage preds));
	  CryptoLib.split_based_on_split_len_prefixed_lemma plaintext;
	  assert(forall i. (is_succ2 (CryptoLib.split_len_prefixed 4 plaintext) sym_key payload /\ 
		      is_publishable (tls13_app_global_usage preds) i plaintext) ==>
		  	(is_publishable (tls13_app_global_usage preds) i sym_key /\ is_publishable (tls13_app_global_usage preds) i payload));
	  assert (is_publishable (tls13_app_global_usage preds) now plaintext \/ 
		 ((exists s r. was_rand_generated_before now sym_key (join (readers [P s]) (readers [P r])) (aead_usage "AEAD.Symmetric_Send_Key") /\
			  // (A.can_flow now (A.get_label (tls13_app_key_usages preds) akrr) public \/ 
			  // 		A.can_flow now (A.get_label (tls13_app_key_usages preds) akrr) (join (readers [P s]) (readers [P r])))) /\
		    (exists (j:timestamp). j <= now /\ preds.extended_higher_layer_gu.send_function_predicates.request_pred j payload) /\
			 A.can_flow now (A.get_label (tls13_app_key_usages preds) payload) (A.get_label (tls13_app_key_usages preds) sym_key)
			 ))); 
	  assert (sender <> receiver);
	  assert (forall j now. j <= now <==> later_than now j);
	  assert (is_publishable (tls13_app_global_usage preds) now plaintext \/
		 ((exists s r. was_rand_generated_before now sym_key (join (readers [P s]) (readers [P r])) (aead_usage "AEAD.Symmetric_Send_Key")) /\ 
		 (exists j. later_than now j /\ preds.extended_higher_layer_gu.send_function_predicates.request_pred j payload)));
	  assert (is_publishable (tls13_app_global_usage preds) now plaintext ==>
		  		(is_publishable (tls13_app_global_usage preds) now payload /\
		  		is_publishable (tls13_app_global_usage preds) now sym_key)); 
	  assert ((is_publishable (tls13_app_global_usage preds) now payload /\ is_publishable (tls13_app_global_usage preds) now sym_key) \/
		 ((exists s r. was_rand_generated_before now sym_key (join (readers [P s]) (readers [P r])) (aead_usage "AEAD.Symmetric_Send_Key")) /\ 
		 (exists j. later_than now j /\ preds.extended_higher_layer_gu.send_function_predicates.request_pred j payload)));
	  rand_is_secret_forall_labels #(tls13_app_global_usage preds) #t0 #(aead_usage "AEAD.Symmetric_Send_Key") sym_key;
	  assert ((is_publishable (tls13_app_global_usage preds) now payload /\ is_publishable (tls13_app_global_usage preds) now sym_key) \/
		 ((exists s r. is_aead_key (tls13_app_global_usage preds) now sym_key (join (readers [P s]) (readers [P r])) "AEAD.Symmetric_Send_Key") /\ 
		 (exists j. later_than now j /\ preds.extended_higher_layer_gu.send_function_predicates.request_pred j payload)));
	  let sym_key_label = get_label (tls13_app_key_usages preds) sym_key in
	  assert(can_flow now sym_key_label (readers [P receiver]) /\ can_flow now sym_key_label (readers [P sender]));
	  can_flow_to_join_and_principal_and_unpublishable_property now; 
	  join_forall_is_equal now sym_key_label sender receiver; 
	  assert ((is_publishable (tls13_app_global_usage preds) now payload /\ is_publishable (tls13_app_global_usage preds) now sym_key) \/
	  	 ((was_rand_generated_before now sym_key (join (readers [P sender]) (readers [P receiver])) (aead_usage "AEAD.Symmetric_Send_Key")) /\ 
	  	 (exists j. later_than now j /\ preds.extended_higher_layer_gu.send_function_predicates.request_pred j payload)));
	  //show that [is_request_at_idx] is true:
	  assert ((is_publishable (tls13_app_global_usage preds) now payload /\ is_publishable (tls13_app_global_usage preds) now sym_key) \/
		 (is_aead_key (tls13_app_global_usage preds) now sym_key (join (readers [P sender]) (readers [P receiver])) "AEAD.Symmetric_Send_Key" /\ 
		 (exists j. later_than now j /\ preds.extended_higher_layer_gu.send_function_predicates.request_pred j payload)));
	  concat_split_lemma plaintext;
	  assert(plaintext == CryptoLib.concat sym_key payload); 
	  assert (exists sender' receiver full_request. was_message_sent_at index_of_send_event sender' receiver full_request /\ full_request == m);
 	  assert(is_request_at_idx payload index_of_send_event sym_key);
	  assert(can_flow now (get_label (tls13_app_key_usages preds) payload) (get_label (tls13_app_key_usages preds) sym_key));
	  (|now, sender, sym_key, payload|)
	  )
	)
      | _ -> error "decryption error") 
    | _ -> error "wrong session state")  


let send_response #i #l #pred initiator responder sym_key send_idx_of_request request message =
  let t0 = global_timestamp () in 
  let (si, vi, st) = get_initiator_session #pred t0 initiator responder in 
  (match st with
    | ResponderState b ak akrr ->
      let gu = (tls13_app_global_usage pred) in
      let now = GlobalRuntimeLib.global_timestamp() in
      let msg_tag:msg pred now l = LabeledCryptoAPI.string_to_bytes #gu #now "Communication.Layer.Response" in
      let message_with_request_idx = LabeledCryptoAPI.concat (LabeledCryptoAPI.nat_to_bytes #gu #i 0 send_idx_of_request) message in
      assert(later_than now i);
      let plaintext = LabeledCryptoAPI.concat msg_tag message_with_request_idx in
      let (|now, iv|) = rand_gen #(tls_app pred) public (nonce_usage "AEAD.iv") in
      let ad = (LabeledCryptoAPI.string_to_bytes #gu #now "") in
      assert(is_publishable gu now sym_key \/ (exists s. is_aead_key gu now sym_key l s));
      assert(is_publishable gu now sym_key \/ (apred pred now "AEAD.Symmetric_Send_Key" sym_key plaintext ad));
      assert(is_publishable gu now sym_key ==> (forall (s:string). apred pred now s sym_key plaintext ad));
      assert(is_aead_key gu now sym_key l "AEAD.Symmetric_Send_Key" ==> (apred pred now "AEAD.Symmetric_Send_Key" sym_key plaintext ad));
      let encrypted_response:msg pred now public = LabeledCryptoAPI.aead_enc #gu #now #l sym_key iv plaintext ad in
      let final_message = concat iv encrypted_response in //TODO: discuss: IV is appended to the message
      let send_idx = LabeledRuntimeAPI.send #(tls_app pred) #now responder initiator final_message in
      send_idx
    | _ -> error "wrong session state"
    )

let receive_response #preds sym_key_state_session_idx index_of_send_event_of_response initiator =
  let (|now, claimed_responder, iv_and_encrypted_response|) =  LabeledRuntimeAPI.receive_i #(tls_app preds) index_of_send_event_of_response initiator in
  let (si, vi, st) = get_responder_session #preds now initiator claimed_responder in 
  (match st with
  | InitiatorStSymKey b ak akrr sym_key -> 
      assert (b == claimed_responder);
      assert(was_rand_generated_before now sym_key (join (readers [P initiator]) (readers [P b])) (aead_usage "AEAD.Symmetric_Send_Key"));
      let gu = (tls13_app_global_usage preds) in
      (match split iv_and_encrypted_response with
      | Error _ -> error "TODO"
      | Success (iv, encrypted_response) -> (
        let ad = (LabeledCryptoAPI.string_to_bytes #gu #now "") in
        rand_is_secret #gu #now #(join (readers [P initiator]) (readers [P b])) #(aead_usage "AEAD.Symmetric_Send_Key") sym_key;
        assert(is_publishable gu now sym_key \/
               is_aead_key gu now sym_key (join (readers [P initiator]) (readers [P b])) "AEAD.Symmetric_Send_Key");
	match LabeledCryptoAPI.aead_dec #gu #now #(join (readers [P initiator]) (readers [P b])) sym_key iv encrypted_response ad with
        | Error _ -> error "TODO"
        | Success (msg_tag_and_plaintext_payload: msg preds now (join (readers [P initiator]) (readers [P b]))) -> (
          match split msg_tag_and_plaintext_payload with
          | Error _ -> error "TODO: plaintext: wrong format"
          | Success (msg_tag_bytes, request_send_idx_and_plaintext_response) -> (
            match bytes_to_string msg_tag_bytes with
            | Error _ -> error "TODO"
            | Success msg_tag -> (
              if msg_tag = "Communication.Layer.Response" then (
                 match split request_send_idx_and_plaintext_response with
                 | Error _ -> error "TODO: error"
		 | Success (request_idx_bytes, plaintext_response) -> (
                   match bytes_to_nat request_idx_bytes with
                   | Error _ -> error "TODO"
                   | Success request_idx -> (
		     let response_pred = preds.extended_higher_layer_gu.send_function_predicates.response_pred in
		     assert(can_flow now (join (readers [P initiator]) (readers [P b])) public \/
				     (apred preds now "AEAD.Symmetric_Send_Key" sym_key msg_tag_and_plaintext_payload ad));					 
		     assert(can_flow now (join (readers [P initiator]) (readers [P b])) public \/
				     (match split request_send_idx_and_plaintext_response with
				     | Success (request_send_idx_bytes, response) -> 
				       request_send_idx_bytes = request_idx_bytes /\ plaintext_response = response /\ (
				       match bytes_to_nat request_send_idx_bytes with
				       | Success request_send_idx -> request_send_idx = request_idx /\
					 (exists sym_key j request. j <= now /\ response_pred j response request sym_key /\ 
								    Communication.MessageStructurePredicates.is_request_at_idx request request_send_idx sym_key))));
		     assert(can_flow now (join (readers [P initiator]) (readers [P b])) public \/
				     (exists sym_key j request. j <= now /\ response_pred j plaintext_response request sym_key /\ 
				     	Communication.MessageStructurePredicates.is_request_at_idx request request_idx sym_key));
		     can_flow_join_labels_public_lemma now (readers [P initiator]) (readers [P b]);
		     can_flow_from_join now (readers [P initiator]) (readers [P b]);
                     assert ((corrupt_id now (P initiator) \/ corrupt_id now (P b)) \/
					 (exists j request sym_key. later_than now j /\ response_pred j plaintext_response request sym_key /\ 
							       is_request_at_idx request request_idx sym_key));
                     LabeledCryptoAPI.can_flow_from_join now (readers [P initiator]) (readers [P b]);
                     let plaintext_response:msg preds now (readers [(P initiator)]) = plaintext_response in
                     assert(is_msg preds now plaintext_response (readers [P b])); 
		     assert(is_msg preds now plaintext_response (readers [P initiator])); 
                     (| now, b, plaintext_response, request_idx |) 
                     ))
                   ) else error "TODO"
                 )
               )
             )
           )
      ) 
    | _ -> error "incorrect session state")
  
