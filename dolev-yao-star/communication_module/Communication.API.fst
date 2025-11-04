/// Communication.API (Implementation)
/// ==================================

module Communication.API

open SecurityLemmas
friend Communication.MessageStructurePredicates
friend Communication.UsagePredicates

let send #i #higher_level_preds sender receiver message channel_property =
  let now = GlobalRuntimeLib.global_timestamp() in
  if (channel_property = Raw) then
  (
    assert(later_than now i);
    assert(is_publishable higher_level_preds.extended_higher_layer_gu now message);
    LabeledPKI.send #(send_preds higher_level_preds) #now sender receiver message
  )
  else if (channel_property = AuthN) then (
   let (|now, signed_message|) = create_authn_message #i #higher_level_preds sender receiver message in
   let result = LabeledPKI.send #(send_preds higher_level_preds) #now sender receiver signed_message in
   assert(is_authenticated_message i message signed_message);
   assert(exists sender'. was_message_sent_at result sender' receiver signed_message);
   result
  )
  else if (channel_property = Conf) then
  (
   let (|now, confidential_message|) = create_conf_message #i #higher_level_preds sender receiver message in
   LabeledPKI.send #(send_preds higher_level_preds) #now sender receiver confidential_message
   // let (|si, m', mi|) = TLS13.API.send #i #higher_level_preds sender receiver message in 
   // mi
  )
  else ( //authenticated+confidential
   assert(channel_property = AuthNConf);
   let (|now, authn_conf_message|) = create_authn_conf_message #i #higher_level_preds sender receiver message in
   LabeledPKI.send #(send_preds higher_level_preds) #now sender receiver authn_conf_message
  )

let receive_i #higher_level_preds index_of_send_event receiver channel_property =
  if (channel_property = Raw) then(
    let (|now,claimed_sender,m|) = LabeledPKI.receive_i #(send_preds higher_level_preds) index_of_send_event receiver in
    assert(exists sender recv. was_message_sent_at index_of_send_event sender recv m);
    (|now,claimed_sender,m|)
  )
  else if (channel_property = AuthN) then (
    let (| now, sender, signed_message |) = LabeledPKI.receive_i #(send_preds higher_level_preds) index_of_send_event receiver in
    let message = process_authn_message #now #higher_level_preds sender receiver index_of_send_event signed_message in
    assert(exists verify_idx. is_authenticated_message verify_idx message signed_message);
    assert(exists (verification_idx:nat).
      is_authenticated_message_sent_at index_of_send_event verification_idx message signed_message
    );
    (|now,sender,message|)
  )
  else if (channel_property = Conf) then (
    let (|now,claimed_sender,m |) = LabeledPKI.receive_i #(send_preds higher_level_preds) index_of_send_event receiver in
    let plaintext = process_conf_message receiver m in
    // let (|now, claimed_sender, plaintext|) = TLS13.API.recv #higher_level_preds index_of_send_event receiver in 
    (|now, claimed_sender, plaintext|)
  )
  else ( //authenticated+confidential
   assert(channel_property = AuthNConf);
   let (| now, sender, msg |) = LabeledPKI.receive_i #(send_preds higher_level_preds) index_of_send_event receiver in
   let (|_, message_payload|) = process_authn_conf_message #now #higher_level_preds sender receiver index_of_send_event msg in
   (|now, sender, message_payload|)
  )

(** The pke implementation for sending a request. 
    Here we encrypt both the symmetric key and the payload asymmetrically (i.e., as a single ciphertext)
*)
val initiator_send_request_pke:
    #i:timestamp ->
    #higher_level_preds:send_layer_preds ->
    sender:principal ->
    receiver:principal ->
    message:msg higher_level_preds.extended_higher_layer_gu i (join (readers [P sender]) (readers [P receiver])) ->
    LCrypto (sym_key_session_state_idx:nat & sym_key:C.bytes & message_idx:timestamp) (pki (send_preds higher_level_preds))
    (requires (fun t0 ->
      let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
      (i <= trace_len t0) /\
      send_predicates.request_pred i message
    ))
    (ensures (fun t0 (|_, sym_key, message_idx|) t1 ->
      (is_request_at_idx message message_idx sym_key) /\
      is_aead_key (higher_level_preds.extended_higher_layer_gu) (trace_len t1) sym_key (join (readers [P sender]) (readers [P receiver])) "AEAD.Symmetric_Send_Key"
    ))


(**
  1. create symmetric key for the receiver
  2. final_message: sym_key || message
  3. create and send confidential message
  4. store (sym_key, send_idx) in state of sender
  5. return send_idx
*)
let initiator_send_request_pke #i #higher_level_preds sender receiver message =
  let key_usages = higher_level_preds.extended_higher_layer_gu.higher_layer_gu.LabeledCryptoAPI.key_usages in
  let (|t0, sym_key|) = LabeledPKI.rand_gen #(send_preds higher_level_preds) (join (readers [P sender]) (readers [P receiver])) (C.aead_usage "AEAD.Symmetric_Send_Key") in
  assert(later_than t0 i);

  // The [message] can flow to the join label. To concatenate the symmetric key with the message, we
  // show that the key can also flow to the join label:
  assert(LCA.can_flow t0 (LCA.get_label key_usages sym_key) (readers [P sender]));
  assert(LCA.can_flow t0 (LCA.get_label key_usages sym_key) (readers [P receiver]));
  LabeledCryptoAPI.can_flow_to_join_forall t0;
  assert(LCA.can_flow t0 (LCA.get_label key_usages sym_key) (join (readers [P sender]) (readers [P receiver])));

  let sym_key:msg higher_level_preds.extended_higher_layer_gu t0 (join (readers [P sender]) (readers [P receiver])) = sym_key in
  let final_message = concat sym_key message in

  rand_is_secret #higher_level_preds.extended_higher_layer_gu #t0 #(join (readers [P sender]) (readers [P receiver])) #(C.aead_usage "AEAD.Symmetric_Send_Key") sym_key;

  assert(LCA.can_flow i (LCA.get_label key_usages message) (LCA.get_label key_usages sym_key));

  let (|now, confidential_message|) = create_conf_message_for_request_pke #t0 #higher_level_preds sender receiver final_message in

  let send_idx = LabeledPKI.send #(send_preds higher_level_preds) #now sender receiver confidential_message in

  // store (send_idx, key) to the state of [sender]
  let connection_info_session = CommunicationState send_idx sym_key receiver in
  let new_si = LabeledPKI.new_session_number #(send_preds higher_level_preds) sender in
 
  let serialized_connection_info_session = serialize_session_st connection_info_session in

  let t_now = GlobalRuntimeLib.global_timestamp () in

  assert(valid_session higher_level_preds t_now sender new_si 0 connection_info_session);

  assert(later_than t_now i);

  serialized_session_st_flows_to_principal_state_session higher_level_preds (send_preds higher_level_preds).LabeledRuntimeAPI.global_usage t_now sender new_si 0 connection_info_session;

  assert(is_msg higher_level_preds.extended_higher_layer_gu t_now serialized_connection_info_session (readers [V sender new_si 0]));

  LabeledPKI.new_session #(send_preds higher_level_preds) #t_now sender new_si 0 serialized_connection_info_session;

  assert(is_confidential_message final_message confidential_message);
  assert(is_request_at_idx message send_idx sym_key);

  (|new_si, sym_key, send_idx|)


val initiator_send_request_pke_auth:
    #i:timestamp ->
    #higher_level_preds:send_layer_preds ->
    sender:principal ->
    receiver:principal ->
    message:msg higher_level_preds.extended_higher_layer_gu i (join (readers [P sender]) (readers [P receiver])) ->
    LCrypto (sym_key_session_state_idx:nat & sym_key:C.bytes & message_idx:timestamp) (pki (send_preds higher_level_preds))
    (requires (fun t0 ->
      let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
      (i <= trace_len t0) /\
      send_predicates.request_pred i message
    ))
    (ensures (fun t0 (|_, sym_key, message_idx|) t1 ->
      (is_request_at_idx message message_idx sym_key) /\
      is_labeled higher_level_preds.extended_higher_layer_gu (trace_len t1) sym_key (join (readers [P sender]) (readers [P receiver]))
    ))

let initiator_send_request_pke_auth #i #higher_level_preds sender receiver message =
  let key_usages = higher_level_preds.extended_higher_layer_gu.higher_layer_gu.LabeledCryptoAPI.key_usages in
  let (|t0, sym_key|) = LabeledPKI.rand_gen #(send_preds higher_level_preds) (join (readers [P sender]) (readers [P receiver])) (C.aead_usage "AEAD.Symmetric_Send_Key") in
  assert(later_than t0 i);

  // The [message] can flow to the join label. To concatenate the symmetric key with the message, we
  // show that the key can also flow to the join label:
  assert(LCA.can_flow t0 (LCA.get_label key_usages sym_key) (readers [P sender]));
  assert(LCA.can_flow t0 (LCA.get_label key_usages sym_key) (readers [P receiver]));
  LabeledCryptoAPI.can_flow_to_join_forall t0;
  assert(LCA.can_flow t0 (LCA.get_label key_usages sym_key) (join (readers [P sender]) (readers [P receiver])));

  let sym_key:msg higher_level_preds.extended_higher_layer_gu t0 (join (readers [P sender]) (readers [P receiver])) = sym_key in
  let final_message = concat sym_key message in

  rand_is_secret #higher_level_preds.extended_higher_layer_gu #t0 #(join (readers [P sender]) (readers [P receiver])) #(C.aead_usage "AEAD.Symmetric_Send_Key") sym_key;

  assert(LCA.can_flow i (LCA.get_label key_usages message) (LCA.get_label key_usages sym_key));

  let (|now, auth_conf_message|) = create_auth_conf_message_for_request_pke #t0 #higher_level_preds sender receiver final_message in

  let send_idx = LabeledPKI.send #(send_preds higher_level_preds) #now sender receiver auth_conf_message in

  // store (send_idx, key) to the state of [sender]
  let connection_info_session = CommunicationState send_idx sym_key receiver in
  let new_si = LabeledPKI.new_session_number #(send_preds higher_level_preds) sender in
 
  let serialized_connection_info_session = serialize_session_st connection_info_session in

  let t_now = GlobalRuntimeLib.global_timestamp () in

  assert(valid_session higher_level_preds t_now sender new_si 0 connection_info_session);

  assert(later_than t_now i);

  serialized_session_st_flows_to_principal_state_session higher_level_preds (send_preds higher_level_preds).LabeledRuntimeAPI.global_usage t_now sender new_si 0 connection_info_session;

  assert(is_msg higher_level_preds.extended_higher_layer_gu t_now serialized_connection_info_session (readers [V sender new_si 0]));

  LabeledPKI.new_session #(send_preds higher_level_preds) #t_now sender new_si 0 serialized_connection_info_session;

  (match split auth_conf_message with 
  | Error _ -> assert (False)
  | Success (acm', tag) ->
    C.concat_split_lemma auth_conf_message;
    assert (auth_conf_message = C.concat acm' tag); 
    (match C.split acm' with 
    | Error _ -> assert (False) | Success (sender_bytes, r_ct) -> C.concat_split_lemma acm';
      (match C.split r_ct with
      | Error e -> assert (False)
      | Success (receiver_bytes, conf_message) -> C.concat_split_lemma r_ct;
    	  assert (acm' = C.concat sender_bytes (C.concat receiver_bytes conf_message) /\
    		 is_confidential_message final_message conf_message /\
    		 auth_conf_message = C.concat (C.concat sender_bytes (C.concat receiver_bytes conf_message)) tag)))
      ); 
  assert(is_request_at_idx message send_idx sym_key);  

  (|new_si, sym_key, send_idx|)

(** The hybrid implementation for sending a request.
    This function implements a hybrid scheme, where only the symmetric key is encrypted asymmetrically,
    and where the payload is encrypted symmetrically with the symmetric key.
*)

val initiator_send_request_pke_aead:
    #i:timestamp ->
    #higher_level_preds:send_layer_preds ->
    sender:principal ->
    receiver:principal ->
    message:msg higher_level_preds.extended_higher_layer_gu i (join (readers [P sender]) (readers [P receiver])) ->
    LCrypto (sym_key_session_state_idx:nat & sym_key:C.bytes & message_idx:timestamp) (pki (send_preds higher_level_preds))
    (requires (fun t0 ->
      let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
      (i <= trace_len t0) /\
      send_predicates.request_pred i message
    ))
    (ensures (fun t0 (|_, sym_key, message_idx|) t1 ->
      (is_request_at_idx message message_idx sym_key) /\
      is_aead_key (higher_level_preds.extended_higher_layer_gu) (trace_len t1) sym_key (join (readers [P sender]) (readers [P receiver])) "AEAD.Symmetric_Send_Key"
    ))
#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let initiator_send_request_pke_aead #i #higher_level_preds sender receiver message =
  let gu = higher_level_preds.extended_higher_layer_gu in
  let (|t0, sym_key|) = LabeledPKI.rand_gen #(send_preds higher_level_preds) (join (readers [P sender]) (readers [P receiver])) (C.aead_usage "AEAD.Symmetric_Send_Key") in
  assert(was_rand_generated_at t0 sym_key (join (readers [P sender]) (readers [P receiver])) (C.aead_usage "AEAD.Symmetric_Send_Key"));

  assert(later_than t0 i);

  let sym_key:msg gu t0 (join (readers [P sender]) (readers [P receiver])) = sym_key in

  assert(was_rand_generated_at t0 sym_key (join (readers [P sender]) (readers [P receiver])) (C.aead_usage "AEAD.Symmetric_Send_Key"));

  let now = GlobalRuntimeLib.global_timestamp() in

  let pub_enc_key = LabeledPKI.get_public_key #(send_preds higher_level_preds) #now sender receiver PKE "SEND_LAYER_CONF_REQUEST_HYBRID" in

  assert(was_rand_generated_at t0 sym_key (join (readers [P sender]) (readers [P receiver])) (C.aead_usage "AEAD.Symmetric_Send_Key"));
  assert(was_rand_generated_before now sym_key (join (readers [P sender]) (readers [P receiver])) (C.aead_usage "AEAD.Symmetric_Send_Key"));

  let (|t1,rand|) = rand_gen #(send_preds higher_level_preds) (join (readers [P sender]) (readers [P receiver])) (C.nonce_usage "PKE_NONCE") in

  sk_label_lemma gu now pub_enc_key (readers [P receiver]);

  assert(was_rand_generated_before now sym_key (join (readers [P sender]) (readers [P receiver])) (C.aead_usage "AEAD.Symmetric_Send_Key"));

  assert(later_than t1 now);

  assert(public_key_enc_pred higher_level_preds.extended_higher_layer_gu t1 "SEND_LAYER_CONF_REQUEST_HYBRID" pub_enc_key sym_key);

  // [pke_enc] requires the label of the message to flow to the receiver
  assert(is_msg gu t1 sym_key (join (readers [P sender]) (readers [P receiver])));
  assert(LCA.can_flow t1 (LCA.get_label gu.higher_layer_gu.LabeledCryptoAPI.key_usages sym_key) (join (readers [P sender]) (readers [P receiver])));

  LabeledCryptoAPI.can_flow_from_join t1 (readers [P sender]) (readers [P receiver]);
  assert(LCA.can_flow t1 (LCA.get_label gu.higher_layer_gu.key_usages sym_key) (readers [P receiver]));
  assert(is_msg gu t1 sym_key (readers [P receiver]));

  let encrypted_sym_key = LabeledCryptoAPI.pke_enc #(send_preds_global_usage gu) #t1 #(join (readers [P sender]) (readers [P receiver])) pub_enc_key rand sym_key in

  let (|t0, iv|) = LabeledPKI.rand_gen #(send_preds higher_level_preds) public (C.nonce_usage "AEAD.iv") in

  let now = GlobalRuntimeLib.global_timestamp() in

  let ad = (LabeledCryptoAPI.string_to_bytes #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now "") in

  let (message_tag:msg gu now (join (readers [P sender]) (readers [P receiver])))  = LabeledCryptoAPI.string_to_bytes #(send_preds_global_usage gu) #now "Send.Layer.Request" in

  let message = concat message_tag message in

  assert(aead_pred higher_level_preds.extended_higher_layer_gu now "AEAD.Symmetric_Send_Key" sym_key message ad);

  let encrypted_message:msg higher_level_preds.extended_higher_layer_gu now public = LabeledCryptoAPI.aead_enc #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #(join (readers [P sender]) (readers [P receiver])) sym_key iv message ad in

  let encrypted_sym_key:msg higher_level_preds.extended_higher_layer_gu now public = encrypted_sym_key in

  assert(later_than now t1);
  let final_message = concat encrypted_sym_key (concat iv encrypted_message) in

  let send_idx = LabeledPKI.send #(send_preds higher_level_preds) #now sender receiver final_message in

  // store (send_idx, key) to the state of [sender]

  let connection_info_session = CommunicationState send_idx sym_key receiver in
  let new_si = LabeledPKI.new_session_number #(send_preds higher_level_preds) sender in

  let serialized_connection_info_session = serialize_session_st connection_info_session in

  let t_now = GlobalRuntimeLib.global_timestamp () in

  assert(valid_session higher_level_preds t_now sender new_si 0 connection_info_session);

  assert(later_than t_now i);

  serialized_session_st_flows_to_principal_state_session higher_level_preds (send_preds higher_level_preds).LabeledRuntimeAPI.global_usage t_now sender new_si 0 connection_info_session;

  assert(is_msg higher_level_preds.extended_higher_layer_gu  t_now serialized_connection_info_session (readers [V sender new_si 0]));

  LabeledPKI.new_session #(send_preds higher_level_preds) #t_now sender new_si 0 serialized_connection_info_session;

  (|new_si, sym_key, send_idx|)
#pop-options




let initiator_send_request =
  if pke_only 
    then initiator_send_request_pke
    else initiator_send_request_pke_aead




val responder_receive_request_pke:
    #i:timestamp ->
    #higher_level_preds:send_layer_preds ->
    index_of_send_event_of_request:timestamp ->
    receiver:principal ->
    LCrypto (now:timestamp & sender:principal & sym_key:C.bytes & msg:msg higher_level_preds.extended_higher_layer_gu now (readers [P receiver])) (pki (send_preds higher_level_preds))
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,sender,sym_key,msg|) t1 ->
      let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
      t0 == t1 /\
      now = trace_len t0 /\
      (index_of_send_event_of_request < trace_len t0) /\
      (is_request_at_idx msg index_of_send_event_of_request sym_key) /\
      (
       (
         (is_publishable higher_level_preds.extended_higher_layer_gu now msg /\
         is_publishable higher_level_preds.extended_higher_layer_gu now sym_key) \/
         (
            (exists (real_sender:principal). is_aead_key higher_level_preds.extended_higher_layer_gu now sym_key (join (readers [P real_sender]) (readers [P receiver])) "AEAD.Symmetric_Send_Key") /\
            (exists j. later_than now j /\ send_predicates.request_pred j msg)
         )
       ) /\
       ( LCA.can_flow now (LCA.get_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).key_usages msg) (LCA.get_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).key_usages sym_key) // follows from the type of the result of [aead_dec]
       )
      )
    ))


val responder_receive_request_hybrid_pke_aead:
    #i:timestamp ->
    #higher_level_preds:send_layer_preds ->
    index_of_send_event_of_request:timestamp ->
    receiver:principal ->
    LCrypto (now:timestamp & sender:principal & sym_key:C.bytes & msg:msg higher_level_preds.extended_higher_layer_gu now (readers [P receiver])) (pki (send_preds higher_level_preds))
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,sender,sym_key,msg|) t1 ->
      let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
      t0 == t1 /\
      now = trace_len t0 /\
      (index_of_send_event_of_request < trace_len t0) /\
      (is_request_at_idx msg index_of_send_event_of_request sym_key) /\
      (
       (
         (is_publishable higher_level_preds.extended_higher_layer_gu now msg /\
         is_publishable higher_level_preds.extended_higher_layer_gu now sym_key) \/
         (
            (exists (real_sender:principal). is_aead_key higher_level_preds.extended_higher_layer_gu now sym_key (join (readers [P real_sender]) (readers [P receiver])) "AEAD.Symmetric_Send_Key") /\
            (exists j. later_than now j /\ send_predicates.request_pred j msg)
         )
       ) /\
       ( LCA.can_flow now (LCA.get_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).key_usages msg) (LCA.get_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).key_usages sym_key) // follows from the type of the result of [aead_dec]
       )
      )
    ))


#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let responder_receive_request_pke #i #higher_level_preds index_of_send_event_of_request receiver =
  
  let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
  let gu = higher_level_preds.extended_higher_layer_gu in

  let t0 = GlobalRuntimeLib.global_timestamp () in
  let (|now,claimed_sender,m |) = LabeledPKI.receive_i #(send_preds higher_level_preds) index_of_send_event_of_request receiver in

  let plaintext = process_conf_request_message_pke #now #higher_level_preds receiver m in
  match split plaintext with
  | Error _ -> error "Incorrect request format."
  | Success (sym_key, payload) -> (

     splittable_term_publishable_implies_components_publishable_forall gu;

     C.split_based_on_split_len_prefixed_lemma plaintext;

     assert(forall i. (C.is_succ2 (C.split_len_prefixed 4 plaintext) sym_key payload /\ is_publishable gu i plaintext) ==>
              (is_publishable gu i sym_key /\ is_publishable gu i payload));


     assert(
        is_publishable gu now plaintext \/
        (
          (exists (p1 p2:principal). was_rand_generated_before now sym_key (join (readers [P p1]) (readers [P p2])) (C.aead_usage "AEAD.Symmetric_Send_Key")) /\
          (exists j. later_than now j /\ send_predicates.request_pred j payload)
        )
      );

     assert(
       is_publishable gu now plaintext ==>
       (is_publishable gu now payload /\
       is_publishable gu now sym_key));

     assert(
        (is_publishable gu now payload /\
        is_publishable gu now sym_key) \/
        (
          (exists (p1 p2:principal). was_rand_generated_before now sym_key (join (readers [P p1]) (readers [P p2])) (C.aead_usage "AEAD.Symmetric_Send_Key")) /\
          (exists j. later_than now j /\ send_predicates.request_pred j payload)
        )
      );

     rand_is_secret_forall_labels #gu #now #(C.aead_usage "AEAD.Symmetric_Send_Key") sym_key;

     assert(
        (is_publishable gu now payload /\
        is_publishable gu now sym_key) \/
        (
          (exists (real_sender real_receiver:principal). is_aead_key gu now sym_key (join (readers [P real_sender]) (readers [P real_receiver])) "AEAD.Symmetric_Send_Key") /\
          (exists j. later_than now j /\ send_predicates.request_pred j payload)
        )
      );

       let sym_key_label = LCA.get_label (send_preds_global_usage gu).LabeledCryptoAPI.key_usages sym_key in

       //the symmetric key can flow to the receiver; thus, if the key is an aead key, one of
       //the principals in the join label is the receiver
       assert(LCA.can_flow now sym_key_label (readers [P receiver]));

       LabeledCryptoAPI.can_flow_to_join_and_principal_and_unpublishable_property now;

     assert(
        (is_publishable gu now payload /\
        is_publishable gu now sym_key) \/
        (
          (exists (real_sender:principal). is_aead_key gu now sym_key (join (readers [P real_sender]) (readers [P receiver])) "AEAD.Symmetric_Send_Key") /\
          (exists j. later_than now j /\ send_predicates.request_pred j payload)
        )
      );

     C.concat_split_lemma plaintext;
     assert(plaintext == concat sym_key payload);
     assert(is_request_at_idx payload index_of_send_event_of_request sym_key);
     (|now, claimed_sender, sym_key, payload|)
  )
#pop-options


#push-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0"
let responder_receive_request_hybrid_pke_aead #i #higher_level_preds index_of_send_event_of_request receiver =
  let t0 = GlobalRuntimeLib.global_timestamp () in
  let gu = higher_level_preds.extended_higher_layer_gu in
  let lca_gu = send_preds_global_usage gu in
  let (|now,claimed_sender,m |) = LabeledPKI.receive_i #(send_preds higher_level_preds) index_of_send_event_of_request receiver in
  match split m with
  | Error _ -> error "[responder_receive_request_hybrid_pke_aead]: wrong message format"
  | Success (encrypted_sym_key, iv_and_encrypted_payload) -> (
    let (|si, priv_pk_key|) = LabeledPKI.get_private_key #(send_preds higher_level_preds) #now receiver PKE "SEND_LAYER_CONF_REQUEST_HYBRID" in
    match LabeledCryptoAPI.pke_dec #lca_gu #now #(readers [P receiver]) priv_pk_key encrypted_sym_key with
    | Error _ -> error "[responder_receive_request_hybrid_pke_aead]: can't decrypt the symmetric key"
    | Success sym_key ->(

            assert( // follows from pke_dec
              is_publishable gu now sym_key \/
              public_key_enc_pred higher_level_preds.extended_higher_layer_gu now "SEND_LAYER_CONF_REQUEST_HYBRID"  (C.pk priv_pk_key) sym_key
            );

            assert(
              is_publishable gu now sym_key \/
              (exists (some_sender receiver_string:string). (was_rand_generated_before now sym_key (join (readers [P some_sender]) (readers [P receiver_string])) (C.aead_usage "AEAD.Symmetric_Send_Key")))
            );

           splittable_term_publishable_implies_components_publishable_forall gu;

           // The symmetric key is publishable (created by the attacker), or labeled with some sender, and the receiver.
           assert(
             is_publishable gu now sym_key \/
             (exists (some_sender receiver_string:string). (was_rand_generated_before now sym_key (join (readers [P some_sender]) (readers [P receiver_string])) (C.aead_usage "AEAD.Symmetric_Send_Key")))
           );

           //next: split up the iv and the encrypted payload and decrypt using the symmetric key:
           match split iv_and_encrypted_payload with
           | Error _ -> error "[responder_receive_request_hybrid_pke_aead]: second part of the message has wrong format"
           | Success (iv, encrypted_payload) -> (
             let now = GlobalRuntimeLib.global_timestamp() in
             let ad = (LabeledCryptoAPI.string_to_bytes #lca_gu #now "") in
             assert(
               is_publishable gu now sym_key \/
               (exists (some_sender receiver_string:string). (was_rand_generated_before now sym_key (join (readers [P some_sender]) (readers [P receiver_string])) (C.aead_usage "AEAD.Symmetric_Send_Key")))
             );

             rand_is_secret_forall_labels #gu #now #(C.aead_usage "AEAD.Symmetric_Send_Key") sym_key;

             assert(
               is_publishable gu now sym_key \/
               (exists (some_sender receiver_string:principal). is_aead_key gu now sym_key (join (readers [P some_sender]) (readers [P receiver_string])) "AEAD.Symmetric_Send_Key")
             );

             let sym_key_label = LCA.get_label lca_gu.LabeledCryptoAPI.key_usages sym_key in

             //the symmetric key can flow to the receiver; thus, if the key is an aead key, one of
             //the principals in the join label is the receiver
             assert(LCA.can_flow now sym_key_label (readers [P receiver]));

             LabeledCryptoAPI.can_flow_to_join_and_principal_and_unpublishable_property now;

             assert(
              (
               (~(is_publishable gu now sym_key)) /\
               (LCA.can_flow now sym_key_label (readers [P receiver])) /\
               (exists (some_sender some_receiver:principal). is_labeled gu now sym_key (join (readers [P some_sender]) (readers [P some_receiver])))
              )
               ==>
               (exists (some_sender:principal). is_labeled gu now sym_key (join (readers [P some_sender]) (readers [P receiver])))
             );
             assert(
               is_publishable gu now sym_key \/
               (exists (some_sender:principal). is_aead_key gu now sym_key (join (readers [P some_sender]) (readers [P receiver])) "AEAD.Symmetric_Send_Key")
             );

             match LabeledCryptoAPI.aead_dec #lca_gu #now #sym_key_label  sym_key iv encrypted_payload ad with
             | Error _ -> error "[responder_receive_request_hybrid_pke_aead]: can't decrypt payload"
             | Success (msg_tag_and_plaintext_payload: msg gu now sym_key_label) -> (
               match split msg_tag_and_plaintext_payload with
               | Error _ -> error "[responder_receive_request_hybrid_pke_aead]: plaintext has wrong format"
               | Success (msg_tag_bytes, plaintext_payload) -> (
                 match bytes_to_string msg_tag_bytes with
                 | Error _ -> error "[responder_receive_request_hybrid_pke_aead]: message tag can not be read"
                 | Success msg_tag -> (
                   if msg_tag = "Send.Layer.Request" then (
                     assert(exists (some_sender:principal). LCA.can_flow now sym_key_label (join (readers [P some_sender]) (readers [P receiver])));

                     assert(exists sender' receiver full_request.
                       was_message_sent_at index_of_send_event_of_request sender' receiver full_request);

                     C.concat_split_lemma m;
                     C.concat_split_lemma iv_and_encrypted_payload;
                     C.concat_split_lemma msg_tag_and_plaintext_payload;
                     C.aead_dec_lemma sym_key iv msg_tag_and_plaintext_payload ad;
                     LabeledCryptoAPI.aead_dec_lemma #lca_gu #now #sym_key_label sym_key iv encrypted_payload ad;
                     let msg_tag_and_plaintext_payload_bytes:C.bytes = msg_tag_and_plaintext_payload in
                     assert(Success msg_tag_and_plaintext_payload_bytes == C.aead_dec sym_key iv encrypted_payload ad);
                     assert(LCA.aead_enc #lca_gu #now #sym_key_label sym_key iv msg_tag_and_plaintext_payload ad == C.aead_enc sym_key iv msg_tag_and_plaintext_payload ad);

                     C.aead_dec_lemma sym_key iv encrypted_payload ad;
                     assert(
                       match C.aead_dec sym_key iv encrypted_payload ad with
                       | Error _ -> True
                       | Success plaintext ->
                         encrypted_payload == C.aead_enc sym_key iv plaintext ad
                     );

                     assert(exists sender' receiver.
                       was_message_sent_at index_of_send_event_of_request sender' receiver m /\
                       m = concat encrypted_sym_key (concat iv encrypted_payload) /\
                       encrypted_payload = C.aead_enc sym_key iv msg_tag_and_plaintext_payload ad
                       );


                     //needed for showing [is_request_at]
                     C.pke_dec_lemma priv_pk_key encrypted_sym_key;

                     assert(exists rand pub_enc_key.
                       encrypted_sym_key == C.pke_enc pub_enc_key rand sym_key
                     );

                     assert(is_request_at_idx plaintext_payload index_of_send_event_of_request sym_key);

                     (| now, claimed_sender, sym_key, plaintext_payload |)
                   ) else error "[responder_receive_request_hybrid_pke_aead]: wrong message tag"
                 )
               )
             )
           )
 )
 )
#pop-options

val responder_receive_request_pke_auth:
    #i:timestamp ->
    #higher_level_preds:send_layer_preds ->
    index_of_send_event_of_request:timestamp ->
    receiver:principal ->
    LCrypto (now:timestamp & sender:principal & sym_key:C.bytes & msg:msg higher_level_preds.extended_higher_layer_gu now (readers [P receiver])) (pki (send_preds higher_level_preds))
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,sender,sym_key,msg|) t1 ->
      let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
      let ku = ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).key_usages in 
      t0 == t1 /\
      now = trace_len t0 /\
      (index_of_send_event_of_request < trace_len t0) /\ 
      (is_request_at_idx msg index_of_send_event_of_request sym_key) /\
      (
       (LabeledCryptoAPI.corrupt_id now (P sender) \/
         (is_publishable higher_level_preds.extended_higher_layer_gu now msg /\
         is_publishable higher_level_preds.extended_higher_layer_gu now sym_key) \/
         (
            (is_aead_key higher_level_preds.extended_higher_layer_gu now sym_key (join (readers [P sender]) (readers [P receiver])) "AEAD.Symmetric_Send_Key") /\
            (exists j. later_than now j /\ send_predicates.request_pred j msg) /\ 
	    LCA.can_flow now (LCA.get_label ku msg) (LCA.get_label ku sym_key)
         )
       ) 
      )
    ))

#push-options "--z3rlimit 50"
let responder_receive_request_pke_auth #i #higher_level_preds index_of_send_event_of_request receiver =
  let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
  let gu = higher_level_preds.extended_higher_layer_gu in

  let t0 = GlobalRuntimeLib.global_timestamp () in
  let (|now,sender,m |) = LabeledPKI.receive_i #(send_preds higher_level_preds) index_of_send_event_of_request receiver in

  let plaintext = process_auth_conf_request_message_pke #now #higher_level_preds sender receiver m in
  match split plaintext with
  | Error _ -> error "Incorrect request format."
  | Success (sym_key, payload) -> (

     splittable_term_publishable_implies_components_publishable_forall gu;

     C.split_based_on_split_len_prefixed_lemma plaintext;

     assert(forall i. (C.is_succ2 (C.split_len_prefixed 4 plaintext) sym_key payload /\ is_publishable gu i plaintext) ==>
              (is_publishable gu i sym_key /\ is_publishable gu i payload));


     assert(
        LabeledCryptoAPI.corrupt_id now (P sender) \/
        is_publishable gu now plaintext \/
        (
          (was_rand_generated_before now sym_key (join (readers [P sender]) (readers [P receiver])) (C.aead_usage "AEAD.Symmetric_Send_Key")) /\
          (exists j. later_than now j /\ send_predicates.request_pred j payload)
        )
      );
      
     assert(
       is_publishable gu now plaintext ==>
       (is_publishable gu now payload /\
       is_publishable gu now sym_key));

     assert(
       LabeledCryptoAPI.corrupt_id now (P sender) \/
        (is_publishable gu now payload /\
        is_publishable gu now sym_key) \/
        (
          (was_rand_generated_before now sym_key (join (readers [P sender]) (readers [P receiver])) (C.aead_usage "AEAD.Symmetric_Send_Key")) /\
          (exists j. later_than now j /\ send_predicates.request_pred j payload)
        )
      );

     rand_is_secret_forall_labels #gu #now #(C.aead_usage "AEAD.Symmetric_Send_Key") sym_key;

     assert(
       LabeledCryptoAPI.corrupt_id now (P sender) \/
        (is_publishable gu now payload /\
        is_publishable gu now sym_key) \/
        (
          (is_aead_key gu now sym_key (join (readers [P sender]) (readers [P receiver])) "AEAD.Symmetric_Send_Key") /\
          (exists j. later_than now j /\ send_predicates.request_pred j payload)
        )
      );

     (match split m with 
     | Error _ -> assert (False)
     | Success (acm', tag) ->
       C.concat_split_lemma m;
       assert (m = C.concat acm' tag); 
       (match C.split acm' with 
       | Error _ -> assert (False) | Success (sender_bytes, r_ct) -> C.concat_split_lemma acm';
	 (match C.split r_ct with
	 | Error e -> assert (False)
	 | Success (receiver_bytes, conf_message) -> C.concat_split_lemma r_ct;
    		   assert (acm' = C.concat sender_bytes (C.concat receiver_bytes conf_message) /\
    			  is_confidential_message plaintext conf_message /\
    			  m = C.concat (C.concat sender_bytes (C.concat receiver_bytes conf_message)) tag)))
	 ); 
     C.concat_split_lemma plaintext;
     assert(plaintext == concat sym_key payload);
     assert(is_request_at_idx payload index_of_send_event_of_request sym_key); 
     (|now, sender, sym_key, payload|)
  )
#pop-options

let responder_receive_request =
  if pke_only 
    then responder_receive_request_pke
    else responder_receive_request_hybrid_pke_aead

let initiator_send_authn_request =
    initiator_send_request_pke_auth

let responder_receive_authn_request =
    responder_receive_request_pke_auth

let responder_send_response #i #l #higher_level_preds initiator responder sym_key send_idx_of_request request message =
  let gu = higher_level_preds.extended_higher_layer_gu in
  let lca_gu = send_preds_global_usage gu in
  let now = GlobalRuntimeLib.global_timestamp() in

  let msg_tag:msg gu now l = LabeledCryptoAPI.string_to_bytes #lca_gu #now "Send.Layer.Response" in
  let message_with_request_idx = LabeledCryptoAPI.concat (LabeledCryptoAPI.nat_to_bytes #lca_gu #i 0 send_idx_of_request) message in

  assert(later_than now i);

  let plaintext = LabeledCryptoAPI.concat msg_tag message_with_request_idx in

  let (|now, iv|) = LabeledPKI.rand_gen #(send_preds higher_level_preds) public (C.nonce_usage "AEAD.iv") in

  let ad = (LabeledCryptoAPI.string_to_bytes #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now "") in

  assert(is_publishable gu now sym_key \/ (exists s. is_aead_key gu now sym_key l s));
  assert(is_publishable gu now sym_key \/ (aead_pred higher_level_preds.extended_higher_layer_gu now "AEAD.Symmetric_Send_Key" sym_key plaintext ad));

  assert(is_publishable gu now sym_key ==> (forall (s:string). aead_pred higher_level_preds.extended_higher_layer_gu now s sym_key plaintext ad));
  assert(is_aead_key gu now sym_key l "AEAD.Symmetric_Send_Key" ==> (aead_pred higher_level_preds.extended_higher_layer_gu now "AEAD.Symmetric_Send_Key" sym_key plaintext ad));

  let encrypted_response:msg gu now public =
      LabeledCryptoAPI.aead_enc #lca_gu #now #l sym_key iv plaintext ad in

  let final_message = concat iv encrypted_response in
  let send_idx = LabeledPKI.send #(send_preds higher_level_preds) #now responder initiator final_message in
  send_idx


let initiator_receive_response #higher_level_preds sym_key_state_session_idx index_of_send_event_of_response initiator =

  let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
  let gu = higher_level_preds.extended_higher_layer_gu in
  let lca_gu = send_preds_global_usage gu in

  let now = GlobalRuntimeLib.global_timestamp () in
  let (|vi , sym_key_session_state|) = LabeledPKI.get_session #(send_preds higher_level_preds) #now initiator sym_key_state_session_idx in

  match Communication.Sessions.parse_session_st sym_key_session_state with
  | Error _ -> error "[initiator_receive_response]: can't parse session state of symmetric key"
  | Success parsed_session_st -> (
    assert(valid_session higher_level_preds now initiator sym_key_state_session_idx vi parsed_session_st);
    match parsed_session_st with
    | (CommunicationState request_send_idx sym_key responder_stored_with_sym_key) -> (
      assert(was_rand_generated_before now sym_key (join (readers [P initiator]) (readers [P responder_stored_with_sym_key])) (C.aead_usage "AEAD.Symmetric_Send_Key"));

      let (|now, claimed_responder, iv_and_encrypted_response |) = LabeledPKI.receive_i #(send_preds higher_level_preds) index_of_send_event_of_response initiator in

           match split iv_and_encrypted_response with
           | Error _ -> error "[initiator_receive_response]: received message has wrong format"
           | Success (iv, encrypted_response) -> (
             let ad = (LabeledCryptoAPI.string_to_bytes #lca_gu #now "") in
             rand_is_secret #gu #now #(join (readers [P initiator]) (readers [P responder_stored_with_sym_key])) #(C.aead_usage "AEAD.Symmetric_Send_Key") sym_key;
             assert(
               is_publishable gu now sym_key \/
               is_aead_key gu now sym_key (join (readers [P initiator]) (readers [P responder_stored_with_sym_key])) "AEAD.Symmetric_Send_Key"
             );

             match LabeledCryptoAPI.aead_dec #lca_gu #now #(join (readers [P initiator]) (readers [P responder_stored_with_sym_key])) sym_key iv encrypted_response ad with
             | Error _ -> error "[initiator_receive_response]: can't decrypt the payload"
             | Success (msg_tag_and_plaintext_payload: msg gu now (join (readers [P initiator]) (readers [P responder_stored_with_sym_key]))) -> (
               match split msg_tag_and_plaintext_payload with
               | Error _ -> error "[initiator_receive_response]: plaintext has wrong format"
               | Success (msg_tag_bytes, request_send_idx_and_plaintext_response) -> (
                 match bytes_to_string msg_tag_bytes with
                 | Error _ -> error "[initiator_receive_response]: can't parse message tag"
                 | Success msg_tag -> (
                   if msg_tag = "Send.Layer.Response" then (
                      match split request_send_idx_and_plaintext_response with
                      | Error _ -> error "[initiator_receive_response]: payload has wrong format"
                      | Success (request_idx_bytes, plaintext_response) -> (
                        match bytes_to_nat request_idx_bytes with
                        | Error _ -> error "[initiator_receive_response]: can't parse request index"
                        | Success request_idx -> (

		          assert(is_publishable gu now sym_key \/
		          (exists s. is_aead_key gu now sym_key (join (readers [P initiator]) (readers [P responder_stored_with_sym_key])) s /\
                          aead_pred higher_level_preds.extended_higher_layer_gu now s sym_key
		          msg_tag_and_plaintext_payload ad));

		          assert(LCA.can_flow now (join (readers [P initiator]) (readers [P responder_stored_with_sym_key])) public \/
		          (exists s. is_aead_key gu now sym_key (join (readers [P initiator]) (readers [P responder_stored_with_sym_key])) s /\
                          aead_pred higher_level_preds.extended_higher_layer_gu now s sym_key
		          msg_tag_and_plaintext_payload ad));

		          assert(LCA.can_flow now (join (readers [P initiator]) (readers [P responder_stored_with_sym_key])) public \/
		          (aead_pred higher_level_preds.extended_higher_layer_gu now "AEAD.Symmetric_Send_Key" sym_key msg_tag_and_plaintext_payload ad));

		          assert(LCA.can_flow now (join (readers [P initiator]) (readers [P responder_stored_with_sym_key])) public \/
                            ( msg_tag = "Send.Layer.Response" /\
                              (
                              match split request_send_idx_and_plaintext_response with
                              | Success (request_send_idx_bytes, response) -> (
                                match bytes_to_nat request_send_idx_bytes with
                                | Success request_send_idx -> exists j request sym_key. j<=now /\
                                  send_predicates.response_pred j response request sym_key /\ is_request_at_idx request request_send_idx sym_key
                                )
                              )
                          ));

		        assert(LCA.can_flow now (join (readers [P initiator]) (readers [P responder_stored_with_sym_key])) public \/
                            (
                            match split request_send_idx_and_plaintext_response with
                            | Success (request_send_idx_bytes, response) -> (
                              request_send_idx_bytes == request_idx_bytes /\
                              response == plaintext_response /\
                              (
                              match bytes_to_nat request_idx_bytes with
                              | Success request_send_idx -> exists j request sym_key. j<=now /\ send_predicates.response_pred j response request sym_key /\ is_request_at_idx request request_send_idx sym_key
                              )
                              )
                            )
                        );


		        assert(LCA.can_flow now (join (readers [P initiator]) (readers [P responder_stored_with_sym_key])) public \/
                          (
                            match bytes_to_nat request_idx_bytes with
                            | Success request_send_idx -> exists j request sym_key. j<=now /\ send_predicates.response_pred j plaintext_response request sym_key /\ is_request_at_idx request request_send_idx sym_key
                        ));


                     assert(LCA.can_flow now (join (readers [P initiator]) (readers [P responder_stored_with_sym_key])) public \/
                       (exists j request sym_key. later_than now j /\ send_predicates.response_pred j plaintext_response request sym_key /\ is_request_at_idx request request_idx sym_key)
                     );

                     LabeledCryptoAPI.can_flow_join_labels_public_lemma now (readers [P initiator]) (readers [P responder_stored_with_sym_key]);
                     assert(LCA.can_flow now (join (readers [P initiator]) (readers [P responder_stored_with_sym_key])) public ==>
                     (
                       LCA.can_flow now (readers [(P initiator)]) public \/
                       LCA.can_flow now (readers [(P responder_stored_with_sym_key)]) public
                     )
                     );
                     assert(LCA.can_flow now (join (readers [P initiator]) (readers [P responder_stored_with_sym_key])) public ==>
                     (
                       LCA.corrupt_id now (P initiator) \/
                       LCA.corrupt_id now (P responder_stored_with_sym_key)
                     )
                     );

                     assert(
                     (LCA.corrupt_id now (P initiator) \/ LCA.corrupt_id now (P responder_stored_with_sym_key)) \/
                       (exists j request sym_key. later_than now j /\ send_predicates.response_pred j plaintext_response request sym_key /\ is_request_at_idx request request_idx sym_key)
                     );


                     LabeledCryptoAPI.can_flow_from_join now (readers [P initiator]) (readers [P responder_stored_with_sym_key]);
                     let plaintext_response:msg gu now (readers [(P initiator)]) = plaintext_response in

                     assert(is_msg gu now plaintext_response (readers [P responder_stored_with_sym_key]));

                     (| now, responder_stored_with_sym_key, plaintext_response, request_idx |)
                     )
                     )
                   ) else error "[initiator_receive_response]: wrong message tag"
                 )
               )
             )
           )
  )
    | _ -> error "[initiator_receive_response]: session at sym_key_session_state_idx is not a session for a symmetric key"
  )


#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let new_session #pr #i p si vi ss =
  let sst = Communication.Sessions.serialize_session_st (APP ss) in
  assert(valid_session pr i p si vi (APP ss));
  serialized_session_st_is_msg pr.extended_higher_layer_gu i (readers [V p si vi]) ss;
  assert(session_st_inv pr (send_preds_global_usage pr.extended_higher_layer_gu) i p si vi sst);
  assert((send_preds pr).LabeledRuntimeAPI.trace_preds.LabeledRuntimeAPI.session_st_inv i p si vi sst);
  LabeledPKI.new_session #(send_preds pr) #i p si vi sst
#pop-options


let update_session #pr #i p si vi ss =
  let sst = Communication.Sessions.serialize_session_st (APP ss) in
  serialized_session_st_is_msg pr.extended_higher_layer_gu i (readers [V p si vi]) ss;
  LabeledPKI.update_session #(send_preds pr) #i p si vi sst


#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let get_session #pr #i p si =
  let (|vi,s|) = LabeledPKI.get_session #((send_preds pr)) #i p si in
  match parse_session_st s with
  | Success (APP s') ->
    assert (valid_session pr  i p si vi (APP s'));
       parsed_app_session_st_is_msg pr.extended_higher_layer_gu i (readers [V p si vi]) s;
    (|vi,s'|)
  | _ -> error "not an application state"
#pop-options

#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let find_session #pr #i p f =
  let f' si vi st =
    match parse_session_st st with
    | Success (APP s) -> f si vi s
    | _ -> false in
  match LabeledPKI.find_session #(send_preds pr) #i p f' with
  | None -> None
  | Some (|si,vi,st|) -> (
    (match parse_session_st st with
     | Success (APP s') ->
       assert (valid_session pr i p si vi (APP s'));
       assert(is_msg pr.extended_higher_layer_gu i st (readers [V p si vi]));
       parsed_app_session_st_is_msg pr.extended_higher_layer_gu i (readers [V p si vi]) st;
       assert(is_msg pr.extended_higher_layer_gu i s' (readers [V p si vi]));
       Some (|si,vi,s'|)
     | _ -> error "not an application state")
)
#pop-options



let gen_send_keys #pr p =
  let preds = pr in
  let t0 = global_timestamp () in
  let conf = gen_private_key #preds #t0 p PKE "SEND_LAYER_CONF_SEND" in
  let t1 = global_timestamp () in
  let conf_authn_enc = gen_private_key #preds #t1 p PKE "SEND_LAYER_CONF_AUTHN_SEND" in
  let t2 = global_timestamp () in
  let conf_req_pke = gen_private_key #preds #t2 p PKE "SEND_LAYER_CONF_REQUEST_ONLY_PKE" in
  let t3 = global_timestamp () in
  let conf_req_hybrid = gen_private_key #preds #t3 p PKE "SEND_LAYER_CONF_REQUEST_HYBRID" in
  let t4 = global_timestamp () in
  let authn = gen_private_key #preds #t4 p SIG "SEND_LAYER_AUTHN_SEND" in
  let t5 = global_timestamp () in
  let conf_authn_sig = gen_private_key #preds #t5 p SIG "SEND_LAYER_CONF_AUTHN_SEND" in
  {
    conf_send_key = conf;
    conf_authn_send_key = conf_authn_enc;
    conf_req_pke_send_key = conf_req_pke;
    conf_req_hybrid_send_key = conf_req_hybrid;
    authn_send_key = authn;
    conf_authn_sig_send_key = conf_authn_sig;
  }


let install_send_public_keys #pr p peer =
  let preds = pr in
  let t0 = global_timestamp () in
  let conf = install_public_key #preds #t0 p peer PKE "SEND_LAYER_CONF_SEND" in
  let t1 = global_timestamp () in
  let conf_authn_enc = install_public_key #preds #t1 p peer PKE "SEND_LAYER_CONF_AUTHN_SEND" in
  let t2 = global_timestamp () in
  let conf_req_pke = install_public_key #preds #t2 p peer PKE "SEND_LAYER_CONF_REQUEST_ONLY_PKE" in
  let t3 = global_timestamp () in
  let conf_req_hybrid = install_public_key #preds #t3 p peer PKE "SEND_LAYER_CONF_REQUEST_HYBRID" in
  let t4 = global_timestamp () in
  let authn = install_public_key #preds #t4 p peer SIG "SEND_LAYER_AUTHN_SEND" in
  let t5 = global_timestamp () in
  let conf_authn_sig = install_public_key #preds #t5 p peer SIG "SEND_LAYER_CONF_AUTHN_SEND" in
  {
    conf_send_key = conf;
    conf_authn_send_key = conf_authn_enc;
    conf_req_pke_send_key = conf_req_pke;
    conf_req_hybrid_send_key = conf_req_hybrid;
    authn_send_key = authn;
    conf_authn_sig_send_key = conf_authn_sig;
  }



val distribute_send_keys_for:  #pr:send_layer_preds -> #len:nat -> (key_owner:principal) -> (principals:list principal{List.Tot.length principals = len}) ->
  LCrypto (list key_session_indices) (pki (send_preds pr))
  (requires fun t0 -> len >= 1)
  (ensures fun t0 r t1 -> trace_len t1 = trace_len t0 + (6 `op_Multiply` len))

let rec distribute_send_keys_for #pr #len key_owner principals =
  match principals with
  | [p] -> [install_send_public_keys #pr key_owner p]
  | hd::tl -> (install_send_public_keys #pr key_owner hd)::(distribute_send_keys_for #pr #(len-1) key_owner tl)


val generate_and_distribute_send_keys_int:
  #pr:send_layer_preds -> #len_all:nat -> #len:nat -> (all_principals:list principal{List.Tot.length all_principals = len_all}) -> (remaining:list principal{List.Tot.length remaining = len}) ->
  LCrypto (list key_session_indices) (pki (send_preds pr))
  (requires fun t0 -> len >= 1 /\ len_all >= 1)
  (ensures fun t0 r t1 -> (
    trace_len t1 =
      trace_len t0 +
      (12 `op_Multiply` len) +  // Generate keys
      ((6 `op_Multiply` len_all) `op_Multiply` len)  // Distribute keys to principals
  ))

let rec generate_and_distribute_send_keys_int #pr #len_all #len all_principals remaining =
  match remaining with
  | [p] -> (
    let t0 = global_timestamp () in
    let priv_key_indices = gen_send_keys #pr p in
    let t1 = global_timestamp () in
    assert(t1 = t0 + 12);
    let _ = distribute_send_keys_for #pr #len_all p all_principals in
    let t2 = global_timestamp () in
    assert(t2 = t1 + (6 `op_Multiply` len_all));
    [priv_key_indices]
  )
  | hd::tl -> (
    let priv_key_indices = gen_send_keys #pr hd in
    let _ = distribute_send_keys_for #pr #len_all hd all_principals in
    priv_key_indices::(generate_and_distribute_send_keys_int #pr #len_all #(len-1) all_principals tl)
  )

let generate_and_distribute_send_keys #pr #len principals =
  generate_and_distribute_send_keys_int #pr #len #len principals principals
