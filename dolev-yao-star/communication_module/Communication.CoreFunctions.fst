/// Communication.CoreFunctions (Implementation)
/// ============================================

module Communication.CoreFunctions

friend Communication.MessageStructurePredicates
friend Communication.UsagePredicates


let create_authn_message #i #higher_level_preds sender receiver message =
   let now = GlobalRuntimeLib.global_timestamp() in
   let gu = ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) in
   assert(later_than now i);
   assert(is_publishable ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now message);

   // 1. Get a signing key of the sender (using the LabeledPKI module)
   let (|sk_si, signing_key|) = get_private_key #(send_preds higher_level_preds) #now sender SIG "SEND_LAYER_AUTHN_SEND" in
   // 2. Create a nonce (for the tag generation)
   let (|t1,n_sig|) = rand_gen #(send_preds higher_level_preds) (readers [P sender]) (nonce_usage "SIG_NONCE") in

   let (verification_trace_idx_bytes:msg gu now public) = (nat_to_bytes #gu #now 4 i) in

   let msg_with_verification_trace_idx = concat verification_trace_idx_bytes message in

   assert(signature_pred higher_level_preds.extended_higher_layer_gu i "SEND_LAYER_AUTHN_SEND" (C. vk signing_key) msg_with_verification_trace_idx);
   assert(sign_pred ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).L.usage_preds now "SEND_LAYER_AUTHN_SEND" (C.vk signing_key) msg_with_verification_trace_idx);

   assert((exists (s: string). is_signing_key ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now signing_key (readers [P sender]) s) );
   assert(forall s. is_signing_key ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now signing_key (readers [P sender]) s ==>
     sign_pred ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).L.usage_preds now s (C.vk signing_key) msg_with_verification_trace_idx);


   // 3. Create the signature tag
   let tag = L.sign #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #(readers [P sender]) #public signing_key n_sig msg_with_verification_trace_idx in
   // 4. Create the final message by concatenating the original message with the tag
   let signed_msg = L.concat #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #public msg_with_verification_trace_idx tag in

   assert(LabeledCryptoAPI.can_flow now (get_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).L.key_usages signed_msg) (readers [P sender; P receiver]));

   assert(
     LabeledCryptoAPI.verify
      #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #public #public
       (LabeledCryptoAPI.vk #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #(readers [P sender]) signing_key) msg_with_verification_trace_idx tag);

   assert(is_publishable ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now signed_msg);
   assert(is_authenticated_message i message signed_msg);

   (|now, signed_msg|)


let process_authn_message #now #higher_level_preds sender receiver message_idx signed_message =
  // 1. Get a public verification key of the sender (using the LabeledPKI module)
  let verify_key_of_sender = LabeledPKI.get_public_key #(send_preds higher_level_preds) #now receiver sender SIG "SEND_LAYER_AUTHN_SEND" in
  // 2. Split the signed message into the original message and the signature tag
  match LabeledCryptoAPI.split signed_message with
  | Error e -> error ("[process_authn_message]: cannot split the message into message and tag: " ^ e)
  | Success (message_and_verification_idx, tag) -> (
    match LabeledCryptoAPI.split message_and_verification_idx with
    | Error e -> error ("[process_authn_message]: cannot split the message into message and verification idx: " ^ e)
    | Success (verification_idx_bytes, message) -> (
      match LabeledCryptoAPI.bytes_to_nat verification_idx_bytes with
      | Error e -> error ("[process_authn_message]: cannot parse verification idx: " ^ e)
      | Success verification_idx -> (
        if (not (later_than message_idx verification_idx)) then error "[process_authn_message]: verification idx in message must be smaller or equal the message idx"
        else (
          assert(later_than message_idx verification_idx);
          if (LabeledCryptoAPI.verify #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #public #public verify_key_of_sender message_and_verification_idx tag) then
          (
            C.concat_split_lemma signed_message;
            assert(is_publishable ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now signed_message);
            concatenation_publishable_implies_components_publishable_forall ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage);

            assert(is_authenticated_message verification_idx message signed_message);
            // 3. Returns the original message if the signature verification was successful
            message
          )
          else (
            error "[process_authn_message]: cannot verify the signature tag"
          )
        )
      )
    )
  )



let create_conf_message #i #higher_level_preds sender receiver message =
  let now = GlobalRuntimeLib.global_timestamp() in
  // 1. Get a public key of the sender (using the LabeledPKI module)
  let pub_enc_key = LabeledPKI.get_public_key #(send_preds higher_level_preds) #now sender receiver PKE "SEND_LAYER_CONF_SEND" in
  // 2. Create a nonce (for the encryption)
  let (|t1,rand|) = rand_gen #(send_preds higher_level_preds) (join (readers [P sender]) (readers [P receiver])) (nonce_usage "PKE_NONCE") in

  let msg' = L.restrict message (readers [P receiver]) in
  assert(later_than now i);
  sk_label_lemma ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now pub_enc_key (readers [P receiver]);
  assert(can_flow now (get_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).L.key_usages msg') (get_sk_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).L.key_usages pub_enc_key));
  assert(is_valid ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now msg');
  assert(is_msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now msg' (get_sk_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).L.key_usages pub_enc_key));

  // 3. Create and return the ciphertext
  let ciphertext = LabeledCryptoAPI.pke_enc #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #(join (readers [P sender]) (readers [P receiver])) pub_enc_key rand msg' in
  (|now, ciphertext|)


let process_conf_message #now #higher_level_preds receiver confidential_message =
  // 1. Get a private decryption key of the receiver (using the LabeledPKI module)
  let (|si, priv_pk_key|) = LabeledPKI.get_private_key #(send_preds higher_level_preds) #now receiver PKE "SEND_LAYER_CONF_SEND" in
  // 2. Decrypt the ciphertext and returns the plaintext
  match L.pke_dec #(send_preds higher_level_preds).LabeledRuntimeAPI.global_usage #now #(readers [P receiver]) priv_pk_key confidential_message with
  | Success plaintext -> (
    assert(is_publishable (send_preds higher_level_preds).LabeledRuntimeAPI.global_usage now plaintext \/
      (exists j. later_than now j /\ higher_level_preds.extended_higher_layer_gu.send_function_predicates.confidential_send_pred j plaintext));
    plaintext
  )
  | Error e -> error e


let create_authn_conf_message #i #higher_level_preds sender receiver message =
  let now = GlobalRuntimeLib.global_timestamp() in
  assert(later_than now i);

  let gu = ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) in

  //Step 1: Create the plaintext: (sender, message)
  let sender_bytes = (string_to_bytes #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now sender) in
  let (verification_trace_idx_bytes:msg gu now public) = (nat_to_bytes #gu #now 4 i) in
  let sender_and_trace_idx_bytes =  L.concat #gu #now #(join (readers [P sender]) (readers [P receiver])) sender_bytes verification_trace_idx_bytes in
  let plaintext = L.concat #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #(join (readers [P sender]) (readers [P receiver]))
     sender_and_trace_idx_bytes message in

  //Step 2: Encrypt the message
  assert(includes_ids [P sender; P receiver] [P sender]);

  //the encryption predicate requires that the payload is readable by the sender
  includes_can_flow_lemma i [P sender; P receiver] [P sender];

  let higher_layer_key_usages = higher_level_preds.extended_higher_layer_gu.higher_layer_gu.LabeledCryptoAPI.key_usages in

  L.can_flow_transitive i (get_label higher_layer_key_usages message) (join (readers [P sender]) (readers [P receiver])) (readers [P sender]);
  assert(can_flow i (get_label higher_layer_key_usages message) (readers [P sender]));

  //the encryption function requires that the message is readable by the owner of the public key (i.e., the receiver)
  includes_can_flow_lemma i [P sender; P receiver] [P receiver];
  assert(can_flow i (get_label higher_layer_key_usages message) (readers [P receiver]));

  let pub_enc_key = LabeledPKI.get_public_key #(send_preds higher_level_preds) #now sender receiver PKE "SEND_LAYER_CONF_AUTHN_SEND" in

  assert(public_key_enc_pred higher_level_preds.extended_higher_layer_gu now "SEND_LAYER_CONF_AUTHN_SEND" pub_enc_key plaintext);
  assert(can_flow now (get_label higher_layer_key_usages plaintext) (join (readers [P sender]) (readers [P receiver])));

  sk_label_lemma ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now pub_enc_key (readers [P receiver]);
  let (|t1,enc_rand|) = rand_gen #(send_preds higher_level_preds) (join (readers [P sender]) (readers [P receiver])) (nonce_usage "PKE_NONCE") in
  let ciphertext = LabeledCryptoAPI.pke_enc
    #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #(join (readers [P sender]) (readers [P receiver])) pub_enc_key enc_rand plaintext in

  assert(higher_level_preds.extended_higher_layer_gu.send_function_predicates.authenticated_confidential_send_pred i message);

  //Step 3: Sign the ciphertext
  let now = GlobalRuntimeLib.global_timestamp() in
  let (|sk_si, signing_key|) = get_private_key #(send_preds higher_level_preds) #now sender SIG "SEND_LAYER_CONF_AUTHN_SEND" in
  let (|t1,n_sig|) = rand_gen #(send_preds higher_level_preds) (readers [P sender]) (nonce_usage "SIG_NONCE") in
  let tag = L.sign #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #(readers [P sender]) #public signing_key n_sig ciphertext in

  //Step 4: Concatenate the ciphertext with the signature tag
  let final_message = L.concat #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #public ciphertext tag in
  let now = GlobalRuntimeLib.global_timestamp() in
  assert(is_authenticated_confidential_message message final_message);
  (|now, final_message|)


let process_authn_conf_message #now #higher_level_preds sender receiver message_idx message =

  let higher_layer_key_usages = higher_level_preds.extended_higher_layer_gu.higher_layer_gu.LabeledCryptoAPI.key_usages in

  match LabeledCryptoAPI.split message with
  | Error e -> error ("[process_authn_conf_message]: cannot split message into ciphertext and signature tag: " ^ e)
  | Success (ciphertext, tag) ->
    // Check the signature
    let verify_key_of_sender = LabeledPKI.get_public_key #(send_preds higher_level_preds) #now receiver sender SIG "SEND_LAYER_CONF_AUTHN_SEND" in
    if(LabeledCryptoAPI.verify #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage)
       #now #public #public verify_key_of_sender ciphertext tag)
    then (
      // The next assertion follows from the successful verification
      assert(forall l s. is_verification_key ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now verify_key_of_sender l s ==>
              (can_flow now l public \/ sign_pred ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).usage_preds now s
                verify_key_of_sender ciphertext));

      assert((can_flow now (readers [P sender]) public \/ sign_pred ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).usage_preds now
               "SEND_LAYER_CONF_AUTHN_SEND" verify_key_of_sender ciphertext));

      assert(can_flow now (readers [P sender]) public \/
              (exists j. later_than now j /\ signature_pred higher_level_preds.extended_higher_layer_gu j "SEND_LAYER_CONF_AUTHN_SEND" verify_key_of_sender ciphertext));

      assert(is_publishable ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now message);
      assert(is_publishable ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now ciphertext);

      // Decrypt the message
      let (|si, priv_pk_key|) = LabeledPKI.get_private_key #(send_preds higher_level_preds) #now receiver PKE "SEND_LAYER_CONF_AUTHN_SEND" in
      match L.pke_dec #(send_preds higher_level_preds).LabeledRuntimeAPI.global_usage #now #(readers [P receiver]) priv_pk_key ciphertext with
      | Error e -> error ("[process_authn_conf_message]: decryption failed: " ^ e)
      | Success plaintext -> (
        match LabeledCryptoAPI.split plaintext with
        | Error e -> error ("[process_authn_conf_message]: cannot split plaintext into principal_and_verification_idx and payload: " ^ e)
        | Success (principal_and_verification_idx_bytes, payload) -> (
          match LabeledCryptoAPI.split principal_and_verification_idx_bytes with
          | Error e -> error ("[process_authn_conf_message]: cannot split principal_and_verification_idx into into principal and verification_idx: " ^ e)
          | Success (principal_bytes, verification_idx_bytes) -> (

          match bytes_to_string principal_bytes, bytes_to_nat verification_idx_bytes with
          | Success principal_in_msg, Success verification_idx_in_msg -> (
            if (principal_in_msg <> sender) then error "[process_authn_conf_message]: principal in plaintext differs from sender"
            else (

              assert(principal_in_msg = sender);

              //the next two assertions follow from the successful signature verification and decryption
              assert((corrupt_id now (P sender) \/
                      (exists j. later_than now j /\ signature_pred higher_level_preds.extended_higher_layer_gu j "SEND_LAYER_CONF_AUTHN_SEND" verify_key_of_sender ciphertext))); //[1]
              assert(is_publishable (send_preds higher_level_preds).LabeledRuntimeAPI.global_usage now plaintext \/
                      public_key_enc_pred higher_level_preds.extended_higher_layer_gu now "SEND_LAYER_CONF_AUTHN_SEND" (C.pk priv_pk_key) plaintext); //[2]


              //by definition of [ppred]:
              assert(is_publishable (send_preds higher_level_preds).LabeledRuntimeAPI.global_usage now plaintext \/
                      can_flow now (get_label higher_layer_key_usages payload) (readers [P sender]));

              assert(is_succ2 (C.split plaintext) principal_and_verification_idx_bytes payload);
              assert(is_succ2 (C.split principal_and_verification_idx_bytes) principal_bytes verification_idx_bytes);
              split_based_on_split_len_prefixed_lemma plaintext;
              split_based_on_split_len_prefixed_lemma principal_and_verification_idx_bytes;
              assert(split_len_prefixed 4 plaintext == Success (principal_and_verification_idx_bytes, payload));
              assert(split_len_prefixed 4 principal_and_verification_idx_bytes == Success (principal_bytes, verification_idx_bytes));
              splittable_term_publishable_implies_components_publishable_forall (send_preds higher_level_preds).LabeledRuntimeAPI.global_usage;

              assert(is_publishable (send_preds higher_level_preds).LabeledRuntimeAPI.global_usage now plaintext ==>
                is_publishable (send_preds higher_level_preds).LabeledRuntimeAPI.global_usage now payload);

              assert(~(corrupt_id now (P sender)) ==>
                      (exists j. later_than verification_idx_in_msg j /\ higher_level_preds.extended_higher_layer_gu.send_function_predicates.authenticated_confidential_send_pred j payload)); // follows from [1]

              assert(can_flow now (get_label higher_layer_key_usages payload) (readers [P sender])); // follows from [2]

              can_flow_to_public_implies_corruption now (P sender); //implies: (readers [P sender]) flows to public <==> (P sender) is corrupt

              assert((corrupt_id now (P sender)) ==>
                      can_flow now (get_label higher_layer_key_usages payload) public);

              assert((corrupt_id now (P sender) /\ can_flow now (get_label higher_layer_key_usages payload) public) \/
                      (exists j. later_than verification_idx_in_msg j /\ higher_level_preds.extended_higher_layer_gu.send_function_predicates.authenticated_confidential_send_pred j payload));


              //show [is_authenticated_confidential_message]
              concat_split_lemma plaintext;
              assert(plaintext == (C.concat (C.concat principal_bytes verification_idx_bytes) payload));
              assert(exists key rand.
                ciphertext == (C.pke_enc key rand plaintext)
              );

              LabeledCryptoAPI.verify_lemma verify_key_of_sender ciphertext tag;
              C.verify_lemma verify_key_of_sender ciphertext tag;

              assert(C.verify verify_key_of_sender ciphertext tag);
              assert(exists secret_key n. verify_key_of_sender == C.vk secret_key /\ tag == C.sign secret_key n ciphertext);
              assert(exists sign_key sign_nonce. tag == C.sign sign_key sign_nonce ciphertext);

              concat_split_lemma message;
              assert(message == C.concat ciphertext tag);
              assert(is_authenticated_confidential_message payload message);

              if (not (later_than message_idx verification_idx_in_msg)) then error "[process_authn_conf_message]: verification idx in message must be smaller or equal the message idx"
              else (|sender, payload|)
           )


          )
          | _, _ -> error ("[process_authn_conf_message]: cannot parse principal byte or verification timestamp (that was contained in the plaintext)"  )


    )))) else error "[process_authn_conf_message]: invalid signature"


let create_conf_message_for_request_pke #i #higher_level_preds sender receiver message =
  let now = GlobalRuntimeLib.global_timestamp() in
  // 1. Get a public key of the sender (using the LabeledPKI module)
  let pub_enc_key = LabeledPKI.get_public_key #(send_preds higher_level_preds) #now sender receiver PKE "SEND_LAYER_CONF_REQUEST_ONLY_PKE" in
  // 2. Create a nonce (for the encryption)
  let (|now,rand|) = rand_gen #(send_preds higher_level_preds) (join (readers [P sender]) (readers [P receiver])) (nonce_usage "PKE_NONCE") in

  LabeledCryptoAPI.can_flow_to_join_forall now;
  LabeledCryptoAPI.can_flow_from_join now (readers [P sender]) (readers [P receiver]);
  let msg' = L.restrict message (readers [P receiver]) in
  assert(later_than now i);
  assert(can_flow now (get_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).L.key_usages msg') (join (readers [P sender]) (readers [P receiver])));
  sk_label_lemma ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now pub_enc_key (readers [P receiver]);
  assert(can_flow now (get_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).L.key_usages msg') (get_sk_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).L.key_usages pub_enc_key));
  assert(is_valid ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now msg');
  assert(is_msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now msg' (get_sk_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).L.key_usages pub_enc_key));
  assert(can_flow now (get_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).key_usages msg') (join (readers [P sender]) (readers [P receiver])));

  // 3. Create and return the ciphertext
  let gu = ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) in
  assert(is_msg gu now msg' (get_sk_label gu.key_usages pub_enc_key));
  assert(can_flow now (get_label gu.key_usages msg') (join (readers [P sender]) (readers [P receiver])));

  assert(LabeledCryptoAPI.pke_pred gu.usage_preds now "SEND_LAYER_CONF_REQUEST_ONLY_PKE" pub_enc_key msg');
  let ciphertext = LabeledCryptoAPI.pke_enc #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #(join (readers [P sender]) (readers [P receiver])) pub_enc_key rand msg' in
  (|now, ciphertext|)

let process_conf_request_message_pke #now #higher_level_preds receiver confidential_message =
  // 1. Get a private decryption key of the receiver (using the LabeledPKI module)
  let (|si, priv_pk_key|) = LabeledPKI.get_private_key #(send_preds higher_level_preds) #now receiver PKE "SEND_LAYER_CONF_REQUEST_ONLY_PKE" in
  // 2. Decrypt the ciphertext and returns the plaintext
  match L.pke_dec #(send_preds higher_level_preds).LabeledRuntimeAPI.global_usage #now #(readers [P receiver]) priv_pk_key confidential_message with
  | Success plaintext -> (
    plaintext
  )
  | Error e -> error e

#push-options "--z3rlimit 50"
let create_auth_conf_message_for_request_pke #i #higher_level_preds sender receiver message =
  let now = GlobalRuntimeLib.global_timestamp() in
  // 1. Get a public key of the sender (using the LabeledPKI module)
  let pub_enc_key = LabeledPKI.get_public_key #(send_preds higher_level_preds) #now sender receiver PKE "SEND_LAYER_CONF_REQUEST_ONLY_PKE" in
  // 2. Create a nonce (for the encryption)
  let (|now,rand|) = rand_gen #(send_preds higher_level_preds) (join (readers [P sender]) (readers [P receiver])) (nonce_usage "PKE_NONCE") in

  LabeledCryptoAPI.can_flow_to_join_forall now;
  LabeledCryptoAPI.can_flow_from_join now (readers [P sender]) (readers [P receiver]);
  let msg' = L.restrict message (readers [P receiver]) in
  assert(later_than now i);
  assert(can_flow now (get_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).L.key_usages msg') (join (readers [P sender]) (readers [P receiver])));
  sk_label_lemma ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now pub_enc_key (readers [P receiver]);
  assert(can_flow now (get_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).L.key_usages msg') (get_sk_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).L.key_usages pub_enc_key));
   assert(is_valid ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now msg');
  assert(is_msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now msg' (get_sk_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).L.key_usages pub_enc_key));
  assert(can_flow now (get_label ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage).key_usages msg') (join (readers [P sender]) (readers [P receiver])));

  // 3. Create the ciphertext
  let gu = ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) in
  assert(is_msg gu now msg' (get_sk_label gu.key_usages pub_enc_key));
  assert(can_flow now (get_label gu.key_usages msg') (join (readers [P sender]) (readers [P receiver])));

  assert(LabeledCryptoAPI.pke_pred gu.usage_preds now "SEND_LAYER_CONF_REQUEST_ONLY_PKE" pub_enc_key msg');
  let ciphertext = LabeledCryptoAPI.pke_enc #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #(join (readers [P sender]) (readers [P receiver])) pub_enc_key rand msg' in
  let sign_text = concat (string_to_bytes #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now sender) 
		    (concat (string_to_bytes #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now receiver) ciphertext) in 
  split_concat_lemma (string_to_bytes #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now receiver) ciphertext;		    
  split_concat_lemma (string_to_bytes #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now sender) 
		     (concat (string_to_bytes #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now receiver) ciphertext);

  // 4. Sign the ciphertext
  let now = global_timestamp () in 
  let (|sk_si, signing_key|) = LabeledPKI.get_private_key #(send_preds higher_level_preds) #now sender SIG "SEND_LAYER_CONF_AUTHN_REQUEST" in
  let (|t1,n_sig|) = rand_gen #(send_preds higher_level_preds) (readers [P sender]) (nonce_usage "SIG_NONCE") in
  L.vk_lemma #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #t1 #(readers [P sender]) signing_key;
  let tag = L.sign #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #t1 #(readers [P sender]) #public signing_key n_sig sign_text in

  //Step 4: Concatenate the ciphertext with the signature tag
  let now = global_timestamp () in
  let final_message = L.concat #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #public sign_text tag in
  (|now, final_message|)	 
  
let process_auth_conf_request_message_pke #now #higher_level_preds sender receiver signed_message =
  // 1. Get the verification key for sender 
  let gu = ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) in
  let verify_key_of_sender = LabeledPKI.get_public_key #(send_preds higher_level_preds) #now receiver sender SIG "SEND_LAYER_CONF_AUTHN_REQUEST" in
  // 2. Split the signed message into the original message and the signature tag
  match LabeledCryptoAPI.split signed_message with
  | Error e -> error ("[process_authn_conf_request_message]: cannot split the message: " ^ e)
  | Success (confidential_message, tag) ->
    if (LabeledCryptoAPI.verify #((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) #now #public #public verify_key_of_sender confidential_message tag) then
    (
      C.concat_split_lemma signed_message;
      concatenation_publishable_implies_components_publishable_forall ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage);
      verification_key_label_lemma gu now verify_key_of_sender (readers [P sender]);
      assert (L.get_signkey_label gu.key_usages verify_key_of_sender == readers [P sender]);
      (match split confidential_message with
      | Error e -> error e
      | Success (sb, rest) -> (match split rest with | Error e -> error e 
	| Success (rb, confidential_message) -> 
	  (match bytes_to_string sb, bytes_to_string rb with 
	  | Success sender', Success receiver' ->
	    if sender' <> sender || receiver' <> receiver then error "incorrect principal"
	    else
	    (assert (sender=sender' /\ receiver=receiver');
	    // 3. Get a private decryption key of the receiver (using the LabeledPKI module)
	    let (|si, priv_pk_key|) = LabeledPKI.get_private_key #(send_preds higher_level_preds) #now receiver PKE "SEND_LAYER_CONF_REQUEST_ONLY_PKE" in
	    // 4. Decrypt the ciphertext and returns the plaintext
	    (match L.pke_dec #(send_preds higher_level_preds).LabeledRuntimeAPI.global_usage #now #(readers [P receiver]) priv_pk_key confidential_message with
	    | Success plaintext ->
	      L.can_flow_to_join_and_principal_and_unpublishable_property now;
	      L.can_flow_to_join_forall now;
	      L.splittable_term_publishable_implies_components_publishable_forall gu;
	      C.split_based_on_split_len_prefixed_lemma plaintext;
	      assert (
		L.can_flow now (readers [P sender]) public \/
		L.can_flow now (L.get_label gu.key_usages plaintext) public \/
		(match split plaintext with 
		| Error e -> False
		| Success (sym_key, msg) -> 
		  was_rand_generated_before now sym_key (join (readers [P sender]) (readers [P receiver])) (aead_usage "AEAD.Symmetric_Send_Key") /\ L.can_flow now (L.get_label gu.key_usages plaintext) (join (readers [P sender]) (readers [P receiver])) /\
		  (exists j. j<=now /\ higher_level_preds.extended_higher_layer_gu.send_function_predicates.request_pred j msg) /\
		  L.can_flow now (L.get_label gu.key_usages msg) (L.get_label gu.key_usages sym_key)
		));
	      plaintext
	    | Error e -> error e))
	  | _ -> error "bytes to string error")))
    )
    else (
      error "cannot verify the signature tag"
    ) 
#pop-options
