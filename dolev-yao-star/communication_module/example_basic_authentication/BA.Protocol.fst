/// BA.Protocol (implementation)
/// ===============================
module BA.Protocol


#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
  let initiator_send_account_registration_request #i initiator responder password =
  let t0 = GlobalRuntimeLib.global_timestamp () in
  let first_message = GenerateAccountReq password in
  let l = (readers [P initiator; P responder]) in

  print_string ("BA.Protocol.initiator_send_account_generation_message: generated first message\n");

  assert(is_msg gu i password (readers [P initiator; P responder]));
  assert(later_than t0 i); //triggers smtpat for is_valid_later
  assert(is_msg gu t0 password (readers [P initiator; P responder]));

  let serialized_first_message = serialize_msg t0 (readers [P initiator; P responder]) first_message in

  parse_serialize_msg_lemma t0 (readers [P initiator; P responder]) first_message;

  assert(was_rand_generated_before t0 password (readers [(P initiator); (P responder)]) (nonce_usage "BA.Password"));
  assert(request_send_pred t0 serialized_first_message);
  assert(is_msg gu t0 serialized_first_message (readers [(P initiator); (P responder)]));

  //store (username, password) into state
  let new_client_session_number = Communication.API.new_session_number #(ba_preds) initiator in
  let new_client_session = (ClientSession initiator responder password None None) in
  let (serialized_client_session:msg gu t0 (readers [P initiator; P responder])) =
    serialize_client_session_state gu t0 (readers [P initiator; P responder]) new_client_session in

  parse_serialize_client_session_state_lemma gu t0 (readers [P initiator; P responder]) initiator responder password None None;

  assert(session_st_inv t0 initiator new_client_session_number 0 serialized_client_session);

  //the next assertions are needed for calling [new_session]
  assert(covers (P initiator) (V initiator new_client_session_number 0));
  assert(includes_ids ([P initiator]) ([V initiator new_client_session_number 0]));
  LCA.includes_can_flow_lemma t0 ([P initiator]) ([V initiator new_client_session_number 0]);
  assert(LCA.can_flow t0  (readers [P initiator; P responder]) (readers [P initiator]));
  assert(is_msg gu t0 serialized_client_session (readers [V initiator new_client_session_number 0]));

  Communication.API.new_session #(ba_preds) #t0 initiator new_client_session_number 0 serialized_client_session;

  print_string ("BA.Protocol.initiator_send_account_generation_message: calling send request function\n");

  //show that the label of the message can flow to the join label (this is required by the
  //send_request function)
  LabeledCryptoAPI.can_flow_to_join_forall t0;
  assert(LCA.can_flow t0  (readers [P initiator; P responder]) (readers [P initiator]));
  assert(LCA.can_flow t0  (readers [P initiator; P responder]) (readers [P responder]));
  let (serialized_first_message:msg gu t0 (join (readers [P initiator])
    (readers [P responder]))) = serialized_first_message in
  let (|sym_key_session_state_idx, _, send_idx|) = Communication.API.initiator_send_request #t0 #ba_preds initiator responder serialized_first_message in
  print_string ("BA.Protocol.initiator_send_account_generation_message: finished calling send request function\n");
  Success (|sym_key_session_state_idx, new_client_session_number, send_idx|)
#pop-options


#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let responder_receive_account_registration_request_and_respond receiver message_send_idx =
  print_string ("BA.Protocol.receive_account_generation_message_and_respond: started\n");

  let now = GlobalRuntimeLib.global_timestamp () in
  let (|t0, sender, sym_key, message|) = Communication.API.responder_receive_request #now #ba_preds message_send_idx receiver in

  // The message was sent over a confidential-only channel. Thus, either the attacker sent the
  // message (and the message is publishable), or the [request_send_pred] holds true.
  assert((is_publishable gu t0 sym_key /\ is_publishable gu t0 message) \/ (exists j. later_than t0 j /\ request_send_pred j message));
  let parsed_message = parse_msg message in
  match parsed_message with
  | Success (GenerateAccountReq password) -> (

    let label_of_sym_key = LCA.get_label ba_key_usages sym_key in
    let label_of_password = LCA.get_label ba_key_usages password in
    let label_of_message = LCA.get_label ba_key_usages message in

    assert(LCA.can_flow t0 label_of_message label_of_sym_key);
    assert(is_valid gu t0 message);
    serialized_account_request_message_valid_implies_password_valid #gu #t0 #label_of_message message;
    assert(is_valid gu t0 password);

    serialized_account_request_message_label_and_password_label #gu #t0 #label_of_message message;
    assert(LCA.can_flow t0 label_of_password label_of_message);

    // We label the secret with the label of the password.
    let (|t1, secret|) = Communication.Layer.rand_gen #ba_preds label_of_password (nonce_usage "BA.Secret") in

    let new_state_session_number = Communication.API.new_session_number #(ba_preds) receiver in

    serialized_account_request_message_publishable_implies_password_publishable message;
    assert(is_publishable gu t0 message ==> is_publishable gu t0 password);

    assert(LCA.can_flow t1 (LCA.get_label ba_key_usages message) (readers [(P receiver)]));
    assert(LCA.can_flow t1 (LCA.get_label ba_key_usages secret) (readers [(P receiver)]));
    assert(LCA.can_flow t1 (LCA.get_label ba_key_usages password) (readers [(P receiver)]));

    assert(later_than t1 t0);

    assert(LCA.can_flow t1 (LCA.get_label ba_key_usages password) label_of_password);

    let (serialized_account_data:msg gu t1 label_of_password) = serialize_server_session_state gu t1 label_of_password (ServerAccountSession password secret) in

    assert(covers (P receiver) (V receiver new_state_session_number 0));
    assert(includes_ids ([P receiver]) ([V receiver new_state_session_number 0]));
    LCA.includes_can_flow_lemma t1 ([P receiver]) ([V receiver new_state_session_number 0]);
    assert(LCA.can_flow t1  label_of_password (readers [P receiver]));
    assert(LCA.can_flow t1  label_of_password (readers [V receiver new_state_session_number 0]));
    assert(is_msg gu t1 serialized_account_data (readers [V receiver new_state_session_number 0]));


    let t2 = GlobalRuntimeLib.global_timestamp () in
    assert(t2 = t1 + 1);

    parse_serialize_server_session_state_lemma gu t1 label_of_password password secret;

    assert(match parse_server_session_state serialized_account_data with
      | Some (ServerAccountSession parsed_password parsed_secret) ->  parsed_password = password /\ parsed_secret = secret
      | _ -> False);


    // label of the secret can flow to the label of the password:
    assert(BA.Preds.session_st_inv t2 receiver new_state_session_number 0 serialized_account_data);

    print_string ("BA.Protocol.receive_account_generation_message_and_respond: generating session now ...\n");

    assert(is_msg gu t2 serialized_account_data (readers [V receiver new_state_session_number 0]));

    Communication.API.new_session #(ba_preds) #t2 receiver new_state_session_number 0 serialized_account_data;
    print_string ("BA.Protocol.receive_account_generation_message_and_respond: finished generating session\n");


    let second_message = GenerateAccountResp "Account created" in
    let serialized_second_message = serialize_msg t1 public second_message in

    parse_serialize_msg_lemma t1 public second_message;

    let now = GlobalRuntimeLib.global_timestamp () in
    assert(response_send_pred now serialized_second_message message sym_key);

    assert(Communication.Layer.is_request_at_idx message message_send_idx sym_key);

    let send_idx = Communication.API.responder_send_response #now #label_of_sym_key #ba_preds sender receiver sym_key message_send_idx message serialized_second_message in


    print_string ("BA.Protocol.receive_account_generation_message_and_respond: finished\n");

    Success (|send_idx, new_state_session_number|)
  )
  | _ -> Error "Wrong Message Type"
#pop-options


#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let initiator_process_account_registration_response initiator sym_key_state_session_idx send_idx_of_request =
  let (|t0, responder, message, send_idx_of_req_from_response|) = Communication.API.initiator_receive_response #ba_preds sym_key_state_session_idx send_idx_of_request initiator in
  match parse_msg message with
  | Success (GenerateAccountResp status) -> (
    print_string ("BA.Protocol.initiator_process_account_generation_response: successfully received first response\n");
    Success status
  )
  | _ -> Error "received wrong message type"
#pop-options


#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let initiator_send_get_secret_request #i initiator app_data_session_idx = 
  let t0 = GlobalRuntimeLib.global_timestamp () in
  let (|app_data_vi, app_data_session|) = Communication.API.get_session #ba_preds #t0 initiator app_data_session_idx in
  match parse_client_session_state app_data_session with
  | Some (ClientSession username responder password _ _) -> (

    let second_request_message = GetSecretReq password in

    print_string ("\n\nBA.Protocol.initiator_send_get_secret_message: generated message\n");

    parsed_client_state_cannot_be_parsed_by_server app_data_session;
    assert(was_rand_generated_before t0 password (readers [(P initiator); (P responder)]) (nonce_usage "BA.Password"));
    rand_is_secret #gu #t0 #(readers [(P initiator); (P responder)])
      #(nonce_usage "BA.Password") password;
    assert(is_msg gu t0 password (readers [P initiator; P responder]));

    let serialized_second_request_message = serialize_msg t0 (readers [P initiator; P responder]) second_request_message in

    parse_serialize_msg_lemma t0 (readers [P initiator; P responder]) second_request_message;


    assert(request_send_pred t0 serialized_second_request_message);
    assert(is_msg gu t0 serialized_second_request_message (readers [(P initiator); (P responder)]));

    //show that the label of the message can flow to the join label (this is required by the
    //send_request function)
    LabeledCryptoAPI.can_flow_to_join_forall t0;
    assert(LCA.can_flow t0  (readers [P initiator; P responder]) (readers [P initiator]));
    assert(LCA.can_flow t0  (readers [P initiator; P responder]) (readers [P responder]));
    let (serialized_second_request_message:msg gu t0 (join (readers [P initiator]) (readers [P
      responder]))) = serialized_second_request_message in

    print_string ("BA.Protocol.initiator_send_get_secret_message: calling send request function\n");
    let (|sym_key_session_state_idx, _, send_idx|) = Communication.API.initiator_send_request initiator responder serialized_second_request_message in
    print_string ("BA.Protocol.initiator_send_get_secret_message: finished calling send request function\n");

    let t0 = GlobalRuntimeLib.global_timestamp () in

    // Update state:
    assert(is_valid_client_state gu  t0
      (readers [V initiator app_data_session_idx app_data_vi]) (ClientSession initiator responder password None (Some send_idx)));
    let (serialized_updated_client_session:msg gu t0 (readers [V initiator app_data_session_idx app_data_vi])) =
      serialize_client_session_state gu t0 (readers [P initiator; P responder]) (ClientSession initiator responder password None (Some send_idx)) in

    parse_serialize_client_session_state_lemma gu t0 (readers [V initiator app_data_session_idx app_data_vi]) initiator responder password None (Some send_idx);

    assert(session_st_inv t0 initiator app_data_session_idx app_data_vi app_data_session);
    assert(Some? (parse_client_session_state app_data_session));
    assert(None? (parse_server_session_state app_data_session));
    assert(was_rand_generated_before t0 password (readers [(P initiator); (P responder)]) (nonce_usage "BA.Password"));

    assert(exists sym_key. Communication.Layer.is_request_at_idx serialized_second_request_message send_idx sym_key);
    assert(match parse_msg_raw serialized_second_request_message with
        | Success (GetSecretReq password_in_request) -> password_in_request == password
        | _ -> False);

    assert(exists request sym_key. Communication.Layer.is_request_at_idx request send_idx sym_key/\
      (
        match parse_msg_raw request with
        | Success (GetSecretReq password_in_request) -> password_in_request == password
        | _ -> False
      )
    );


    parse_serialize_client_session_state_lemma gu t0 (readers [P initiator; P responder]) initiator responder password None (Some send_idx);

    Communication.Layer.is_request_at_idx_injective_forall ();

    assert(
      match parse_server_session_state serialized_updated_client_session, parse_client_session_state serialized_updated_client_session with
      | Some (ServerAccountSession password secret), None -> False
      | None, Some (ClientSession initiator_in_state server password opt_secret opt_latest_get_secret_request_idx) ->
        (
        initiator_in_state = initiator /\
        was_rand_generated_before t0 password (readers [(P initiator); (P server)]) (nonce_usage "BA.Password") /\
        (LCA.get_label ba_gu.key_usages password) == (readers [P initiator; P server]) /\
        (Some? opt_secret ==> False) /\
        (Some? opt_latest_get_secret_request_idx ==>
          (
          let latest_get_secret_request_idx = Some?.v opt_latest_get_secret_request_idx in
          exists sym_key. Communication.Layer.is_request_at_idx serialized_second_request_message latest_get_secret_request_idx sym_key /\
            (
              match parse_msg_raw serialized_second_request_message with
              | Success (GetSecretReq password_in_request) -> password_in_request == password
              | _ -> False
            )
          )
        )
      )
      | _ -> True
    );

    assert(session_st_inv t0 initiator app_data_session_idx 0 serialized_updated_client_session);

    //the next assertions are needed for calling [update_session]
    assert(covers (P initiator) (V initiator app_data_session_idx 0));
    assert(includes_ids ([P initiator]) ([V initiator app_data_session_idx 0]));
    LCA.includes_can_flow_lemma t0 ([P initiator]) ([V initiator app_data_session_idx 0]);
    assert(LCA.can_flow t0  (readers [P initiator; P responder]) (readers [P initiator]));
    assert(is_msg gu t0 serialized_updated_client_session (readers [V initiator app_data_session_idx 0]));

    Communication.API.update_session #(ba_preds) #t0 initiator app_data_session_idx 0 serialized_updated_client_session;

    Success (|sym_key_session_state_idx, send_idx|)
  )
  | _ -> Error "cannot parse initiator state"
#pop-options


let find_session_predicate (password:bytes) (si:nat) (vi:nat) (st:bytes) : bool =
  match parse_server_session_state st with
  | None -> false
  | Some (ServerAccountSession stored_password stored_secret) ->
        stored_password = password

#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let responder_receive_get_secret_request_and_respond receiver message_send_idx =
  print_string ("BA.Protocol.receive_account_generation_message_and_respond: started\n");

  let now = GlobalRuntimeLib.global_timestamp () in
  let (|t0, sender, sym_key, message|) = Communication.API.responder_receive_request #now #ba_preds message_send_idx receiver in

  // The message was sent over a confidential-only channel. Thus, either the attacker sent the
  // message (and the message is publishable), or the [request_send_pred] holds true.
  assert((is_publishable gu t0 sym_key /\ is_publishable gu t0 message) \/ (exists j. later_than t0 j /\ request_send_pred j message));
  let parsed_message = parse_msg message in
  match parsed_message with
  | Success (GetSecretReq password) -> (

    // retrieve the secret from the state of the responder
    match Communication.API.find_session #(ba_preds) #t0 receiver (find_session_predicate password) with
    | None -> Error "[responder_receive_get_secret_message_and_respond]: wrong username or password, or account was not generated"
    | Some (|si, vi, st|) -> (
      match parse_server_session_state_labeled st with
      | None -> Error "[responder_receive_get_secret_message_and_respond]: can't parse session state containing the received password"
      | Some (ServerAccountSession stored_password secret) -> (
        if (stored_password <> password) then Error "[responder_receive_get_secret_message_and_respond]: wrong password"
        else (

          assert(stored_password = password);

          print_string ("BA.Protocol.responder_receive_get_secret_message_and_respond: successfully retrieved secret: ");
          print_bytes secret;
          print_string (" \n");


          // when previously creating the secret, we must ensure that the secret can flow to the label of the password:
          // (1) the password is created by the attacker ==> the secret must be publishable
          // (2) the password is created by an honest initiator ==> the secret must flow to the initiator (and the responder)
          let label_of_pwd = LCA.get_label ba_key_usages password in
          let label_of_sym_key = LCA.get_label ba_key_usages sym_key in
          let label_of_message = LCA.get_label ba_key_usages message in

          serialized_account_request_message_label_and_password_label #gu #t0 #label_of_message message;
          assert(LCA.can_flow t0 label_of_pwd label_of_message);

          assert(LCA.can_flow t0 label_of_message label_of_sym_key);
          assert(LCA.can_flow t0 label_of_pwd label_of_sym_key);

          let label_of_secret = LCA.get_label ba_key_usages secret in

          //the state invariant for the server holds true as the state is a server state (and cannot
          //be a client state):
          parsed_server_state_cannot_be_parsed_by_client st;

          // necessary to assert the properties of the password and secret
          // from the state invariant
          parse_server_session_state_labeled_equals_raw_parse_function st;

          assert(BA.Preds.session_st_inv t0 receiver si vi st);
          assert(LCA.can_flow t0 (LCA.get_label ba_key_usages secret) (LCA.get_label ba_key_usages password));

          // from the state invariant:
          assert(LCA.can_flow t0 label_of_secret label_of_pwd);

          let (secret:msg gu t0 label_of_pwd) = secret in

          let second_response = GetSecretResp secret in
          let serialized_second_response = serialize_msg t0 label_of_pwd second_response in

          parse_serialize_msg_lemma t0 label_of_pwd second_response;
          assert(response_send_pred t0 serialized_second_response message sym_key);
          assert(is_msg gu t0 serialized_second_response label_of_pwd);


          assert(is_publishable gu t0 sym_key \/ is_aead_key gu t0 sym_key label_of_sym_key "AEAD.Symmetric_Send_Key");


          let send_idx = Communication.API.responder_send_response #t0 #(LCA.get_label ba_key_usages sym_key) #ba_preds sender receiver sym_key message_send_idx message serialized_second_response in
          Success send_idx
        )
      )
    )
  )
  | _ -> Error "[responder_receive_get_secret_message_and_respond]: Wrong Message Type"
#pop-options


#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let initiator_process_response_with_secret initiator sym_key_state_session_idx send_idx_of_request =
  let (|t0, responder, message, send_idx_of_req_from_response|) = Communication.API.initiator_receive_response #ba_preds sym_key_state_session_idx send_idx_of_request initiator in
  match parse_msg message with
  | Success (GetSecretResp secret) -> (
    print_string ("BA.Protocol.initiator_process_response_with_secret: successfully received secret: ");
    print_bytes secret;
    print_string (" \n\n");

    let app_data_session_opt = Communication.API.find_session #ba_preds #t0 initiator (fun si vi st ->
      match parse_client_session_state st with
      | Some (ClientSession _ responder_in_state _ _ (Some latest_get_secret_request_idx)) -> responder_in_state = responder && send_idx_of_req_from_response = latest_get_secret_request_idx
      | _ -> false
    ) in
    match app_data_session_opt with
    | None -> error "Could not find appropriate session to continue"
    | Some (|app_data_session_idx, app_data_vi, app_data_session|) -> (

      assert(is_msg gu t0 app_data_session (readers [V initiator app_data_session_idx app_data_vi]));

      assert(is_valid gu t0 app_data_session);

      let Some (ClientSession initiator_in_state responder_in_state password _ (Some latest_get_secret_request_idx)) = parse_client_session_state_labeled t0 (readers [V initiator app_data_session_idx app_data_vi]) app_data_session in

      assert(latest_get_secret_request_idx = send_idx_of_req_from_response);
      assert(responder = responder_in_state);

      parsed_client_state_cannot_be_parsed_by_server app_data_session;

      assert((LCA.get_label ba_key_usages password) == (readers [P initiator; P responder]));

      assert(((LCA.corrupt_id t0 (P initiator) \/ LCA.corrupt_id t0 (P responder)) /\
        is_publishable gu t0 message) \/ (exists j request (sym_key:bytes). later_than t0 j /\ response_send_pred j message request sym_key));

      secret_message_publishable_implies_secret_publishable #gu #t0 #(readers [P initiator]) message;

      assert(is_publishable gu t0 message ==>
        is_publishable gu t0 secret);


      Communication.Layer.is_request_at_idx_injective_forall ();

      assert(is_msg gu  t0 password (readers [V initiator app_data_session_idx app_data_vi]));

      rand_is_secret #gu #t0 #(readers [P initiator; P responder]) #(nonce_usage "BA.Secret") secret;

      assert(covers (P initiator) (V initiator app_data_session_idx 0));
      assert(includes_ids ([P initiator]) ([V initiator app_data_session_idx 0]));
      LCA.includes_can_flow_lemma t0 ([P initiator]) ([V initiator app_data_session_idx 0]);
      assert(LCA.can_flow t0  (readers [P initiator; P responder]) (readers [P initiator]));

      assert(is_valid_client_state gu t0
         (readers [V initiator app_data_session_idx app_data_vi]) (ClientSession initiator responder password (Some secret) None));
      let (serialized_updated_client_session:msg gu t0 (readers [V initiator app_data_session_idx app_data_vi])) =
        serialize_client_session_state gu t0 (readers [P initiator; P responder]) (ClientSession initiator responder password (Some secret) None) in

      parse_serialize_client_session_state_lemma gu t0 (readers [V initiator app_data_session_idx app_data_vi]) initiator responder password (Some secret) None;
      parse_serialize_client_session_state_lemma gu t0 (readers [P initiator; P responder]) initiator responder password (Some secret) None;

      assert(session_st_inv t0 initiator app_data_session_idx app_data_vi app_data_session);

      assert(Some? (parse_client_session_state app_data_session));
      assert(None? (parse_server_session_state app_data_session));

      assert(was_rand_generated_before t0 password (readers [(P initiator_in_state); (P responder)]) (nonce_usage "BA.Password"));

      parse_client_session_state_equals_parse_client_session_state_labeled t0 (readers [V initiator app_data_session_idx app_data_vi]) serialized_updated_client_session;


      assert(session_st_inv t0 initiator app_data_session_idx 0 serialized_updated_client_session);

      //the next assertions are needed for calling [update_session]
      assert(covers (P initiator) (V initiator app_data_session_idx 0));
      assert(includes_ids ([P initiator]) ([V initiator app_data_session_idx 0]));
      LCA.includes_can_flow_lemma t0 ([P initiator]) ([V initiator app_data_session_idx 0]);
      assert(LCA.can_flow t0  (readers [P initiator; P responder]) (readers [P initiator]));
      assert(is_msg gu t0 serialized_updated_client_session (readers [V initiator app_data_session_idx 0]));

      Communication.API.update_session #(ba_preds) #t0 initiator app_data_session_idx 0 serialized_updated_client_session;
      Success ()
    )
  )
  | _ -> Error "received wrong message type"
#pop-options
