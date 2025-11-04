/// BA.Labeled.SerializingParsing (Implementation)
/// ==============================================
module BA.Labeled.SerializingParsing

friend BA.Messages
friend BA.Sessions

module C = CryptoLib

let parse_msg (#gu:extended_global_usage) (#i:timestamp) (#l:label) (m: msg gu i l) : (r:result message{r == parse_msg_raw m}) =
  match split m with
  | Error e -> Error ("[parse_msg or parse_msg_raw]: cannot split message into tag and payload")
  | Success (msg_tag, part_2) ->  (
    match bytes_to_string msg_tag with
    | Error e -> Error "[parse_msg or parse_msg_raw]: cannot parse message tag"
    | Success "Msg_Tag_Generate_Account_Request" -> (
      let password = part_2 in
      Success (GenerateAccountReq password)
    )
    | Success "Msg_Tag_Get_Secret_Request" -> (
      let password = part_2 in
      Success (GetSecretReq password)
    )
    | Success "Msg_Tag_Generate_Account_Resp" -> (
      match bytes_to_string part_2 with
      | Error e -> Error e
      | Success status -> Success (GenerateAccountResp status)
    )
    | Success "Msg_Tag_Get_Secret_Resp" -> (
      let encrypted_secret = part_2 in
      Success (GetSecretResp encrypted_secret)
    )
    | Success _ -> Error "[parse_msg or parse_msg_raw]: wrong message tag"
  )

let secret_message_publishable_implies_secret_publishable #gu #i #l m =
  match split m with
  | Success (msg_tag, encrypted_secret) ->  (
    match bytes_to_string msg_tag with
    | Error e -> ()
    | Success "Msg_Tag_Get_Secret_Resp" -> (
          split_based_on_split_len_prefixed_lemma m;
          assert(C.is_succ2 (C.split_len_prefixed 4 m) msg_tag encrypted_secret);
          splittable_term_publishable_implies_components_publishable_forall gu
    )
  | _ -> ()
  )


let serialized_account_request_message_publishable_implies_password_publishable #gu #i #l m =
  match split m with
  | Success (msg_tag, password) ->  (
    match bytes_to_string msg_tag with
    | Error e -> ()
    | Success "Msg_Tag_Generate_Account_Request" -> (
      split_based_on_split_len_prefixed_lemma m;
      assert(C.is_succ2 (C.split_len_prefixed 4 m) msg_tag password);
      splittable_term_publishable_implies_components_publishable_forall gu;
      assert(is_publishable gu i m ==> is_publishable gu i password)
    )
  | _ -> ()
  )

let serialized_account_request_message_valid_implies_password_valid #gu #i #l m =
  match split m with
  | Success (msg_tag, password) ->  (
    match bytes_to_string msg_tag with
    | Error e -> ()
    | Success "Msg_Tag_Generate_Account_Request" -> ()
  | _ -> ()
  )

let serialized_secret_response_message_encrypted_secret_valid #gu #i #l m =
  match split m with
  | Success (msg_tag, password) ->  (
    match bytes_to_string msg_tag with
    | Error e -> ()
    | Success "Msg_Tag_Generate_Account_Request" -> ()
  | _ -> ()
  )

let serialized_account_request_message_label_and_password_label #gu #i #l m =
  match split m with
  | Success (msg_tag, password) ->  (
    match bytes_to_string msg_tag with
    | Error e -> ()
    | Success "Msg_Tag_Generate_Account_Request" -> ()
    | Success "Msg_Tag_Get_Secret_Request" -> ()
    | _ -> ()
    )
  | _ -> ()


let serialize_msg i l m =
  match m with
  | GenerateAccountReq password -> (
    let msg_tag = "Msg_Tag_Generate_Account_Request" in
    let result = concat #gu #i #l (string_to_bytes #gu #i msg_tag) password in
    result
  )
  | GetSecretReq password -> (
    let msg_tag = "Msg_Tag_Get_Secret_Request" in
    let result = concat #gu #i #l (string_to_bytes #gu #i msg_tag) password in
    result
  )
  | GenerateAccountResp status ->(
    let msg_tag = "Msg_Tag_Generate_Account_Resp" in
    let result = concat #gu #i #l
      (string_to_bytes #gu #i msg_tag)
      (string_to_bytes #gu #i status) in
    result
  )
  | GetSecretResp encrypted_secret -> (
    let msg_tag = "Msg_Tag_Get_Secret_Resp" in
    let result = concat #gu #i #l
      (string_to_bytes #gu #i msg_tag)
      encrypted_secret in
    result
  )

let parse_serialize_msg_lemma i l msg = ()



let parse_client_session_state_labeled i l st =
  match split st with
  | Error _ -> None
  | Success (state_tag, state_payload) -> (
     match bytes_to_string state_tag with
     | Success "client.state.without.secret.without.send_idx.without.sym_key" -> (
       match split state_payload with
       | Error _ -> None
       | Success (username_server_bytes, password) -> (
         match split username_server_bytes with
         | Error _ -> None
         | Success (username_bytes, server_bytes) -> (
           match bytes_to_string username_bytes, bytes_to_string server_bytes with
           | Success username, Success server -> Some (ClientSession username server password None None None)
           | _,_ -> None
         )
       )
     )
     | Success "client.state.with.secret.without.send_idx.without.sym_key" -> (
       match split state_payload with
       | Error _ -> None
       | Success (username_server_password, secret) -> (
         match split username_server_password with
         | Error _ -> None
         | Success (username_server, password) -> (
           match split username_server with
           | Error _ -> None
           | Success (username_bytes, server_bytes) -> (
             match bytes_to_string username_bytes, bytes_to_string server_bytes with
             | Success username, Success server -> Some (ClientSession username server password (Some secret) None None)
             | _,_ -> None
           )
         )
       )
     )
     | Success "client.state.without.secret.with.send_idx.without.sym_key" -> (
       match split state_payload with
       | Error _ -> None
       | Success (username_server_password, send_idx_bytes) -> (
         match split username_server_password with
         | Error _ -> None
         | Success (username_server, password) -> (
           match split username_server with
           | Error _ -> None
           | Success (username_bytes, server_bytes) -> (
             match bytes_to_string username_bytes, bytes_to_string server_bytes, bytes_to_nat send_idx_bytes with
             | Success username, Success server, Success send_idx -> Some (ClientSession username server password None (Some send_idx) None)
             | _,_,_ -> None
           )
         )
       )
     )
     | Success "client.state.with.secret.with.send_idx.without.sym_key" -> (
       match split state_payload with
       | Error _ -> None
       | Success (username_server_password_secret, send_idx_bytes) -> (
         match split username_server_password_secret with
         | Error _ -> None
         | Success (username_server_password, secret) -> (
           match split username_server_password with
           | Error _ -> None
           | Success (username_server, password) -> (
             match split username_server with
             | Error _ -> None
             | Success (username_bytes, server_bytes) -> (
                     match bytes_to_string username_bytes, bytes_to_string server_bytes, bytes_to_nat send_idx_bytes with
                     | Success username, Success server, Success send_idx -> Some (ClientSession username server password (Some secret) (Some send_idx) None)
                     | _,_,_ -> None
             )
           )
         )
       )
     )
     | Success "client.state.without.secret.without.send_idx.with.sym_key" -> (
         match split state_payload with
         | Error _ -> None
         | Success (username_server_bytes_and_password, sym_key) -> (
           match split username_server_bytes_and_password with
           | Error _ -> None
           | Success (username_server_bytes, password) -> (
             match split username_server_bytes with
             | Error _ -> None
             | Success (username_bytes, server_bytes) -> (
               match bytes_to_string username_bytes, bytes_to_string server_bytes with
               | Success username, Success server -> Some (ClientSession username server password None None (Some sym_key))
               | _,_ -> None
             )
           )
       )
     )
     | Success "client.state.without.secret.with.send_idx.with.sym_key" -> (
         match split state_payload with
         | Error _ -> None
         | Success (username_server_bytes_and_password_send_idx_bytes, sym_key) -> (
           match split username_server_bytes_and_password_send_idx_bytes with
           | Error _ -> None
           | Success (username_server_password, send_idx_bytes) -> (
             match split username_server_password with
             | Error _ -> None
             | Success (username_server, password) -> (
               match split username_server with
               | Error _ -> None
               | Success (username_bytes, server_bytes) -> (
                 match bytes_to_string username_bytes, bytes_to_string server_bytes, bytes_to_nat send_idx_bytes with
                 | Success username, Success server, Success send_idx -> Some (ClientSession username server password None (Some send_idx) (Some sym_key))
                 | _,_,_ -> None
               )
             )
           )
         )
     )
     | _ -> None
  )

let parse_client_session_state_equals_parse_client_session_state_labeled i l st = ()



let parse_server_session_state_labeled #i #l #gu st =
  match CryptoLib.split st with
  | Error _ -> None
  | Success (tag, account_data_with_tag) -> (
    if(CryptoLib.bytes_to_string tag <> (Success "server_account_session")) then None
    else (
      match CryptoLib.split account_data_with_tag with
      | Error _ -> None
      | Success (password, secret) -> (
        splittable_term_flows_to_label_implies_components_flow_to_label_forall i 4 gu l st;
        split_based_on_split_len_prefixed_lemma st;
        assert(is_succ2 (CryptoLib.split st) tag account_data_with_tag);
        splittable_term_flows_to_label_implies_components_flow_to_label_forall i 4 gu l account_data_with_tag;
        split_based_on_split_len_prefixed_lemma account_data_with_tag;
        assert(is_succ2 (CryptoLib.split account_data_with_tag) password secret);
        assert(is_msg gu i secret l);
        Some (ServerAccountSession password secret)
      )
    )
  )


let parse_server_session_state_labeled_equals_raw_parse_function #i #l #gu st = ()
