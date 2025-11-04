/// BA.Sessions
/// ==============

module BA.Sessions

let serialize_server_session_state gu i label_of_password server_session =
  match server_session with
  | ServerAccountSession password secret ->
    let password:msg gu i label_of_password = password in
    let serialized_account_data = concat #gu #i #label_of_password password secret in
    let serialized_account_data_with_tag = concat #gu #i #label_of_password (string_to_bytes #gu # i "server_account_session") serialized_account_data in
    serialized_account_data_with_tag

let parse_server_session_state st =
  match CryptoLib.split st with
  | Error _ -> None
  | Success (tag, account_data_with_tag) -> (
    if(CryptoLib.bytes_to_string tag <> (Success "server_account_session")) then None
    else (
      match CryptoLib.split account_data_with_tag with
      | Error _ -> None
      | Success (password, secret) -> (
        Some (ServerAccountSession password secret)
      )
    )
  )

let parse_serialize_server_session_state_lemma gu i l password secret = ()

let serialize_client_session_state (gu:extended_global_usage) (i:timestamp) (l:label) (client_session:ba_example_st{is_valid_client_state gu i l client_session}) : (st:msg gu i l) =
  match client_session with
  | ClientSession username server password opt_secret opt_latest_get_secret_request_idx opt_stored_sym_key->
    let password:msg gu i l = password in
    let username_and_server = concat #gu #i #l (string_to_bytes #gu #i username) (string_to_bytes #gu #i server) in
    let username_and_server_and_password = concat #gu #i #l username_and_server password in
    match opt_secret, opt_latest_get_secret_request_idx, opt_stored_sym_key with
    | None, None, None -> (
      concat #gu #i #l (string_to_bytes #gu #i "client.state.without.secret.without.send_idx.without.sym_key") username_and_server_and_password
      )
    | Some secret, None, None ->
      let username_and_server_and_password_and_secret = concat #gu #i #l username_and_server_and_password secret in
      concat #gu #i #l (string_to_bytes #gu #i "client.state.with.secret.without.send_idx.without.sym_key") username_and_server_and_password_and_secret
    | None, Some send_idx, None ->
      let username_and_server_and_password_and_send_idx = concat #gu #i #l username_and_server_and_password (nat_to_bytes #gu #i 0 send_idx) in
      concat #gu #i #l (string_to_bytes #gu #i "client.state.without.secret.with.send_idx.without.sym_key") username_and_server_and_password_and_send_idx
    | Some secret, Some send_idx, None ->
      let username_and_server_and_password_and_secret = concat #gu #i #l username_and_server_and_password secret in
      let username_and_server_and_password_and_secret_and_send_idx = concat #gu #i #l username_and_server_and_password_and_secret (nat_to_bytes #gu #i 0 send_idx) in
      concat #gu #i #l (string_to_bytes #gu #i "client.state.with.secret.with.send_idx.without.sym_key") username_and_server_and_password_and_secret_and_send_idx
    | None, None, Some sym_key -> (
      let username_and_server_and_password_and_sym_key = concat #gu #i #l username_and_server_and_password sym_key in
      concat #gu #i #l (string_to_bytes #gu #i "client.state.without.secret.without.send_idx.with.sym_key") username_and_server_and_password_and_sym_key
      )
    | None, Some send_idx, Some sym_key ->
      let username_and_server_and_password_and_send_idx = concat #gu #i #l username_and_server_and_password (nat_to_bytes #gu #i 0 send_idx) in
      let username_and_server_and_password_and_send_idx_and_sym_key = concat #gu #i #l username_and_server_and_password_and_send_idx sym_key in
      concat #gu #i #l (string_to_bytes #gu #i "client.state.without.secret.with.send_idx.with.sym_key") username_and_server_and_password_and_send_idx_and_sym_key

let parse_client_session_state (st:bytes) : (result:option ba_example_st{Some? result ==> (let result_state = Some?.v result in ClientSession? result_state)}) =
  match CryptoLib.split st with
  | Error _ -> None
  | Success (state_tag, state_payload) -> (
     match CryptoLib.bytes_to_string state_tag with
     | Success "client.state.without.secret.without.send_idx.without.sym_key" -> (
       match CryptoLib.split state_payload with
       | Error _ -> None
       | Success (username_server_bytes, password) -> (
         match CryptoLib.split username_server_bytes with
         | Error _ -> None
         | Success (username_bytes, server_bytes) -> (
           match CryptoLib.bytes_to_string username_bytes, CryptoLib.bytes_to_string server_bytes with
           | Success username, Success server -> Some (ClientSession username server password None None None)
           | _,_ -> None
         )
       )
     )
     | Success "client.state.with.secret.without.send_idx.without.sym_key" -> (
       match CryptoLib.split state_payload with
       | Error _ -> None
       | Success (username_server_password, secret) -> (
         match CryptoLib.split username_server_password with
         | Error _ -> None
         | Success (username_server, password) -> (
           match CryptoLib.split username_server with
           | Error _ -> None
           | Success (username_bytes, server_bytes) -> (
             match CryptoLib.bytes_to_string username_bytes, CryptoLib.bytes_to_string server_bytes with
             | Success username, Success server -> Some (ClientSession username server password (Some secret) None None)
             | _,_ -> None
           )
         )
       )
     )
     | Success "client.state.without.secret.with.send_idx.without.sym_key" -> (
       match CryptoLib.split state_payload with
       | Error _ -> None
       | Success (username_server_password, send_idx_bytes) -> (
         match CryptoLib.split username_server_password with
         | Error _ -> None
         | Success (username_server, password) -> (
           match CryptoLib.split username_server with
           | Error _ -> None
           | Success (username_bytes, server_bytes) -> (
             match CryptoLib.bytes_to_string username_bytes, CryptoLib.bytes_to_string server_bytes, CryptoLib.bytes_to_nat send_idx_bytes with
             | Success username, Success server, Success send_idx -> Some (ClientSession username server password None (Some send_idx) None)
             | _,_,_ -> None
           )
         )
       )
     )
     | Success "client.state.with.secret.with.send_idx.without.sym_key" -> (
       match CryptoLib.split state_payload with
       | Error _ -> None
       | Success (username_server_password_secret, send_idx_bytes) -> (
         match CryptoLib.split username_server_password_secret with
         | Error _ -> None
         | Success (username_server_password, secret) -> (
           match CryptoLib.split username_server_password with
           | Error _ -> None
           | Success (username_server, password) -> (
             match CryptoLib.split username_server with
             | Error _ -> None
             | Success (username_bytes, server_bytes) -> (
                     match CryptoLib.bytes_to_string username_bytes, CryptoLib.bytes_to_string server_bytes, CryptoLib.bytes_to_nat send_idx_bytes with
                     | Success username, Success server, Success send_idx -> Some (ClientSession username server password (Some secret) (Some send_idx) None)
                     | _,_,_ -> None
             )
           )
         )
       )
     )
     | Success "client.state.without.secret.without.send_idx.with.sym_key" -> (
         match CryptoLib.split state_payload with
         | Error _ -> None
         | Success (username_server_bytes_and_password, sym_key) -> (
           match CryptoLib.split username_server_bytes_and_password with
           | Error _ -> None
           | Success (username_server_bytes, password) -> (
             match CryptoLib.split username_server_bytes with
             | Error _ -> None
             | Success (username_bytes, server_bytes) -> (
               match CryptoLib.bytes_to_string username_bytes, CryptoLib.bytes_to_string server_bytes with
               | Success username, Success server -> Some (ClientSession username server password None None (Some sym_key))
               | _,_ -> None
             )
           )
       )
     )
     | Success "client.state.without.secret.with.send_idx.with.sym_key" -> (
         match CryptoLib.split state_payload with
         | Error _ -> None
         | Success (username_server_bytes_and_password_send_idx_bytes, sym_key) -> (
           match CryptoLib.split username_server_bytes_and_password_send_idx_bytes with
           | Error _ -> None
           | Success (username_server_password, send_idx_bytes) -> (
             match CryptoLib.split username_server_password with
             | Error _ -> None
             | Success (username_server, password) -> (
               match CryptoLib.split username_server with
               | Error _ -> None
               | Success (username_bytes, server_bytes) -> (
                 match CryptoLib.bytes_to_string username_bytes, CryptoLib.bytes_to_string server_bytes, CryptoLib.bytes_to_nat send_idx_bytes with
                 | Success username, Success server, Success send_idx -> Some (ClientSession username server password None (Some send_idx) (Some sym_key))
                 | _,_,_ -> None
               )
             )
           )
         )
     )
     | _ -> None
  )

let parse_serialize_client_session_state_lemma gu i l username server password opt_secret opt_latest_get_secret_request_idx opt_sym_key = ()

let parsed_server_state_cannot_be_parsed_by_client st = ()

let parsed_client_state_cannot_be_parsed_by_server st = ()
