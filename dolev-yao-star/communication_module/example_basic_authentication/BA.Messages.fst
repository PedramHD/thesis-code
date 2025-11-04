/// BA.Messages (implementation)
/// ===============================
module BA.Messages

let parse_msg_raw b =
  match split b with
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
    | Success "Msg_Tag_Get_Secret_Resp" -> Success (GetSecretResp part_2)
    | Success _ -> Error "[parse_msg or parse_msg_raw]: wrong message tag"
  )
