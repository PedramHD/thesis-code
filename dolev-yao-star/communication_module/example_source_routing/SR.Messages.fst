/// SR.Messages (implementation)
/// =============================
module SR.Messages

module C = CryptoLib

let rec parse_list_of_principals b =
  match CryptoLib.split b with
  | Success (principal_bytes, principal_list) -> (
    concat_split_lemma b;
    match C.bytes_to_string principal_bytes with
    | Success p -> (
      assert(term_depth principal_list < term_depth b);
      match parse_list_of_principals principal_list with
      | Success p_list -> Success (p::p_list)
      | Error e -> Error ("SR.Messages: parse_list_of_principals: cannot parse tail of principal list: " ^ e)
    )
    | Error e -> Error ("SR.Messages: parse_list_of_principals: cannot parse first part of the principal list into a string: " ^ e)
  )
  | Error e -> (
    match C.bytes_to_string b with
    | Success "" -> Success []
    | _ -> Error ("SR.Messages: parse_list_of_principals: cannot parse first the input into a string: ")
  )

let rec serialize_list_of_principals_raw l =
  match List.Tot.length l with
  | 0 -> C.string_to_bytes ""
  | _ -> let hd::tl = l in
        C.concat (C.string_to_bytes hd) (serialize_list_of_principals_raw tl)

let parse_msg_raw b =
  match C.split b with
  | Success (part_1, nonce) ->  (
     match parse_list_of_principals part_1 with
     | Success principal_list ->  Success (Msg principal_list nonce)
     | Error e -> (
        match C.split part_1 with
        | Success (counter_bytes, principal_list_bytes) -> (
          match C.bytes_to_nat counter_bytes with
          | Success counter -> (
            match parse_list_of_principals principal_list_bytes with
            | Success principal_list -> Success (MsgWithCounter principal_list counter nonce)
            | Error e -> Error ("[parse_msg or parse_msg_raw]: Message is neither a [Msg] nor a [MsgWithCounter]: cannot parse principal list")
          )
          | Error e -> Error ("[parse_msg or parse_msg_raw]: Message is neither a [Msg] nor a [MsgWithCounter]: cannot parse counter")
        )
        | Error _ -> Error ("[parse_msg or parse_msg_raw]: Message is neither a [Msg] nor a [MsgWithCounter]")
     )
  )
  | Error _ -> Error ("[parse_msg or parse_msg_raw]: Message is neither a [Msg] nor a [MsgWithCounter]: cannot split the message")


let serialize_msg_raw m =
  match m with
  | Msg principal_list nonce -> (
    let result = C.concat (serialize_list_of_principals_raw principal_list) nonce in
    result
  )
  | MsgWithCounter principal_list counter nonce -> (
    // 1. concat principal_list and counter:
    let counter_and_principal_list = C.concat (C.nat_to_bytes 0 counter) (serialize_list_of_principals_raw principal_list) in
    // 2. concat with the nonce:
    let result = C.concat counter_and_principal_list nonce in
    result
  )

