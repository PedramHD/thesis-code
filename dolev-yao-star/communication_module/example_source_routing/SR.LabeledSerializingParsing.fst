/// SR.LabeledserializingParsing (Implementation)
/// =============================================

module SR.LabeledSerializingParsing

friend SR.Messages
open SR.Preds
open Communication.Layer
module C = CryptoLib

let parse_msg (#gu:extended_global_usage) (#i:timestamp) (#l:label) (m: msg gu i l) : (r:result message{r == parse_msg_raw m}) =
  match split m with
  | Success (part_1, nonce) ->  (
     match parse_list_of_principals part_1 with
     | Success principal_list ->  Success (Msg principal_list nonce)
     | Error e -> (
        match split part_1 with
        | Success (counter_bytes, principal_list_bytes) -> (
          match bytes_to_nat counter_bytes with
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
  | Error _ -> Error ("[parse_msg or parse_msg_raw]: Message is neither a [Msg] nor a [MsgWithCounter]: cannot split the message"
  )



let rec serialize_list_of_principals i l =
  match List.Tot.length l with
  | 0 -> string_to_bytes #gu #i ""
  | _ -> let hd::tl = l in
        concat
          #gu
          #i
          #public
          (string_to_bytes #gu #i hd)
          (serialize_list_of_principals i tl)


let serialize_msg i l m =
  match m with
  | Msg principal_list nonce -> (
    let result =concat #gu #i #l (serialize_list_of_principals i principal_list) nonce in
    result
  )
  | MsgWithCounter principal_list counter nonce -> (
    // 1. concat principal_list and counter:
    let counter_and_principal_list = concat #gu #i #l (nat_to_bytes #gu #i 0 counter) (serialize_list_of_principals i principal_list) in
    // 2. concat with the nonce:
    let result = concat #gu #i #l counter_and_principal_list nonce in
    result
  )



let rec serialize_list_of_principals_raw_lemma #i principal_list =
  match List.Tot.length principal_list with
  | 0 -> assert(string_to_bytes "" == string_to_bytes #gu #i "")
  | _ -> let hd::tl = principal_list in
        serialize_list_of_principals_raw_lemma #i tl

let parse_list_of_principals_of_empty_string_creates_empty_list () :
  Lemma (ensures (parse_list_of_principals (C.string_to_bytes "") = Success []))
  =
    let b = (C.string_to_bytes "") in
    concat_split_lemma b;
    concat_not_equal_string_to_bytes_lemma ()

let rec parse_serialize_list_of_principals_lemma i principal_list =
  match List.Tot.length principal_list with
  | 0 -> (
     assert(principal_list = []);
     assert(serialize_list_of_principals i [] = C.string_to_bytes "");
     let b = C.string_to_bytes "" in
     parse_list_of_principals_of_empty_string_creates_empty_list ();
     assert(parse_list_of_principals b = Success [])
  )
  | _ -> let hd::tl = principal_list in parse_serialize_list_of_principals_lemma i tl


let rec parse_serialize_list_of_principals_raw_lemma principal_list =
  match List.Tot.length principal_list with
  | 0 -> (
     assert(principal_list = []);
     assert(serialize_list_of_principals_raw [] = C.string_to_bytes "");
     let b = C.string_to_bytes "" in
     parse_list_of_principals_of_empty_string_creates_empty_list ();
     assert(parse_list_of_principals b = Success [])
  )
  | _ -> let hd::tl = principal_list in parse_serialize_list_of_principals_raw_lemma tl


#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let rec serialize_parse_list_of_principals_lemma i l b =
  match split b with
  | Success (principal_bytes, principal_list) -> (
    concat_split_lemma b;
    assert(b = concat principal_bytes principal_list);
    concat_not_equal_string_to_bytes_lemma ();
    assert(concat principal_bytes principal_list <> (C.string_to_bytes ""));
    match bytes_to_string principal_bytes with
    | Success p -> (
      match parse_list_of_principals principal_list with
      | Success p_list -> serialize_parse_list_of_principals_lemma i l principal_list;
                         bytes_to_string_lemma principal_bytes;
                         CryptoLib.bytes_to_string_lemma principal_bytes
      | Error e -> ()
    )
    | Error e -> ()
  )
  | Error e -> (
      match bytes_to_string b with
      | Success "" -> bytes_to_string_lemma b;
                     CryptoLib.bytes_to_string_lemma b

      | _ -> ()
  )
#pop-options


let parse_list_of_principals_nat_lemma input_bytes counter =
  let b = (CryptoLib.concat (C.nat_to_bytes 0 counter) input_bytes) in
  match C.split b with
  | Success (principal_bytes, principal_list) -> (
    match C.bytes_to_string principal_bytes with
    | Success p -> (
      bytes_to_string_of_nat_to_bytes_error counter;
      assert(Error? (C.bytes_to_string (C.nat_to_bytes 0 counter)))
    )
    | Error _ -> ()
  )


#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let parse_serialize_msg_lemma i l msg =
  match msg with
  | Msg principal_list nonce -> parse_serialize_list_of_principals_lemma i principal_list
  | MsgWithCounter principal_list counter nonce -> (
     parse_serialize_list_of_principals_lemma i principal_list;
     C.nat_to_bytes_lemma 0 counter;
     let counter_and_principal_list = CryptoLib.concat (C.nat_to_bytes 0 counter) (serialize_list_of_principals i principal_list) in
     let result = CryptoLib.concat counter_and_principal_list nonce in
     assert(result == serialize_msg i l msg);
     parse_list_of_principals_nat_lemma (serialize_list_of_principals i principal_list) counter
  )
#pop-options

let parse_serialize_msg_raw_lemma msg
  : Lemma ( Success msg == (parse_msg_raw (serialize_msg_raw msg )) )
= match msg with
  | Msg ps nonce -> parse_serialize_list_of_principals_raw_lemma ps
  | MsgWithCounter ps ctr nonce -> begin
      parse_serialize_list_of_principals_raw_lemma ps;
      parse_list_of_principals_nat_lemma (serialize_list_of_principals_raw ps) ctr
    end



let rec serialize_parse_list_of_principals_raw_lemma ps
  : Lemma (requires Success? (parse_list_of_principals ps))
     (ensures ps == serialize_list_of_principals_raw (Success?.v (parse_list_of_principals ps)))
       (decreases (term_depth ps))
  =  match C.split ps with
  | Success (principal_bytes, principal_list) -> (
    concat_split_lemma ps;
    assert(ps = C.concat principal_bytes principal_list);
    concat_not_equal_string_to_bytes_lemma ();
    assert(CryptoLib.concat principal_bytes principal_list <> (C.string_to_bytes ""));
    match CryptoLib.bytes_to_string principal_bytes with
    | Success p -> (
      match parse_list_of_principals principal_list with
      | Success p_list -> serialize_parse_list_of_principals_raw_lemma principal_list;
                         CryptoLib.bytes_to_string_lemma principal_bytes
      | Error e -> ()
    )
    | Error e -> ()
  )
  | Error e -> (
      match C.bytes_to_string ps with
      | Success "" ->
                   C.bytes_to_string_lemma ps;
                     CryptoLib.bytes_to_string_lemma ps

      | _ -> ()
  )


let serialize_parse_msg_raw_lemma m
  : Lemma
     (requires Success? (parse_msg_raw m))
     (ensures serialize_msg_raw (Success?.v (parse_msg_raw m)) == m)
= match C.split m with
  | Success (part_1, nonce) ->  (
     match parse_list_of_principals part_1 with
     | Success principal_list -> concat_split_lemma m; serialize_parse_list_of_principals_raw_lemma part_1
     | Error e -> (
        match C.split part_1 with
        | Success (counter_bytes, principal_list_bytes) -> (
          match C.bytes_to_nat counter_bytes with
          | Success counter -> (
            match parse_list_of_principals principal_list_bytes with
            | Success principal_list ->
                      assert(parse_msg_raw m == Success ( MsgWithCounter principal_list counter nonce));
                     concat_split_lemma m;
                     serialize_parse_list_of_principals_raw_lemma principal_list_bytes;
                     C.bytes_to_nat_lemma 0 counter_bytes
            | Error e -> ()
          )
          | Error e -> ()
        )
        | Error _ -> ()
     )
  )
  | Error _ -> ()

let parse_serialize_raw_msg_lemma m msg
= parse_serialize_msg_raw_lemma msg; serialize_parse_msg_raw_lemma m

