/// SR.LabeledserializingParsing
/// ============================


module SR.LabeledSerializingParsing


open SecrecyLabels
open CryptoLib
open Communication.Layer

open SR.Messages
open SR.Preds


(* define conditions on the contents of labeled messages *)
let is_valid_message (i:nat) (m:message) (l:label) =
  match m with
  | Msg principal_list nonce -> is_msg gu i nonce l
  | MsgWithCounter principal_list counter nonce -> is_msg gu i nonce l

(* define a new type for labeled messages satisfying the above conditions *)
let valid_message (i:nat) (l:label) = m:message{is_valid_message i m l}


(* Parsing of a labeled message.
   The result is the same as the one of un-labeled parsing. *)
val parse_msg: (#gu:extended_global_usage) -> (#i:timestamp) -> (#l:label) -> (m: msg gu i l) -> (r:result message{r == parse_msg_raw m})



val serialize_list_of_principals: i:nat -> l:list principal -> (r:msg gu i public{r == serialize_list_of_principals_raw l})

(* Serializing a labeled message.
   The result is the same as the one of un-labeled serializing. *)
val serialize_msg: i:nat -> l:label -> m:valid_message i l ->  (r:msg gu i l{r == serialize_msg_raw m})


(*! Lemmas about serializing and parsing *)

(**
  [serialize_list_of_principals_raw] outputs the same as [serialize_list_of_principals].
*)
val serialize_list_of_principals_raw_lemma:
  (#i:nat) ->
  (principal_list:list principal) ->
  Lemma (ensures (serialize_list_of_principals_raw principal_list == serialize_list_of_principals i principal_list))


val parse_serialize_list_of_principals_lemma: i:nat -> principal_list:list principal ->
  Lemma (ensures (
    Success principal_list = parse_list_of_principals (serialize_list_of_principals i principal_list)
  ))


val parse_serialize_list_of_principals_raw_lemma: (principal_list:list principal) ->
  Lemma (ensures (
    Success principal_list = parse_list_of_principals (serialize_list_of_principals_raw principal_list)
  ))


val serialize_parse_list_of_principals_lemma: i:nat -> l:label -> b:msg gu i l ->
  Lemma (ensures(
    match parse_list_of_principals b with
    | Success list_of_principals -> b == serialize_list_of_principals i list_of_principals
    | _ -> True
  ))
  (decreases (term_depth b))




(**
  It is not possible to successfully apply the [parse_list_of_principals] function to the
  concatenation of a byte with a serialized natural number.
*)
val parse_list_of_principals_nat_lemma: (b:bytes) -> (counter:nat) ->
  Lemma (ensures (
    match parse_list_of_principals (CryptoLib.concat (CryptoLib.nat_to_bytes 0 counter) b) with
    | Success _ -> False
    | Error _ -> True
  ))




val parse_serialize_msg_lemma: i:nat -> l:label -> msg:valid_message i l ->  Lemma (
  let msg:message = msg in
  Success msg == (parse_msg (serialize_msg i l msg ))
)


val parse_serialize_raw_msg_lemma: (m: bytes) -> (msg: message) -> 
  Lemma (requires parse_msg_raw m == Success msg) (ensures m == serialize_msg_raw msg )
