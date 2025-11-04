/// BA.Labeled.SerializingParsing
/// ================================

module BA.Labeled.SerializingParsing
open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib
module A = LabeledCryptoAPI
module LAPI = LabeledRuntimeAPI
module LPKI = LabeledPKI
open Communication.Layer

open BA.Messages
open BA.Sessions
open BA.Preds

(*! Messages *)


(* define conditions on the contents of labeled messages *)
let is_valid_message (i:nat) (m:message) (l:label) =
  match m with
  | GenerateAccountReq password
  | GetSecretReq password -> is_msg gu i password l
  | GenerateAccountResp status -> True
  | GetSecretResp encrypted_secret -> is_msg gu i encrypted_secret public


(* define a new type for labeled messages satisfying the above conditions *)
let valid_message (i:nat) (l:label) = m:message{is_valid_message i m l}

(* Parsing of a labeled message.
   The result is the same as the one of un-labeled parsing. *)
val parse_msg: (#gu:extended_global_usage) -> (#i:timestamp) -> (#l:label) -> (m: msg gu i l) -> (r:result message {r == parse_msg_raw m})


(**
    If the last message that contains the secret (GetSecretResp) is publishable,
    then the secret is publishable too.
*)
val secret_message_publishable_implies_secret_publishable: (#gu:extended_global_usage) -> (#i:timestamp) -> (#l:label) -> (m: msg gu i l) ->
  Lemma
  (requires (Success? (parse_msg m)))
  (ensures (
    match parse_msg m with
    | Success (GetSecretResp encrypted_secret) -> (is_publishable gu i m ==> is_publishable gu i encrypted_secret)
    | _ -> True
  ))


(** If the account generation request is publishable,
    then so is the password contained in it.
*)
val serialized_account_request_message_publishable_implies_password_publishable: (#gu:extended_global_usage) -> (#i:timestamp) -> (#l:label) -> (m: msg gu i l) ->
  Lemma
  (requires (Success? (parse_msg m)))
  (ensures (
    match parse_msg m with
    | Success (GenerateAccountReq password) -> is_publishable gu i m ==> is_publishable gu i password
    | _ -> True
  ))

(* the parsed password is correctly labeled *)
val serialized_account_request_message_valid_implies_password_valid: (#gu:extended_global_usage) -> (#i:timestamp) -> (#l:label) -> (m: msg gu i l) ->
  Lemma
  (requires (Success? (parse_msg m)))
  (ensures (
    match parse_msg m with
    | Success (GenerateAccountReq password) -> is_valid gu i password
    | _ -> True
  ))

(* the encrypted secret is correctly labeled *)
val serialized_secret_response_message_encrypted_secret_valid: (#gu:extended_global_usage) -> (#i:timestamp) -> (#l:label) -> (m: msg gu i l) ->
  Lemma
  (requires (Success? (parse_msg m)))
  (ensures (
    match parse_msg m with
    | Success (GetSecretResp encrypted_secret) -> is_valid gu i encrypted_secret
    | _ -> True
  ))

(** If the request can flow to label [l], then so can the password.
*)
val serialized_account_request_message_label_and_password_label: (#gu:extended_global_usage) -> (#i:timestamp) -> (#l:label) -> (m: msg gu i l) ->
  Lemma
  (requires (Success? (parse_msg m)))
  (ensures (
    match parse_msg m with
    | Success (GenerateAccountReq password)
    | Success (GetSecretReq password) -> A.can_flow i (A.get_label (gu.higher_layer_gu.key_usages) password) l
    | _ -> True
  ))


(**
    To return a byte of type [msg] (see the result type below), the password contained in the
    message needs to be of the same type, thus, we require the message to fulfil [is_valid_message].

    Intuitively, this means that if the password can flow to [l], then the overall serialized
    message can also flow to [l].
*)
val serialize_msg: i:nat -> l:label -> m:valid_message i l ->  msg gu i l

(** Parsing of a serialized message results in the message.
*)
val parse_serialize_msg_lemma: i:nat -> l:label -> msg:valid_message i l ->  Lemma (
  let msg:message = msg in
  Success msg == (parse_msg (serialize_msg i l msg ))
)


(*! States *)

(**
  The labeled version of [parse_client_session_state]
  with postconditions on the password and the secret:
  both flow to the same label as the state
*)
val parse_client_session_state_labeled:
    (i:nat) ->
    (l:label) ->
    (st:msg gu i l) ->
    (result:option ba_example_st{
       (result == parse_client_session_state st) /\
       (match result with
         | Some (ClientSession username server password opt_secret opt_latest_get_secret_request_idx opt_sym_key) ->
              is_msg gu i password l
            /\ (Some? opt_secret ==> is_msg gu i (Some?.v opt_secret) l)
         | _ -> True
       )
      })



(**
  Lemma stating that both client state parsing functions return the same value
*)
val parse_client_session_state_equals_parse_client_session_state_labeled: (i:nat) -> (l:label) -> (st:msg gu i l) ->
  Lemma
  (ensures (parse_client_session_state_labeled i l st == parse_client_session_state st))


(** The labeled version of [parse_server_session_state] returning a valid server state.
*)
val parse_server_session_state_labeled:
  (#i:nat) -> (#l:label) -> (#gu:extended_global_usage) -> (st:msg gu i l)
  -> (result:option ba_example_st{Some? result ==> is_valid_server_state gu i l (Some?.v result)})

(** Lemma showing that the labeled and un-labeled server state parsing functions return the same value
*)
val parse_server_session_state_labeled_equals_raw_parse_function: (#i:nat) -> (#l:label) -> (#gu:extended_global_usage) -> (st:msg gu i l) ->
  Lemma (ensures (
    parse_server_session_state_labeled #i #l #gu st == parse_server_session_state st
  ))
