/// BA.Sessions
/// ==============

module BA.Sessions

open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib
module A = LabeledCryptoAPI
module LAPI = LabeledRuntimeAPI
module LPKI = LabeledPKI
open Communication.Layer

(*! State Types *)

(** we define a session type for a server and a client *)
noeq type ba_example_st =
  | ServerAccountSession:
      password:bytes -> // the password received in an account registration request
      secret:bytes -> // the secret generated for the account related to [password]
      ba_example_st
  | ClientSession:
      username:string ->
      server:principal ->
      password:bytes -> // the password used in this session (i.e., for the account registration and access requests)
      secret:option bytes -> // the secret received in an access response (if any)
      latest_get_secret_request_idx: option nat -> // the index of the latest access request (if any)
                                                // This is used to check whether the access response matches the request.
      ba_example_st


(*! validity of labeled states *)

(* a server session is valid for label [l],
   if the [password] and [secret] can both flow to [l]
*)
let is_valid_server_state (gu:extended_global_usage) (i:timestamp) (l:label) (session_state:ba_example_st) =
  match session_state with
  | ServerAccountSession password secret -> is_msg gu i password l /\ is_msg gu i secret l
  | _ -> False

(* a client session is valid for label [l],
   if the [password] can flow to [l]
   and the [secret] is publishable (e.g., if one of [initiator] or [server] is corrupt)
   or it also flows to [l]
*)
let is_valid_client_state (gu:extended_global_usage) (i:timestamp) (l:label) (session_state:ba_example_st) =
  match session_state with
  | ClientSession username server password opt_secret opt_latest_get_secret_request_idx ->
                  is_msg gu i password l /\
                  (
                    Some? opt_secret ==>
                      ((A.corrupt_id i (P username) \/ A.corrupt_id i (P server)) /\ is_publishable gu i  (Some?.v opt_secret))
                      \/ (is_msg gu i (Some?.v opt_secret) l)
                  )
  | _ -> False

(*! state serialization/parsing functions for server*)

val serialize_server_session_state:
    (gu:extended_global_usage) ->
    (i:timestamp) ->
    (label_of_password:label) ->
    (server_session:ba_example_st{is_valid_server_state gu i label_of_password server_session}) ->
    (serialized_server_session:msg gu i label_of_password)


val parse_server_session_state:
    (st:bytes) ->
    (result:option ba_example_st{Some? result ==> (let result_state = Some?.v result in ServerAccountSession? result_state)})


val parse_serialize_server_session_state_lemma: (gu:extended_global_usage) -> (i:timestamp) -> (l:label) -> (password:bytes) -> (secret:bytes) ->
  Lemma
  (requires (
    is_valid_server_state gu i l (ServerAccountSession password secret)
  ))
  ( ensures (
    match parse_server_session_state (serialize_server_session_state gu i l (ServerAccountSession password secret)) with
    | Some (ServerAccountSession parsed_password  parsed_secret) ->  parsed_password = password /\ parsed_secret = secret
    | _ -> False
  ))


(*! state serialize/parsing functions for client *)

val serialize_client_session_state:
    (gu:extended_global_usage) ->
    (i:timestamp) ->
    (l:label) ->
    (client_session:ba_example_st{is_valid_client_state gu i l client_session}) ->
    (st:msg gu i l)

val parse_client_session_state:
    (st:bytes) ->
    (result:option ba_example_st{Some? result ==> (let result_state = Some?.v result in ClientSession? result_state)})


val parse_serialize_client_session_state_lemma: (gu:extended_global_usage) -> (i:timestamp) -> (l:label) -> (username:string) -> (server:principal) -> (password:bytes) -> (opt_secret:option bytes) -> (opt_latest_get_secret_request_idx:option nat) ->
  Lemma
  (requires (
    is_valid_client_state gu i l (ClientSession username server password opt_secret opt_latest_get_secret_request_idx)
  ))
  ( ensures (
    match parse_client_session_state (serialize_client_session_state gu i l (ClientSession username server password opt_secret opt_latest_get_secret_request_idx)) with
    | Some (ClientSession parsed_username parsed_server parsed_password parsed_secret parsed_opt_request_idx) -> parsed_username = username /\ parsed_server = server /\ parsed_password = password /\ parsed_secret = opt_secret /\ parsed_opt_request_idx = opt_latest_get_secret_request_idx
    | _ -> False
  ))

val parsed_server_state_cannot_be_parsed_by_client: (st:bytes) ->
  Lemma
  (requires (Some? (parse_server_session_state st))
  )
  ( ensures (
    None? (parse_client_session_state st)
  ))

val parsed_client_state_cannot_be_parsed_by_server: (st:bytes) ->
  Lemma
  (requires (Some? (parse_client_session_state st))
  )
  ( ensures (
    None? (parse_server_session_state st)
  ))
