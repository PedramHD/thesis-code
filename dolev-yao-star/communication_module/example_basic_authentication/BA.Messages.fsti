/// BA.Messages
/// ==============

module BA.Messages
open SecrecyLabels
open CryptoLib


(**
    In this example, the initiator first sends a request (containing a password) to the responder to
    create an account [GenerateAccountReq].
    When creating the account, the responder also creates a secret value.
    After this is done, the initiator can send the password and retrieve the secret [GetSecretReq].
    For each request we have a corresponding response message type
*)

noeq type message =
  | GenerateAccountReq: password:bytes -> message
  | GenerateAccountResp: status:string -> message
  | GetSecretReq:  password:bytes -> message
  | GetSecretResp: secret:bytes -> message


(**
    This function parses bytes and is used within the request and response send predicates.
    Once the predicate is defined, we can define instance of the predicate container of this
    (application) layer, and then we can instantiate the [msg] type with the global usage
    (Communication.Sessions.send_preds ba_preds).LabeledRuntimeAPI.global_usage. We then define the
    [parse_msg] function which takes bytes that are of the corresponding [msg] type.
*)
val parse_msg_raw: b:bytes -> result message
