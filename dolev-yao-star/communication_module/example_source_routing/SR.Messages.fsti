/// SR.Messages
/// ===========

module SR.Messages
open SecrecyLabels
open CryptoLib
open Communication.Layer

(*! Message Type *)

(**
  [Msg] is a normal message, used for confidential-only send.

  For showing path integrity, we add a counter to the message indicating the position within the
  list (used for authenticated send).

  When sending the first message, the initiator sets the counter to 0. 
  Thus, when receiving a message with value [counter], the following holds true:
    principal_list[counter] = sender of the message
    principal_list[counter + 1] = receiver
    principal_list[counter + 2] = next principal to send the nonce to
*)
noeq type message =
  | Msg: l:list principal -> nonce: bytes -> message
  | MsgWithCounter: l:list principal -> counter:nat -> nonce: bytes -> message



(*! (raw) Serializing and Parsing*)


(** Helper functions for list of principals  *)

(** Parse function for list of principals. *)
val parse_list_of_principals: b:bytes -> Tot (result (list principal))
  (decreases (term_depth b))

(** Serialize function for list of principals returning a byte. This is used for defining events. *)
val serialize_list_of_principals_raw: list principal -> bytes



(**
    This function parses bytes and is used within the confidential send predicate.  Once
    the predicate is defined, we can define instance of the predicate container of this
    (application) layer, and then we can instantiate the [msg] type with the global usage
    (Communication.Sessions.send_preds sr_preds).LabeledRuntimeAPI.global_usage. We then define the
    [parse_msg] function which takes bytes that are of the corresponding [msg] type.
*)
val parse_msg_raw: bytes -> result message

val serialize_msg_raw: message ->  bytes
