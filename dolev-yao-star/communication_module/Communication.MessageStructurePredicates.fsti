/// Communication.MessageStructurePredicates
/// ========================================
///
/// This module defines helper predicates on the structure of messages.
module Communication.MessageStructurePredicates

open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib
module LC = LabeledCryptoAPI

(**
  The signed message must be publishable and contain the message and some tag. The signature
  verification must be successful (for some verification key of the sender).
*)
val is_authenticated_message:
  verify_index:nat ->
  message:bytes ->
  signed_message:bytes ->
  Type0

(**
  The confidential message must be a ciphertext created with some key.
*)
val is_confidential_message:
  message:bytes ->
  confidential_message:bytes ->
  Type0

val is_authenticated_confidential_message:
  message:bytes ->
  authn_conf_message:bytes ->
  Type0

(** True iff the entry at [trace_index] is a [Message] entry with the given sender, and if the
message added to the trace entry is an authenticated message. *)
val is_authenticated_message_sent_at:
  trace_index:nat ->
  verify_index:nat ->
  msg:bytes ->
  signed_msg:bytes ->
  Type0

(** True iff the entry at [trace_index] is a [Message] and if the message added to the trace entry
is a confidential message. *)
val is_confidential_message_sent_at:
  trace_index:nat ->
  msg:bytes ->
  confidential_msg:bytes ->
  Type0

(** True iff the entry at [trace_index] is a [Message] and if the message added to the trace entry
is an authenticated and confidential message. *)
val is_authenticated_confidential_message_sent_at:
  trace_index:nat ->
  msg:bytes ->
  Type0

let is_request_at_idx (request_payload:bytes) (request_send_idx:nat) (sym_key:bytes) =
  exists sender' receiver full_request.
    was_message_sent_at request_send_idx sender' receiver full_request /\
    (
      (
        let final_message = concat sym_key request_payload in
        is_confidential_message final_message full_request
      )
      \/
      (
        exists tag ad iv encrypted_message pub_enc_key rand.
        let enc_sym_key = pke_enc pub_enc_key rand sym_key in
        full_request = concat enc_sym_key (concat iv encrypted_message) /\
        encrypted_message = aead_enc sym_key iv (concat tag request_payload) ad
      )
      \/
      (
        exists key iv ad.
	full_request = aead_enc key iv (concat sym_key request_payload) ad
      )
      \/
      (
        exists rand pub_enc_key tag sender_bytes receiver_bytes.
	let final_message = concat sym_key request_payload in
	let enc_message = pke_enc pub_enc_key rand final_message in
	full_request = concat (concat sender_bytes (concat receiver_bytes enc_message)) tag
      )
    )


val is_request_at_idx_injective_forall: unit ->
  Lemma (forall (request_payload1:bytes) (request_payload2:bytes) (send_idx1:nat) (send_idx2:nat) (sym_key1:bytes) (sym_key2:bytes).
           (is_request_at_idx request_payload1 send_idx1 sym_key1 /\
            is_request_at_idx request_payload2 send_idx2 sym_key2 /\
            send_idx1 = send_idx2)
           ==>
           (
             request_payload1 == request_payload2 /\
             sym_key1 == sym_key2
           )
         )
