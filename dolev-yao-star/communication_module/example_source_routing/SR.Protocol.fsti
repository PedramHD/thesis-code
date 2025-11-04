/// SR.Protocol
/// =============

module SR.Protocol

open SecrecyLabels
open CryptoLib

open LabeledRuntimeAPI
module LPKI = LabeledPKI
module S = Communication.Layer

open SR.Preds



(**! Confidential-only Channels *)

(**
  The initiator gets a list of principals, then:
   - generates a nonce that is readable by these principals
   - determines the next principal to which it has to send the message
   - creates and serializes the message (Msg principal_list secret_nonce)
   - sends the message to the next principal using a confidential-only channel
   - triggers an [initiate] event
   - returns the index of the send event
*)
val confidential_initiator_send_msg: initiator:principal -> principal_list:list principal -> LCrypto (send_index:result nat) (LPKI.pki (Communication.Layer.send_preds sr_preds))
  (requires fun t0 -> List.Tot.length principal_list > 0 /\
                   List.Tot.hd principal_list = initiator)
  (ensures fun t0 _ t1 -> True)

(**
  Whenever a principal receives a message (over a confidential-only channel), it:
   - triggers a [received_confidential] event
   - determines the next principal to which it has to send the message
   - sends the received message to the next principal using a confidential-only channel
   - returns the index of the send event
*)
val confidential_receive_and_process_message: receiver:principal -> recv_idx:nat -> LCrypto (send_index:result nat) (LPKI.pki (Communication.Layer.send_preds sr_preds))
  (requires fun t0 -> True)
  (ensures fun t0 _ t1 -> True)

(**! Authenticated-only Channels *)

(**
  The initiator gets a list of principals, then:
   - generates a nonce that is public
   - creates and serializes the message (MsgWithcounter principal_list 0 nonce)
   - triggers an [initiate_authenticated] event
   - triggers a [processed_authenticated_message] event
   - sends the message to the next principal using an authenticated channel
   - returns the index of the send event

  As the principal sends the message over an authenticated, but not confidential channel, the nonce
  has to be public.
*)
val authenticated_initiator_send_msg: initiator:principal -> principal_list:list principal -> LCrypto (send_index:result nat) (LPKI.pki (Communication.Layer.send_preds sr_preds))
  (requires fun t0 -> List.Tot.length principal_list > 0 /\
                   List.Tot.hd principal_list = initiator)
  (ensures fun t0 _ t1 -> True)


(**
    If the counter reached the maximum value, the receiver creates a
    [processed_authenticated_message] and a [finished_authenticated]
    event.

    Otherwise, it
    - triggers a [processed_authenticated_message]
    - creates and serializes the message for the next principal
    - sends the serialized message to the next principal using an authenticated channel
    - returns the index of the send event
*)
val authenticated_receive_and_process_message: receiver:principal -> recv_idx:nat -> LCrypto (send_index:result nat) (LPKI.pki (Communication.Layer.send_preds sr_preds))
  (requires fun t0 -> True)
  (ensures fun t0 _ t1 -> True)


(**! Authenticated+Confidential Channels *)

(**
  The initiator gets a list of principals, then:
   - generates a nonce that is readable by these principals
   - creates and serializes the message (MsgWithcounter principal_list 0 secret_nonce)
   - triggers an [initiate] event
   - triggers a [processed_confidential_authenticated_message] event
   - sends the message to the next principal using an authenticated+confidential channel
   - returns the index of the send event
*)
val authenticated_confidential_initiator_send_msg: initiator:principal -> principal_list:list principal -> LCrypto (send_index:result nat) (LPKI.pki (Communication.Layer.send_preds sr_preds))
  (requires fun t0 -> List.Tot.length principal_list > 0 /\
                   List.Tot.hd principal_list = initiator)
  (ensures fun t0 _ t1 -> True)

(**
    If the counter reached the maximum value, the receiver creates a
    [processed_confidential_authenticated_message] and a [finished_confidential_authenticated]
    event.

    Otherwise, it
    - triggers a [processed_confidential_authenticated_message]
    - creates and serializes the message for the next principal
    - sends the serialized message to the next principal using an authenticated+confidential channel
    - returns the index of the send event
*)
val authenticated_confidential_receive_and_process_message: receiver:principal -> recv_idx:nat -> LCrypto (send_index:result nat) (LPKI.pki (Communication.Layer.send_preds sr_preds))
  (requires fun t0 -> True)
  (ensures fun t0 _ t1 -> True)
