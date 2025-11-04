/// BA.SecurityLemmas
/// ====================
module BA.SecurityLemmas

open SecrecyLabels
open CryptoLib
open GlobalRuntimeLib
open CryptoEffect

module LC = LabeledCryptoAPI
open LabeledRuntimeAPI
open AttackerAPI

open LabeledPKI

open Communication.Layer

open BA.Messages
open BA.Sessions
open BA.Preds

open SecurityLemmas


(** This property states that the [secret_nonce] is stored in a client state of the [initiator] related to the [server] *)
val is_secret_in_initiator_state: (set_state_idx:nat) -> (version_vector:version_vec) -> (state_vector:state_vec) -> (state_session_idx:nat) -> (initiator:principal) -> (server:principal) -> (secret_nonce:bytes) -> Type0


(** The main secrecy property:
    A [secret_nonce] stored in a client state of an [initiator] related to a [server] is secret,
    as long as both parties are honest.

   This property follows immediately from the state invariant of a client session:
     label of [secret_nonce] is exactly [initiator, server]
*)
val secrecy_of_secret_initiator: (set_state_idx:nat) -> (version_vector:version_vec) -> (state_vector:state_vec) -> state_session_idx:nat -> initiator:principal -> server:principal -> secret_nonce:bytes ->
    LCrypto unit (pki (Communication.Layer.send_preds ba_preds))
    (requires (fun t0 ->
      (
        set_state_idx < trace_len t0 /\
        is_secret_in_initiator_state set_state_idx version_vector state_vector state_session_idx initiator server secret_nonce /\
        ~ ((corrupt_at (trace_len t0) (P initiator) \/ corrupt_at (trace_len t0) (P server)))
      )
     ))
    (ensures (fun t0 _ t1 -> t0 == t1 /\
       is_unknown_to_attacker_at (trace_len t0) secret_nonce
    ))
