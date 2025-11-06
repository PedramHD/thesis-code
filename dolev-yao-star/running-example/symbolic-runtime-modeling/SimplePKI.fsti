/// SimplePKI
/// ===========
///
/// This module is a simplified version of the LabeledPKI module for illustrating the running
/// example without using the Labeled Security API.

module SimplePKI

open SecrecyLabels
open CryptoEffect
open GlobalRuntimeLib
open CryptoLib

type session_st =
  | SigningKey: t:string -> secret_key:bytes -> session_st
  | VerificationKey: t:string -> peer:principal -> public_key:bytes -> session_st
  | DHPrivateKey: t:string -> secret_key:bytes -> session_st
  | DHPublicKey: t:string -> peer:principal -> public_key:bytes -> session_st
  | OneTimeDHPrivKey: t:string -> secret_key:bytes -> session_st
  | OneTimeDHPubKey: t:string -> peer:principal -> public_key:bytes -> session_st
  | DeletedOneTimeKey: t:string -> session_st
  | DecryptionKey: t:string -> secret_key:bytes -> session_st
  | EncryptionKey: t:string -> peer:principal -> public_key:bytes -> session_st
  | APP: st:bytes -> session_st

val parse_session_st (serialized_session:bytes) : result session_st


/// Stateful session API for PKI layer
/// ----------------------------------
let new_session_number (p:principal) :
  Crypto nat
  (requires fun t0 -> True)
  (ensures fun t0 r t1 -> t1 == t0) =
  let now = global_timestamp () in
  if now = 0 then 0 else
  match get_last_state_before (now - 1) p with
  | Some (i,v,st) -> Seq.length v
  | None -> 0

val new_session: p:principal -> si:nat -> vi:nat -> st:bytes ->
  Crypto unit
  (requires fun t0 -> True)
  (ensures fun t0 r t1 ->
    (
    match r with
    | Error _ -> trace_len t1 == trace_len t0
    | Success _ ->
    (exists (state_vec:state_vec) (vvec:version_vec) (app_state:bytes). state_was_set_at (trace_len t0) p vvec state_vec /\
        trace_len t1 == trace_len t0 + 1
    )
  )
  )

val update_session:   p:principal -> si:nat -> vi:nat -> st:bytes ->
  Crypto unit
  (requires fun t0 -> True)
  (ensures fun t0 r t1 ->
    match r with
    | Error _ ->  trace_len t1 == trace_len t0
    | Success _ -> trace_len t1 == trace_len t0 + 1
  )

val get_session: p:principal -> si:nat ->
  Crypto (vi:nat & bytes)
  (requires fun t0 -> True)
  (ensures fun t0 r t1 -> t1 == t0)

val find_session:
  p:principal -> f:(si:nat -> vi:nat -> st:bytes -> bool) ->
  Crypto (option (si:nat & vi:nat & bytes))
  (requires fun t0 -> True)
  (ensures fun t0 r t1 -> t1 == t0 /\
                       (match r with
                        | Error _ -> True
                        | Success None -> True
                        | Success (Some (|si,vi,st|)) -> f si vi st))


/// PKI-specific (stateful) APIs
/// ----------------------------

type key_type = | PKE | DH | SIG | OneTimeDH


// Returns session index (of the session which stores the private key)
val gen_private_key: p:principal -> kt:key_type -> t:string ->
    Crypto (priv_key_session_id:nat)
    (requires (fun t0 -> True))
    (ensures (fun t0 r t1 -> match r with
      | Error _ -> True
      | Success _ -> trace_len t1 = trace_len t0 + 2))

// Retrieve a private key for p, identified by its type and usage string. Returns the session index
// of the session in which the private key is stored, and of course the key itself.
val get_private_key:  p:principal -> kt:key_type -> t:string ->
    Crypto (si:nat & bytes)
    (requires (fun t0 -> True))
    (ensures (fun t0 _ t1 -> t0 == t1))

// Install public key of p (identified by type and usage string) at peer. Returns the session index
// at which the public key is stored in peer's state.
val install_public_key: p:principal -> peer:principal -> kt:key_type -> t:string ->
    Crypto nat
    (requires (fun t0 -> True))
    (ensures (fun t0 r t1 -> match r with | Error _ -> True | Success _ -> trace_len t1 = trace_len t0 + 1))

// Retrieve the public key or peer (identified by type and usage string) in p's state.
val get_public_key: p:principal -> peer:principal -> kt:key_type -> t:string ->
    Crypto bytes
    (requires (fun t0 -> True))
    (ensures (fun t0 pk t1 -> t0 == t1))
