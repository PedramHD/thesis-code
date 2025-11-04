/// Communication.CoreFunctions (Interface)
/// =======================================

module Communication.CoreFunctions

open SecrecyLabels
open CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI
open Communication.MessageStructurePredicates
open Communication.UsagePredicates
open Communication.Sessions
open Communication.Preds

module C = CryptoLib
module L = LabeledCryptoAPI


(**
  Create a signed message:
    1. Get a signing key of the sender (using the LabeledPKI module)
    2. Create a nonce (for the tag generation)
    3. Create the signature tag
    4. Create the final message by concatenating the original message with the tag
*)
val create_authn_message:
  #i:nat ->
  #higher_level_preds:send_layer_preds ->
  sender:principal ->
  receiver:principal ->
  message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) i (join (readers [P sender]) (readers [P receiver])) ->
  LCrypto (now:timestamp & signed_message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now public) (pki (send_preds higher_level_preds))
  (requires( fun t0 ->
    (i <= trace_len t0) /\
    (is_publishable ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) i message) /\
    higher_level_preds.extended_higher_layer_gu.send_function_predicates.authenticated_send_pred i message
  ))
  (ensures( fun t0 (|now, signed_msg|) t1 ->
    trace_len t0 = now /\
    trace_len t1 = trace_len t0 + 1 /\
    is_authenticated_message i message signed_msg
  ))


(**
  Given a signed message (created by [create_authn_message]), this function
    1. Gets a public verification key of the sender (using the LabeledPKI module)
    2. Splits the signed message into the original message and the signature tag
    3. Returns the original message if the signature verification was successful
*)
val process_authn_message:
  #now:nat ->
  #higher_level_preds:send_layer_preds ->
  sender:principal ->
  receiver:principal ->
  message_idx:timestamp ->
  signed_message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now public ->
  LCrypto (message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now (readers [P receiver])) (pki (send_preds higher_level_preds))
  (requires( fun t0 ->
    now = trace_len t0
  ))
  (ensures( fun t0 message t1 ->
    t0 == t1 /\
    now = trace_len t0 /\
    (exists (verify_idx:nat). is_authenticated_message verify_idx message signed_message) /\
    can_flow now (get_label higher_level_preds.extended_higher_layer_gu.higher_layer_gu.LabeledCryptoAPI.key_usages message) public /\
    (
      corrupt_id now (P sender) \/
      (exists j. later_than message_idx j /\ higher_level_preds.extended_higher_layer_gu.send_function_predicates.authenticated_send_pred j message)
    )
  ))

(**
  Create a confidential message:
    1. Get a public key of the sender (using the LabeledPKI module)
    2. Create a nonce (for the encryption)
    3. Create and return the ciphertext
*)
val create_conf_message:
  #i:nat ->
  #higher_level_preds:send_layer_preds ->
  sender:principal ->
  receiver:principal ->
  message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) i (join (readers [P sender]) (readers [P receiver])) ->
  LCrypto (now:timestamp & conf_message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now public) (pki (send_preds higher_level_preds))
  (requires( fun t0 ->
    (i <= trace_len t0) /\
    higher_level_preds.extended_higher_layer_gu.send_function_predicates.confidential_send_pred i message

  ))
  (ensures( fun t0 (|now, conf_message|) t1 ->
    is_confidential_message message conf_message /\
    is_publishable ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now conf_message /\
    trace_len t0 = now /\
    trace_len t1 = trace_len t0 + 1
  ))


(**
  Given a confidential message (created by [create_conf_message]), this function
    1. Gets a private decryption key of the receiver (using the LabeledPKI module)
    2. Decrypts the ciphertext and returns the plaintext
*)
val process_conf_message:
  #now:nat ->
  #higher_level_preds:send_layer_preds ->
  receiver:principal ->
  confidential_message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now public ->
  LCrypto (message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now (readers [P receiver])) (pki (send_preds higher_level_preds))
  (requires( fun t0 ->
    now = trace_len t0
  ))
  (ensures( fun t0 message t1 -> t0 == t1 /\
    is_confidential_message message confidential_message /\
    (
      is_publishable (send_preds higher_level_preds).LabeledRuntimeAPI.global_usage now message \/
      (exists j. later_than now j /\
        higher_level_preds.extended_higher_layer_gu.send_function_predicates.confidential_send_pred j message)
    )
  ))


(**
  Create an authenticated+confidential message:

  Given the payload [message], this function is implemented as follows (simplified for explanation):

  1. Concatenate the message with the sender: plaintext = (sender, message)
  2. Encrypt using the public key of the receiver: ciphertext = enc(plaintext, pke_key_receiver)
  3. Sign the ciphertext with the signing key of the sender: tag = sign(ciphertext, sig_key_sender)
  4. Return out the ciphertext and signature tag (concatenated)

  By adding the sender to the message, we can require in the encryption predicate that the payload
  [message] is readable by the sender. Thus, after successful decryption, we have the guarantee that
  either the payload is publishable, or it is readable by the sender.

  The signature predicate provides the guarantee that either the sender is corrupted, or the
  authenticated_confidential_send_pred holds true. As we know that the message is readable by the
  sender, it follows that the message can flow to public if the sender is corrupted.

  When sending a message, the sender needs to show that the message is readable by the receiver.
  The property that the message is publishable if the sender is corrupted is useful when, for
  example, the receiver needs to relay the message to another principal. Otherwise, the receiver
  would not be able to relay the message.
*)
val create_authn_conf_message:
  #i:nat ->
  #higher_level_preds:send_layer_preds ->
  sender:principal ->
  receiver:principal ->
  message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) i (join (readers [P sender]) (readers [P receiver])) ->
  LCrypto (now:timestamp & message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now public) (pki (send_preds higher_level_preds))
  (requires( fun t0 ->
    (i <= trace_len t0) /\
    (higher_level_preds.extended_higher_layer_gu.send_function_predicates.authenticated_confidential_send_pred i message)
  ))
  (ensures( fun t0 (|now, authn_conf_message|) t1 ->
    is_publishable ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now authn_conf_message /\
    trace_len t1 = now /\
    trace_len t1 = trace_len t0 + 2 /\
    is_authenticated_confidential_message message authn_conf_message
  ))


(**
  Given an authenticated+confidential message (created by [create_authn_conf_message]), this
  function returns the payload of the message.
*)
val process_authn_conf_message:
  #now:nat ->
  #higher_level_preds:send_layer_preds ->
  sender_in_trace_event:principal -> // the sender contained in the [Message] event
  receiver:principal ->
  message_idx:timestamp ->
  authn_conf_message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now public ->
  LCrypto (sender:principal & message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now (readers [P receiver])) (pki (send_preds higher_level_preds))
  (requires( fun t0 ->
    now = trace_len t0
  ))
  (ensures( fun t0 (|sender, message|) t1 -> t0 == t1 /\
    is_authenticated_confidential_message message authn_conf_message /\
    (sender_in_trace_event = sender) /\
    ((corrupt_id now (P sender) /\ can_flow now (get_label higher_level_preds.extended_higher_layer_gu.higher_layer_gu.LabeledCryptoAPI.key_usages message) public) \/
      (exists j. later_than message_idx j /\ higher_level_preds.extended_higher_layer_gu.send_function_predicates.authenticated_confidential_send_pred j message))
  ))



(**
  Create a (confidential) request:
    1. Get a public key of the sender (using the LabeledPKI module)
    2. Create a nonce (for the encryption)
    3. Create and return the ciphertext

    This function can be used for requests that contain a symmetric (aead) key.
*)
val create_conf_message_for_request_pke:
  #i:nat ->
  #higher_level_preds:send_layer_preds ->
  sender:principal ->
  receiver:principal ->
  message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) i (join (readers [P sender]) (readers [P receiver])) ->
  LCrypto (now:timestamp & conf_message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now public) (pki (send_preds higher_level_preds))
  (requires( fun t0 ->
    (i <= trace_len t0) /\
    (
    is_publishable ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) i message \/
    ( match split message with
      | Error _ -> False
      | Success (sym_key, payload) -> (
        let higher_layer_key_usages = higher_level_preds.extended_higher_layer_gu.higher_layer_gu.LabeledCryptoAPI.key_usages in
        (exists (real_sender real_receiver:string). was_rand_generated_before i sym_key (join (readers [P real_sender]) (readers [P real_receiver])) (aead_usage "AEAD.Symmetric_Send_Key") /\ can_flow i (get_label higher_layer_key_usages message) (join (readers [P real_sender]) (readers [P real_receiver]))) /\
        (exists j. j<=i /\ higher_level_preds.extended_higher_layer_gu.send_function_predicates.request_pred j payload) /\
        can_flow i (get_label higher_layer_key_usages payload) (get_label higher_layer_key_usages sym_key)
      )
     )
   )))
  (ensures( fun t0 (|now, conf_message|) t1 ->
    is_confidential_message message conf_message /\
    is_publishable ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now conf_message /\
    trace_len t0 = now /\
    trace_len t1 = trace_len t0 + 1
  ))


(**
  Given a request (created by [create_conf_message_for_request_pke]), this function
    1. Gets a private decryption key of the receiver (using the LabeledPKI module)
    2. Decrypts the ciphertext and returns the plaintext
*)
val process_conf_request_message_pke:
  #now:nat ->
  #higher_level_preds:send_layer_preds ->
  receiver:principal ->
  confidential_message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now public ->
  LCrypto (message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now (readers [P receiver])) (pki (send_preds higher_level_preds))
  (requires( fun t0 ->
    now = trace_len t0
  ))
  (ensures( fun t0 message t1 -> t0 == t1 /\
    is_confidential_message message confidential_message /\
    (
      is_publishable (send_preds higher_level_preds).LabeledRuntimeAPI.global_usage now message \/
      (
        match split message with
        | Error _ -> False
        | Success (sym_key, payload) -> (
          let higher_layer_key_usages = higher_level_preds.extended_higher_layer_gu.higher_layer_gu.LabeledCryptoAPI.key_usages in
          (exists (real_sender real_receiver:string). was_rand_generated_before now sym_key (join (readers [P real_sender]) (readers [P real_receiver])) (aead_usage "AEAD.Symmetric_Send_Key") /\ can_flow now (get_label higher_layer_key_usages message) (join (readers [P real_sender]) (readers [P real_receiver]))) /\
          (exists j. later_than now j /\ higher_level_preds.extended_higher_layer_gu.send_function_predicates.request_pred j payload) /\
          can_flow now (get_label higher_layer_key_usages payload) (get_label higher_layer_key_usages sym_key)
        )
      )
  )))

(**
  Create a authenticated confidential request:
    1. Get a public key of the sender (using the LabeledPKI module)
    2. Create a nonce (for the encryption)
    3. Create and return the ciphertext

    This function can be used for requests that contain a symmetric (aead) key.
*)
val create_auth_conf_message_for_request_pke:
  #i:nat ->
  #higher_level_preds:send_layer_preds ->
  sender:principal ->
  receiver:principal ->
  message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) i (join (readers [P sender]) (readers [P receiver])) ->
  LCrypto (now:timestamp & auth_conf_message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now public) (pki (send_preds higher_level_preds))
  (requires( fun t0 ->
    (i <= trace_len t0) /\
    (
    is_publishable ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) i message \/
    ( match split message with
      | Error _ -> False
      | Success (sym_key, payload) -> (
        let higher_layer_key_usages = higher_level_preds.extended_higher_layer_gu.higher_layer_gu.LabeledCryptoAPI.key_usages in
        (was_rand_generated_before i sym_key (join (readers [P sender]) (readers [P receiver])) (aead_usage "AEAD.Symmetric_Send_Key")) /\ 
	can_flow i (get_label higher_layer_key_usages message) (join (readers [P sender]) (readers [P receiver])) /\
        (exists j. j<=i /\ higher_level_preds.extended_higher_layer_gu.send_function_predicates.request_pred j payload) /\
        can_flow i (get_label higher_layer_key_usages payload) (get_label higher_layer_key_usages sym_key)
      )
     )
   )))
  (ensures( fun t0 (|now, auth_conf_message|) t1 ->
    now <= trace_len t1 /\
    (match split auth_conf_message with 
    | Error _ -> False
    | Success (auth_conf_message, tag) ->
      (match split auth_conf_message with 
      | Error _ -> False | Success (sender_bytes, r_ct) -> 
	(match split r_ct with
	| Error e -> False
	| Success (receiver_bytes, auth_conf_message) ->
	  is_confidential_message message auth_conf_message /\
	  is_publishable ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now auth_conf_message))
    )))


(**
  Given a request (created by [create_conf_message_for_request_pke]), this function
    1. Gets a private decryption key of the receiver (using the LabeledPKI module)
    2. Decrypts the ciphertext and returns the plaintext
*)
val process_auth_conf_request_message_pke:
  #now:nat ->
  #higher_level_preds:send_layer_preds ->
  sender:principal ->
  receiver:principal ->
  auth_conf_message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now public ->
  LCrypto (message:msg ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now (readers [P receiver])) (pki (send_preds higher_level_preds))
  (requires( fun t0 ->
    now = trace_len t0
  ))
  (ensures( fun t0 message t1 -> t0 == t1 /\
    (match split auth_conf_message with 
    | Error _ -> False
    | Success (auth_conf_message, tag) ->
      (match split auth_conf_message with 
      | Error _ -> False | Success (sender_bytes, r_ct) -> 
	(match split r_ct with
	| Error e -> False
	| Success (receiver_bytes, auth_conf_message) ->
	  is_confidential_message message auth_conf_message /\
	  is_publishable ((send_preds higher_level_preds).LabeledRuntimeAPI.global_usage) now auth_conf_message))
    ) /\
    (
      corrupt_id now (P sender) \/ is_publishable (send_preds higher_level_preds).LabeledRuntimeAPI.global_usage now message \/
      (
        match split message with
        | Error _ -> False
        | Success (sym_key, payload) -> (
          let higher_layer_key_usages = higher_level_preds.extended_higher_layer_gu.higher_layer_gu.LabeledCryptoAPI.key_usages in
          (was_rand_generated_before now sym_key (join (readers [P sender]) (readers [P receiver])) (aead_usage "AEAD.Symmetric_Send_Key")) /\ 
	  can_flow now (get_label higher_layer_key_usages message) (join (readers [P sender]) (readers [P receiver])) /\
          (exists j. later_than now j /\ higher_level_preds.extended_higher_layer_gu.send_function_predicates.request_pred j payload) /\
          can_flow now (get_label higher_layer_key_usages payload) (get_label higher_layer_key_usages sym_key)
        )
      )
  )))

