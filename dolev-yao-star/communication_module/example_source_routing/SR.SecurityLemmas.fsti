/// SR.SecurityLemmas
/// ====================
module SR.SecurityLemmas

open SecrecyLabels
open CryptoLib
open GlobalRuntimeLib
open LabeledRuntimeAPI
open LabeledPKI
open AttackerAPI
open SR.HelperFunctions
open SR.Messages
open SR.Messages.Lemmas
open SR.Protocol
open SR.Preds
open SR.Events
open SecurityLemmas
open Communication.CryptoLib


val receiver_secrecy_lemma: i:nat -> receiver:principal -> principal_list:list principal -> secret_nonce:bytes ->
    LCrypto unit (pki (Communication.Layer.send_preds sr_preds))
    (requires (fun t0 -> i < trace_len t0 /\ did_event_occur_at i receiver (received_confidential principal_list secret_nonce) /\
      (forall p. List.Tot.mem p principal_list ==> ~ (corrupt_at (trace_len t0) (P p)))
     ))
    (ensures (fun t0 _ t1 -> t0 == t1 /\
       LabeledCryptoAPI.can_flow i (LabeledCryptoAPI.get_label key_usages secret_nonce) public \/
       is_unknown_to_attacker_at (trace_len t0) secret_nonce
    ))


(**
   Integrity property when using authenticated channels.

   When the last principal receives the message, it creates a "Finished_Authenticated" event, which
   contains the principal list and the nonce. If all the principals in the list are honest, then
   there was an "Initiate" event created by the first principal in the list with the
   same list and nonce.
*)
val authenticated_message_integrity: i:nat -> initiator:principal -> receiver:principal -> principal_list:list principal -> nonce:bytes -> counter:nat ->
    LCrypto unit (pki (Communication.Layer.send_preds sr_preds))
    (requires (fun t0 -> i < trace_len t0 /\
      List.Tot.Base.length principal_list > 0 /\
      List.Tot.hd principal_list = initiator /\
      did_event_occur_at i receiver (finished_authenticated principal_list nonce counter) /\
      (forall p. List.Tot.mem p principal_list ==> ~ (corrupt_at (trace_len t0) (P p)))
    ))
    (ensures (fun t0 _ t1 -> t0 == t1 /\
      did_event_occur_before i initiator (initiate initiator principal_list nonce)
    ))

(**
   Integrity property when using authenticated channels.

   When the last principal receives the message, it creates a "Finished_Authenticated" event, which
   contains the principal list and the nonce. If all the principals in the list are honest, then:

   (1) every principal in the list created a "Processed_Message" event, and
   (2) the order of the events corresponds to the order of the principals in the list.
*)
val authenticated_path_integrity: trace_idx:nat -> receiver:principal -> principal_list:list principal -> nonce:bytes -> counter:nat ->
    LCrypto unit (pki (Communication.Layer.send_preds sr_preds))
    (requires (fun t0 ->
      trace_idx < trace_len t0 /\
      did_event_occur_at trace_idx receiver (finished_authenticated principal_list nonce counter) /\
      (forall p. List.Tot.mem p principal_list ==> ~ (corrupt_at (trace_len t0) (P p)))
    ))
    (ensures (fun t0 _ t1 -> t0 == t1 /\ (
      counter = (List.Tot.Base.length principal_list - 1) /\

      // every principal in the list created a processed_authenticated_message event and sent a message 
      // with the list of principals and the nonce:
      ( forall (i:nat). (i <= counter) ==>
         (
           let p_i = List.Tot.Base.index principal_list i in
           exists (k_i m_i:timestamp). (k_i <= (trace_len t0)) /\ (did_event_occur_at k_i p_i (processed_authn_message principal_list nonce i))
             /\ (i > 0 ==> (let recv_msg = serialize_msg_raw (MsgWithCounter principal_list (i-1) nonce) in
             exists signed_msg verif_idx. Communication.Layer.is_authenticated_message_sent_at m_i verif_idx recv_msg signed_msg
             ))
         )
      ) /\

      // for every pair of principals p_i, p_j (with i < j being the position of the principals in
      // the list), if p_j triggered a processed_authenticated_message event, then p_i
      // previously triggered a processed_authenticated_message event
      // and in between these events a message with counter = j-1 was sent.
      (forall (k_j:timestamp) i j. (i < j) /\ (j <= List.Tot.Base.length principal_list - 1)  ==> (
        let p_i = List.Tot.Base.index principal_list i in
        let p_j = List.Tot.Base.index principal_list j in
        // principal_list = [..., p_i, ..., p_j, ...] and p_i triggered the processed_authenticated_message event prior to p_j:
        ( (k_j < trace_len t0 /\
          did_event_occur_at k_j p_j (processed_authn_message principal_list nonce j))
          ==> (exists (k_i m_j:timestamp). (k_i <= m_j) /\ (m_j <= k_j) /\ (did_event_occur_at k_i p_i (processed_authn_message principal_list nonce i))
                /\ ( let recv_msg = serialize_msg_raw (MsgWithCounter principal_list (j-1) nonce) in
                   exists signed_msg verif_idx. Communication.Layer.is_authenticated_message_sent_at m_j verif_idx recv_msg signed_msg
                  )
             )
        )
      ))
    )))


(**
   When the protocol run with authenticated+confidential channels is finished (i.e., whenever a
   principal triggers a "Finished_Confidential_Authenticated" event), the nonce cannot be derived by
   the attacker if all principals in the list are honest.
*)
val confidential_authenticated_receiver_secrecy_lemma: i:nat -> receiver:principal -> principal_list:list principal -> secret_nonce:bytes -> counter:nat ->
    LCrypto unit (pki (Communication.Layer.send_preds sr_preds))
    (requires (fun t0 -> i < trace_len t0 /\ did_event_occur_at i receiver (finished_confidential_authenticated principal_list secret_nonce counter) /\
      (forall p. List.Tot.mem p principal_list ==> ~ (corrupt_at (trace_len t0) (P p)))
     ))
    (ensures (fun t0 _ t1 -> t0 == t1 /\
             is_unknown_to_attacker_at (trace_len t0) secret_nonce
    ))


(**
   Integrity property when using confidential and authenticated channels.

   When the last principal receives the message, it creates a "Finished_Confidential_Authenticated"
   event, which contains the principal list and the nonce. If all the principals in the list are
   honest, then there was an "Initiate" event created by the first principal in the list with the
   same list and nonce.
*)
val confidential_authenticated_message_integrity: i:nat -> initiator:principal -> receiver:principal -> principal_list:list principal -> secret_nonce:bytes -> counter:nat ->
    LCrypto unit (pki (Communication.Layer.send_preds sr_preds))
    (requires (fun t0 -> i < trace_len t0 /\
      List.Tot.Base.length principal_list > 0 /\
      List.Tot.hd principal_list = initiator /\
      did_event_occur_at i receiver (finished_confidential_authenticated principal_list secret_nonce counter) /\
      (forall p. List.Tot.mem p principal_list ==> ~ (corrupt_at (trace_len t0) (P p)))
    ))
    (ensures (fun t0 _ t1 -> t0 == t1 /\
      did_event_occur_before i initiator (initiate initiator principal_list secret_nonce)
    ))


(**
   Integrity property when using confidential and authenticated channels.

   When the last principal receives the message, it creates a "Finished_Confidential_Authenticated"
   event, which contains the principal list and the nonce. If all the principals in the list are
   honest, then:

   (1) every principal in the list created a "Processed_Message" event, and
   (2) the order of the events corresponds to the order of the principals in the list.
*)
val confidential_authenticated_path_integrity: trace_idx:nat -> receiver:principal -> principal_list:list principal -> secret_nonce:bytes -> counter:nat ->
    LCrypto unit (pki (Communication.Layer.send_preds sr_preds))
    (requires (fun t0 ->
      trace_idx < trace_len t0 /\
      did_event_occur_at trace_idx receiver (finished_confidential_authenticated principal_list secret_nonce counter) /\
      (forall p. List.Tot.mem p principal_list ==> ~ (corrupt_at (trace_len t0) (P p)))
    ))
    (ensures (fun t0 _ t1 -> t0 == t1 /\ (
      counter = (List.Tot.Base.length principal_list - 1) /\

      // every principal in the list created a processed_confidential_authenticated_message event with the list of principals and the nonce:
      ( forall (i:nat). (i <= counter) ==>
         (
           let p_i = List.Tot.Base.index principal_list i in
           exists (k_i m_i:timestamp). (k_i <= (trace_len t0)) 
             /\ (did_event_occur_at k_i p_i (processed_authnconf_message principal_list secret_nonce i))
             /\ (i > 0 ==> (let recv_msg = serialize_msg_raw (MsgWithCounter principal_list (i-1) secret_nonce) in
                          Communication.Layer.is_authenticated_confidential_message_sent_at m_i recv_msg
             ))
         )
      ) /\

      // for every pair of principals p_i, p_j (with i < j being the position of the principals in
      // the list), if p_j triggered a processed_confidential_authenticated_message event, then p_i
      // previously triggered a processed_confidential_authenticated_message event.
      (forall (k_j:timestamp) i j. (i < j) /\ (j < List.Tot.Base.length principal_list)  ==> (
        let p_i = List.Tot.Base.index principal_list i in
        let p_j = List.Tot.Base.index principal_list j in
        // principal_list = [..., p_i, ..., p_j, ...] and p_i triggered the processed_confidential_authenticated_message event prior to p_j:
        ( (k_j < trace_len t0 /\
          did_event_occur_at k_j p_j (processed_authnconf_message principal_list secret_nonce j))
          ==> (exists (k_i m_j:timestamp). (k_i <= m_j) /\ (m_j <= k_j) /\ (did_event_occur_at k_i p_i (processed_authnconf_message principal_list secret_nonce i))
                /\ ( let recv_msg = serialize_msg_raw (MsgWithCounter principal_list (j-1) secret_nonce) in
                    Communication.Layer.is_authenticated_confidential_message_sent_at m_j recv_msg
                  )
             )
        )
      ))
    )))
