/// SR.Preds (Implementation)
/// =========================

module SR.Preds

open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib
module A = LabeledCryptoAPI
open Communication.Layer

open SR.HelperFunctions
open SR.Messages
open SR.Events

(*! Global Usage *)

let pke_pred (i:timestamp) (s:string) (pk:bytes) (m:bytes) = False
let aead_pred i s k m ad  = False
let sign_pred i s k m  = False
let mac_pred i s k m  = False


let sr_usage_preds : A.usage_preds = {
  A.can_pke_encrypt = pke_pred;
  A.can_aead_encrypt =  aead_pred;
  A.can_sign = sign_pred;
  A.can_mac = mac_pred
}


let sr_gu: A.global_usage = {
  A.usage_preds = sr_usage_preds;
  A.key_usages = A.default_key_usages
}


(*! Send Predicates *)

(**
   True, if there is a principal in the list that is corrupted at the given trace index and the nonce flows to public.
*)
let principal_in_list_corrupted_and_nonce_flows_to_public (trace_idx:timestamp) (principal_list:list principal) (nonce:bytes) =
    exists (p:principal). (List.Tot.mem p principal_list /\ A.corrupt_id trace_idx (P p) /\ A.can_flow trace_idx (A.get_label A.default_key_usages nonce) public)


(**
  When sending a message (Msg principal_list nonce) over a confidential channel, we want to ensure
  that only the principals in the list can access the nonce. Thus, we require the label to
  correspond exactly to this list. Note that it is not sufficient to require that the nonce can flow
  to these principals.
*)
let confidential_send_pred trace_idx m =
  match parse_msg_raw m with
  | Success (Msg principal_list nonce) -> (
     A.can_flow trace_idx (A.get_label A.default_key_usages nonce) public \/
    was_rand_generated_before trace_idx nonce (readers (create_id_list_from_principal_list principal_list)) (nonce_usage "SR.Secret")
  )
  | _ -> False // do not allow the message to be a MsgWithCounter


(**
  When sending out a message containing a principal list, a counter, and a nonce over an
  authenticated channel, then some principal in the list is corrupted (and the nonce flows to
  public), or:
    1. The initiator (the first principal in the list) created an [initiate] event for
       the same list of principals and the same nonce
    2. A [processed_message] event was previously triggered for the
       principal list, nonce, and counter value.

  When using an authenticated but not confidential channel, we cannot show secrecy, as the messages
  that will be sent over the network must be publishable. Hence, unlike the [confidential_send_pred]
  and [authenticated_confidential_send_pred], we cannot require that the label of the nonce
  corresponds exactly to the principal list.
*)
let authenticated_send_pred (trace_idx:timestamp) m =
  match parse_msg_raw m with
  | Success (MsgWithCounter principal_list counter nonce) -> (
    principal_in_list_corrupted_and_nonce_flows_to_public trace_idx principal_list nonce \/
    (
      List.Tot.Base.length principal_list > 0 /\
      counter < List.Tot.Base.length principal_list /\
      (
        let initiator = List.Tot.hd principal_list in
        did_event_occur_before trace_idx initiator (initiate initiator principal_list nonce) // (1)
      ) /\
      (did_event_occur_before trace_idx (List.Tot.Base.index principal_list counter) (processed_authn_message principal_list nonce counter) // (2)
      )
    )
  )
  | _ -> False


(**
  When sending out a message containing a principal list, a counter, and a nonce over an
  authenticated and confidential channel, then some principal in the list is corrupted (and the nonce
  flows to public), or:
    1. The label of the nonce corresponds exactly to the list of principals
    2. The initiator (the first principal in the list) created an [initiate] event for the same list
       of principals and the same nonce
    3. A [processed_message] event was previously triggered for the
       principal list, nonce, and counter value.
*)
let authenticated_confidential_send_pred (trace_idx:timestamp) m =
  match parse_msg_raw m with
  | Success (MsgWithCounter principal_list counter nonce) -> (
    principal_in_list_corrupted_and_nonce_flows_to_public trace_idx principal_list nonce \/
    (
      List.Tot.Base.length principal_list > 0 /\
      counter < List.Tot.Base.length principal_list /\
      was_rand_generated_before trace_idx nonce (readers (create_id_list_from_principal_list principal_list)) (nonce_usage "SR.Secret") /\ // (1)
      (
        let initiator = List.Tot.hd principal_list in
        did_event_occur_before trace_idx initiator (initiate initiator principal_list nonce) // (2)
      ) /\
      did_event_occur_before trace_idx (List.Tot.Base.index principal_list counter) (processed_authnconf_message principal_list nonce counter) // (3)
    )
  )
  | _ -> False


let request_send_pred (trace_idx:timestamp) m = False
let response_send_pred (trace_idx:timestamp) response request sym_key = False


let sr_send_function_preds:predicates_for_send_functions = {
  confidential_send_pred = confidential_send_pred;
  authenticated_send_pred = authenticated_send_pred;
  authenticated_confidential_send_pred = authenticated_confidential_send_pred;
  request_pred = request_send_pred;
  response_pred = response_send_pred;
}

(*! Extended Global Usage *)

let sr_extended_gu:extended_global_usage = {
  higher_layer_gu = sr_gu;
  send_function_predicates = sr_send_function_preds;
}

(*! State Invariant*)
(* The participants don't store anything, hence we don't allow to set sessions. *)
let session_st_inv (trace_idx:timestamp) (p:principal) (session_id:nat) (version_id:nat) (state:bytes) = False

(*! Event Predicate *)

let epred (i:timestamp) s e =
    match e with
    | ("Initiate",[principal_list_bytes;secret_nonce]) ->(
      match parse_list_of_principals principal_list_bytes with
      | Success principal_list -> True
      | _ -> False
    )
    | ("Received_Confidential",[principal_list_bytes;secret_nonce]) ->(
      match parse_list_of_principals principal_list_bytes with
      | Success principal_list -> (
       A.can_flow i (A.get_label sr_gu.A.key_usages secret_nonce) public \/
       was_rand_generated_before i secret_nonce (readers (create_id_list_from_principal_list principal_list)) (nonce_usage "SR.Secret")
      )
      | _ -> False
    )
    | ("Processed_AuthNConf_Message",[principal_list_bytes;secret_nonce;counter_bytes]) ->(
      match parse_list_of_principals principal_list_bytes, CryptoLib.bytes_to_nat counter_bytes with
      | Success principal_list, Success (counter:nat) -> (
        counter < List.Tot.length principal_list /\
        (
          principal_in_list_corrupted_and_nonce_flows_to_public i principal_list secret_nonce \/
          (
            (
              (**
                 The initiator can simply create the event. The other principals in the list have to
                 show that the previous principal in the list created a
                 [processed_message] event with (counter - 1).

                 Thus, whenever the second principal in the list gets the message (with counter 0),
                 the send predicate provides the guarantee that there is such
                 an event for counter 0. Thus, the second principal can create this event for counter
                 = 1, and, therefore, fulfils the [authenticated_confidential_send_pred]. This
                 continues until the last principal in the list creates this event.
               *)
              if(counter = 0) then True
              else (
                let previous_principal = List.Tot.Base.index principal_list (counter -1) in
                let recv_msg = serialize_msg_raw (MsgWithCounter principal_list (counter-1) secret_nonce) in
                exists (previous_ev_idx:timestamp) (previous_msg_idx:timestamp). 
                    (previous_ev_idx < previous_msg_idx) /\ (previous_msg_idx < i) 
                  /\ (did_event_occur_at previous_ev_idx previous_principal (processed_authnconf_message principal_list secret_nonce (counter - 1)))
                  /\ is_authenticated_confidential_message_sent_at previous_msg_idx recv_msg
              )
            )
          )
        )
      )
      | _ -> False
    )
    | ("Processed_AuthN_Message",[principal_list_bytes;secret_nonce;counter_bytes]) ->(
      match parse_list_of_principals principal_list_bytes, CryptoLib.bytes_to_nat counter_bytes with
      | Success principal_list, Success (counter:nat) -> (
        counter < List.Tot.length principal_list /\
        (
          principal_in_list_corrupted_and_nonce_flows_to_public i principal_list secret_nonce \/
          (
            (
              (**
                The initiator can simply create the event. The other principals in the list have to
                show that the previous principal in the list created a
                [processed_message] event with (counter - 1) and that there is a message with (counter - 1).

                Thus, whenever the second principal in the list gets the message (with counter 0),
                the send predicate provides the guarantee that there is such
                an event for counter 0. Thus, the second principal can create this event for counter
                = 1, and, therefore, fulfils the [authenticated_confidential_send_pred]. This
                continues until the last principal in the list creates this event.
              *)
              if(counter = 0) then True
              else (
                let previous_principal = List.Tot.Base.index principal_list (counter -1) in
                let recv_msg = serialize_msg_raw (MsgWithCounter principal_list (counter-1) secret_nonce) in
                exists (previous_ev_idx:timestamp) (previous_msg_idx:timestamp). 
                    (previous_ev_idx < previous_msg_idx) /\ (previous_msg_idx < i) 
                  /\ (did_event_occur_at previous_ev_idx previous_principal (processed_authn_message principal_list secret_nonce (counter - 1)))
                  /\ (exists signed_msg verif_idx. is_authenticated_message_sent_at previous_msg_idx verif_idx recv_msg signed_msg)
              )
            )
          )
        )
      )
      | _ -> False
    )
    | ("Finished_Confidential_Authenticated",[principal_list_bytes;secret_nonce;counter_bytes]) ->(
      match parse_list_of_principals principal_list_bytes, CryptoLib.bytes_to_nat counter_bytes with
      | Success principal_list, Success counter -> (
        let counter:nat = counter in
        (
        List.Tot.Base.length principal_list > 0 /\
        counter = (List.Tot.length principal_list - 1) /\
        counter <> 0 /\
        (
          principal_in_list_corrupted_and_nonce_flows_to_public i principal_list secret_nonce \/
          (
            was_rand_generated_before i secret_nonce (readers (create_id_list_from_principal_list principal_list)) (nonce_usage "SR.Secret") /\
            did_event_occur_before i (List.Tot.hd principal_list) (initiate (List.Tot.hd principal_list) principal_list secret_nonce) /\
            (
              // the principal that created the event is the last principal in the list (i.e., the final receiver of the nonce)
              let receiver = List.Tot.Base.index principal_list ((List.Tot.length principal_list) - 1) in
              s = receiver
            ) /\
            (
               let receiver = List.Tot.Base.index principal_list ((List.Tot.length principal_list) - 1) in
               exists (previous_ev_idx:timestamp). (previous_ev_idx <= i) /\ (did_event_occur_at previous_ev_idx receiver (processed_authnconf_message principal_list secret_nonce ((List.Tot.length principal_list) - 1)))
            )
          )
        )
        )
    )
    | _, _ -> False
    )
    | ("Finished_Authenticated",[principal_list_bytes;secret_nonce;counter_bytes]) ->(
      match parse_list_of_principals principal_list_bytes, CryptoLib.bytes_to_nat counter_bytes with
      | Success principal_list, Success counter -> (
        let counter:nat = counter in
        (
        List.Tot.Base.length principal_list > 0 /\
        counter = (List.Tot.length principal_list - 1) /\
        counter <> 0 /\
        (
          principal_in_list_corrupted_and_nonce_flows_to_public i principal_list secret_nonce \/
          (
            did_event_occur_before i (List.Tot.hd principal_list) (initiate (List.Tot.hd principal_list) principal_list secret_nonce) /\
            (
              // the principal that created the event is the last principal in the list (i.e., the final receiver of the nonce)
              let receiver = List.Tot.Base.index principal_list ((List.Tot.length principal_list) - 1) in
              s = receiver
            ) /\
            (
               let receiver = List.Tot.Base.index principal_list ((List.Tot.length principal_list) - 1) in
               exists (previous_ev_idx:timestamp). (previous_ev_idx <= i) /\ (did_event_occur_at previous_ev_idx receiver (processed_authn_message principal_list secret_nonce ((List.Tot.length principal_list) - 1)))
            )
          )
        )
        )
    )
    | _, _ -> False
    )
    | _ -> False


(*! Complete Set of Predicates *)

(** an instance of the predicates exposed by the communication layer *)
let sr_preds:send_layer_preds = {
  extended_higher_layer_gu = sr_extended_gu;
  epred = epred;
  session_st_inv = session_st_inv;
  session_st_inv_later = (fun (i:timestamp) (j:timestamp) (p:principal) (si:nat) (vi:nat) (st:bytes) -> ());
}

(* shorter names for commonly used usages *)
let gu = sr_preds.extended_higher_layer_gu // == sr_extended_gu
let key_usages = gu.higher_layer_gu.key_usages // == sr_gu.key_usages
