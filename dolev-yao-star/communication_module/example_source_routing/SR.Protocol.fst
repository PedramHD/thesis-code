/// SR.Protocol (implementation)
/// ==============================
module SR.Protocol

open GlobalRuntimeLib
module LCA = LabeledCryptoAPI

open Communication.CryptoLib

open SR.Messages
open SR.Messages.Lemmas
open SR.HelperFunctions
open SR.LabeledSerializingParsing
open SR.Events

#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let confidential_initiator_send_msg initiator principal_list =
  let (|t0, secret_nonce|) = S.rand_gen
    #sr_preds
    (readers (create_id_list_from_principal_list principal_list))
    (nonce_usage "SR.Secret") in
  let opt_next_principal = get_next_principal_in_list initiator principal_list in
  match opt_next_principal with
  | Some next_principal -> (

    assert(List.Tot.mem initiator principal_list);      // follows from [get_next_principal_in_list]
    assert(List.Tot.mem next_principal principal_list); // follows from [get_next_principal_in_list]

    nonce_flows_to_principals_contained_in_principal_list
      t0
      gu
      initiator
      next_principal
      secret_nonce principal_list;

    assert(is_msg gu t0 secret_nonce (readers [P initiator; P next_principal]));

    let message = Msg principal_list secret_nonce in
    let serialized_message = serialize_msg t0 (readers (create_id_list_from_principal_list principal_list)) message in

    parse_serialize_msg_lemma t0 (readers (create_id_list_from_principal_list principal_list)) message;
    assert(confidential_send_pred t0 serialized_message);
    assert(is_msg gu t0 serialized_message (readers [P initiator; P next_principal]));
    let trace_len_before_sending = GlobalRuntimeLib.global_timestamp () in

    // next, we show that the label of the serialized message can flow to the join label required by
    // the send function
    let (serialized_message:msg gu t0
      (readers [P initiator; P next_principal])) = serialized_message in
    LabeledCryptoAPI.can_flow_to_join_forall t0;
    assert(LCA.can_flow t0 (readers [P initiator; P next_principal]) (readers [P initiator]));
    assert(LCA.can_flow t0 (readers [P initiator; P next_principal]) (readers [P next_principal]));
    let (serialized_message:msg gu t0
      (join (readers [P initiator]) (readers [P next_principal]))) = serialized_message in

    let send_index = Communication.API.send #t0 #sr_preds initiator next_principal serialized_message Communication.API.Conf in

    let current_trace_len =  GlobalRuntimeLib.global_timestamp () in
    let ev = initiate initiator principal_list secret_nonce in
    parse_serialize_list_of_principals_lemma current_trace_len principal_list;
    assert(epred trace_len_before_sending initiator ev);
    S.trigger_event #sr_preds initiator ev;

    Success send_index
  )
  | None -> Error "[confidential_initiator_send_msg]: Initiator cannot determine the next principal."
#pop-options


#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let confidential_receive_and_process_message receiver recv_idx =
  let (|t0, _, received_serialized_msg|) = Communication.API.receive_i #sr_preds recv_idx receiver Communication.API.Conf in
  match parse_msg received_serialized_msg with
  | Error e -> Error ("[confidential_receive_and_process_message]: Receiver cannot parse the message: " ^ e)
  | Success received_msg -> (
    match received_msg with
    | Msg principal_list secret_nonce -> (

      assert(is_publishable gu t0 received_serialized_msg \/
        (exists j. later_than t0 j /\ confidential_send_pred j received_serialized_msg)
      ); // this follows from the confidential receive

      assert(is_publishable gu t0 received_serialized_msg \/
        (confidential_send_pred t0 received_serialized_msg)
      ); // this follows from the definition of [confidential_send_pred]

      assert(is_publishable gu t0 received_serialized_msg \/
        (
          LabeledCryptoAPI.can_flow t0 (LabeledCryptoAPI.get_label key_usages secret_nonce) public \/
          was_rand_generated_before t0 secret_nonce (readers (create_id_list_from_principal_list principal_list)) (nonce_usage "SR.Secret")
        )
      );
      parse_msg_preserves_is_publishable received_serialized_msg;

      assert(is_publishable gu t0 received_serialized_msg ==>
        LabeledCryptoAPI.can_flow t0 (LabeledCryptoAPI.get_label key_usages secret_nonce) public);
      assert(LabeledCryptoAPI.can_flow t0 (LabeledCryptoAPI.get_label key_usages secret_nonce) public \/
        was_rand_generated_before t0 secret_nonce (readers (create_id_list_from_principal_list principal_list)) (nonce_usage "SR.Secret"));

      parse_serialize_list_of_principals_lemma t0 principal_list;

      let ev = received_confidential principal_list secret_nonce in
      assert(
        match ev with
        | ("Received_Confidential",[principal_list_bytes;secret_nonce]) ->(
          match parse_list_of_principals principal_list_bytes with
          | Success principal_list' -> principal_list' == principal_list
          | _ -> False
        )
        | _ -> False
      );
      assert(epred t0 receiver ev);
      S.trigger_event #sr_preds receiver ev;

      let opt_next_principal = get_next_principal_in_list receiver principal_list in
      match opt_next_principal with
      | Some next_principal -> (
        assert(is_publishable gu t0 received_serialized_msg ==>
        LCA.can_flow t0 (LCA.get_label key_usages received_serialized_msg) (readers [P receiver; P next_principal]));
        assert(List.Tot.mem receiver principal_list);
        assert(List.Tot.mem next_principal principal_list);

        parse_msg_label_lemma received_serialized_msg receiver next_principal;

        assert(LabeledCryptoAPI.get_label key_usages secret_nonce == (readers (create_id_list_from_principal_list principal_list)) ==>
          LCA.can_flow t0 (LCA.get_label key_usages received_serialized_msg) (readers [P receiver; P next_principal]));

        assert(LCA.can_flow t0 (LCA.get_label key_usages received_serialized_msg) (readers [P receiver; P next_principal]));
        assert(is_msg gu t0 received_serialized_msg
          (readers [P receiver; P next_principal]));

        // next, we show that the label of the serialized message can flow to the join label required by
        // the send function
        let (received_serialized_msg:msg gu t0
          (readers [P receiver; P next_principal])) = received_serialized_msg in
        LCA.can_flow_to_join_forall t0;
        assert(LCA.can_flow t0 (readers [P receiver; P next_principal]) (readers [P receiver]));
        assert(LCA.can_flow t0 (readers [P receiver; P next_principal]) (readers [P next_principal]));
        let (received_serialized_msg:msg gu t0
          (join (readers [P receiver]) (readers [P next_principal]))) = received_serialized_msg in

        let send_index = Communication.API.send #t0 #sr_preds receiver next_principal received_serialized_msg Communication.API.Conf in
        Success send_index
      )
      | None -> Error "[confidential_receive_and_process_message]: Receiver cannot determine next principal"
    )
    | _ -> Error "[confidential_receive_and_process_message]: Not a [Msg] message"
  )
#pop-options


#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let authenticated_initiator_send_msg initiator principal_list =
 //create a public nonce (as the message will be sent over a non-confidential channel)
 let (|t0, nonce|) = Communication.API.rand_gen #sr_preds public (nonce_usage "SR.Secret") in
 if (List.Tot.Base.length principal_list <= 1) then
   Error "[authenticated_initiator_send_msg]: list of principals contains only one principal. Stop."
 else (
   let next_principal = List.Tot.Base.index principal_list 1 in // send the message to the second principal of the list
   assert(is_msg gu t0 nonce (readers [P initiator; P next_principal]));

   let message = MsgWithCounter principal_list 0 nonce in
   let serialized_message = serialize_msg t0 public message in

   let trace_len_before_sending = GlobalRuntimeLib.global_timestamp () in
   parse_serialize_msg_lemma t0 public message ;
   assert(is_publishable gu trace_len_before_sending nonce);
   assert(is_msg gu t0 serialized_message (readers [P initiator; P next_principal]));
   parse_serialize_list_of_principals_lemma trace_len_before_sending principal_list;

   // [initiate_authenticated] event
   let ev = initiate initiator principal_list nonce in
   assert(epred trace_len_before_sending initiator ev);
   S.trigger_event #sr_preds initiator ev;

   // [processed_authenticated_message] event
   let processed_ev = processed_authn_message principal_list nonce 0 in
   S.trigger_event #sr_preds initiator processed_ev;

   // send message over an authenticated channel
   let current_trace_len =  GlobalRuntimeLib.global_timestamp () in
   assert(authenticated_send_pred current_trace_len serialized_message);
   assert(is_publishable gu current_trace_len serialized_message);
   let send_index = Communication.API.send #current_trace_len #sr_preds initiator next_principal serialized_message Communication.API.AuthN in
   Success send_index
 )
#pop-options


#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let authenticated_receive_and_process_message receiver recv_idx =
  let (|t0, sender, received_serialized_msg|) = Communication.API.receive_i #sr_preds recv_idx receiver Communication.API.AuthN in
  assert(
   (is_publishable gu t0 received_serialized_msg) /\
   (LCA.corrupt_id t0 (P sender)  \/ (exists j. (later_than t0 j) /\ authenticated_send_pred j received_serialized_msg))); // post-condition of the authn receive
  match parse_msg received_serialized_msg with
  | Error e -> Error ("[authenticated_receive_and_process_message]: Receiver cannot parse the message: " ^ e)
  | Success (Msg principal_list nonce) -> Error "[authenticated_receive_and_process_message]: Received wrong message type"
  | Success (MsgWithCounter principal_list counter nonce) -> (
     if (not(List.Tot.mem sender principal_list)) then (
      error "SR.Protocol: authenticated_receive_and_process_message: sender is not in list of principals")
     else if (not(List.Tot.mem receiver principal_list)) then (
      error "SR.Protocol: authenticated_receive_and_process_message: receiver is not in list of principals")
     else (
      parse_msg_preserves_is_msg received_serialized_msg;
      parse_serialize_list_of_principals_lemma t0 principal_list;
      parse_msg_preserves_is_publishable received_serialized_msg;
      assert(is_valid gu t0 nonce);
      assert(List.Tot.mem sender principal_list);
      assert(
        is_publishable gu t0 received_serialized_msg
        ==> is_publishable gu t0 nonce
      );
      assert(
        (LCA.corrupt_id t0 (P sender) /\ is_publishable gu t0 received_serialized_msg)
        ==> (LCA.corrupt_id t0 (P sender) /\ is_publishable gu t0 nonce)
      );
      authn_send_pred_lemma t0 sender received_serialized_msg;
      assert(authenticated_send_pred t0 received_serialized_msg);
      assert(
        principal_in_list_corrupted_and_nonce_flows_to_public t0 principal_list nonce \/
        did_event_occur_before t0 (List.Tot.Base.index principal_list counter) (processed_authn_message principal_list nonce counter)
      );

      parse_serialize_raw_msg_lemma received_serialized_msg (MsgWithCounter principal_list counter nonce);
      // Counter Value:
      // principal_list[counter] = sender
      // principal_list[counter + 1] = receiver
      // principal_list[counter + 2] = next principal to send the nonce to

      if((counter + 2) > List.Tot.length principal_list) then Error "wrong counter"
      else if ((counter + 2) < List.Tot.length principal_list) then (
        // Send message to next principal in the list:
        let next_principal_in_list = List.Tot.Base.index principal_list (counter + 2) in
        let next_counter = (counter+1) in
        let message_for_next_principal = MsgWithCounter principal_list next_counter nonce in
        if (List.Tot.Base.index principal_list (counter + 1) <> receiver) then (
          error "SR.Protocol: authenticated_receive_and_process_message: receiver is not in list of principals"
        ) else (
          assert(List.Tot.mem receiver principal_list);
          assert(List.Tot.memP next_principal_in_list principal_list);
          assert(List.Tot.mem next_principal_in_list principal_list);
          assert(is_publishable gu t0 received_serialized_msg ==>
            LCA.can_flow t0 (LCA.get_label key_usages received_serialized_msg) (readers (create_id_list_from_principal_list principal_list)));
          assert(LCA.can_flow t0 (LCA.get_label key_usages nonce) public);
          let serialized_next_message = serialize_msg t0 public message_for_next_principal in
          parse_serialize_msg_lemma t0 public message_for_next_principal;
          parse_serialize_list_of_principals_lemma t0 principal_list;
          parse_msg_preserves_is_publishable received_serialized_msg;
          let processed_ev = processed_authn_message principal_list nonce next_counter in

          let previous_principal = List.Tot.Base.index principal_list (counter) in
          assert(
            (principal_in_list_corrupted_and_nonce_flows_to_public t0 principal_list nonce \/
            (exists (previous_ev_idx:timestamp) previous_msg_idx.
                 (previous_msg_idx < t0) /\ (previous_ev_idx < previous_msg_idx)
              /\ (did_event_occur_at previous_ev_idx previous_principal (processed_authn_message principal_list nonce counter))
              /\ (exists signed_msg verif_idx. Communication.Layer.is_authenticated_message_sent_at previous_msg_idx verif_idx received_serialized_msg signed_msg)
            )
            )
          );
          assert(epred t0 receiver processed_ev);
          S.trigger_event #sr_preds receiver processed_ev;
          let current_trace_len =  GlobalRuntimeLib.global_timestamp () in
          assert(later_than current_trace_len t0);
          assert((authenticated_send_pred t0 received_serialized_msg));
          authenticated_send_pred_holds_later t0 current_trace_len received_serialized_msg;
          assert((authenticated_send_pred current_trace_len received_serialized_msg));
          assert((authenticated_send_pred current_trace_len serialized_next_message));

          assert(LCA.can_flow current_trace_len (LCA.get_label key_usages nonce) public);
          assert(is_valid_message current_trace_len message_for_next_principal public);
          parse_serialize_msg_lemma current_trace_len public message_for_next_principal;
          assert(is_msg gu current_trace_len serialized_next_message public);
          parse_msg_label_lemma #current_trace_len #public serialized_next_message receiver next_principal_in_list;
          assert(is_msg gu current_trace_len serialized_next_message (readers [P receiver; P next_principal_in_list]));
          let send_index = Communication.API.send #current_trace_len #sr_preds receiver next_principal_in_list serialized_next_message Communication.API.AuthN in
          Success send_index

        )
      ) else (
        // the receiver is the last principal in the list and creates a [finished_confidential_authenticated] event
        assert((counter + 1) = (List.Tot.length principal_list) - 1);
        let last_principal_in_list = List.Tot.Base.index principal_list (counter + 1) in
        if (last_principal_in_list <> receiver) then Error "Reached max counter, but wrong receiver"
        else(

          //create a [processed_authenticated_message] event
          let processed_ev = processed_authn_message principal_list nonce (counter + 1) in
          assert(counter + 1 <> 0);
          assert(epred t0 receiver processed_ev);
          S.trigger_event #sr_preds receiver processed_ev;

          //create a [finished_authenticated] event
          let current_trace_len =  GlobalRuntimeLib.global_timestamp () in
          let finished_ev = finished_authenticated principal_list nonce (counter+1) in
          assert((authenticated_send_pred t0 received_serialized_msg));
          principal_in_list_corrupted_and_nonce_flows_to_public_later_forall current_trace_len principal_list nonce;
          assert(epred current_trace_len receiver finished_ev);
          S.trigger_event #sr_preds receiver finished_ev;

          Error "finished"
        )
      )
     )
  )
#pop-options

#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let authenticated_confidential_initiator_send_msg initiator principal_list =
 let (|t0, secret_nonce|) = S.rand_gen #sr_preds (readers (create_id_list_from_principal_list principal_list)) (nonce_usage "SR.Secret") in
 if (List.Tot.Base.length principal_list <= 1) then
   Error "[authenticated_confidential_initiator_send_msg]: list of principals contains only one principal. Stop."
 else (
   let next_principal = List.Tot.Base.index principal_list 1 in // send the message to the second principal of the list
   nonce_flows_to_principals_contained_in_principal_list
     t0
     gu
     initiator
     next_principal
     secret_nonce principal_list;
   assert(is_msg gu t0 secret_nonce (readers [P initiator; P next_principal]));

   let message = MsgWithCounter principal_list 0 secret_nonce in
   let serialized_message = serialize_msg t0 (readers (create_id_list_from_principal_list principal_list)) message in

   let trace_len_before_sending = GlobalRuntimeLib.global_timestamp () in
   parse_serialize_msg_lemma t0 (readers (create_id_list_from_principal_list principal_list)) message ;
   assert(is_msg gu t0 serialized_message (readers [P initiator; P next_principal]));
   parse_serialize_list_of_principals_lemma trace_len_before_sending principal_list;

   // [initiate] event
   let ev = initiate initiator principal_list secret_nonce in
   assert(epred trace_len_before_sending initiator ev);
   S.trigger_event #sr_preds initiator ev;

   // [processed_confidential_authenticated_message] event
   // we cannot trigger the event after sending the message, as we need to say in the
   // authenticated_confidential_send_pred that this event was triggered
   let processed_ev = processed_authnconf_message principal_list secret_nonce 0 in
   S.trigger_event #sr_preds initiator processed_ev;

   // send message over an authenticated+confidential channel
   let current_trace_len =  GlobalRuntimeLib.global_timestamp () in
   assert(authenticated_confidential_send_pred current_trace_len serialized_message);


    // next, we show that the label of the serialized message can flow to the join label required by
    // the send function
    let (serialized_message:msg gu t0
      (readers [P initiator; P next_principal])) = serialized_message in
    LabeledCryptoAPI.can_flow_to_join_forall t0;
    assert(LCA.can_flow t0 (readers [P initiator; P next_principal]) (readers [P initiator]));
    assert(LCA.can_flow t0 (readers [P initiator; P next_principal]) (readers [P next_principal]));
    let (serialized_message:msg gu t0
      (join (readers [P initiator]) (readers [P next_principal]))) = serialized_message in

   let send_index = Communication.API.send #current_trace_len #sr_preds initiator next_principal serialized_message Communication.API.AuthNConf in
   Success send_index
 )
#pop-options


#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let authenticated_confidential_receive_and_process_message receiver recv_idx =
  let (|t0, sender, received_serialized_msg|) = Communication.API.receive_i #sr_preds recv_idx receiver Communication.API.AuthNConf in
  assert( S.is_authenticated_confidential_message_sent_at recv_idx received_serialized_msg /\
  ((LCA.corrupt_id t0 (P sender) /\  is_publishable gu t0 received_serialized_msg) \/
   (exists j. (later_than t0 j) /\ authenticated_confidential_send_pred j received_serialized_msg))); // post-condition of the authn+conf receive
  match parse_msg received_serialized_msg with
  | Error e -> Error ("[authenticated_confidential_receive_and_process_message]: Receiver cannot parse the message: " ^ e)
  | Success (Msg principal_list secret_nonce) -> Error "[authenticated_confidential_receive_and_process_message]: Received wrong message type"
  | Success (MsgWithCounter principal_list counter secret_nonce) -> (
     if (not(List.Tot.mem sender principal_list)) then (
      error "SR.Protocol: authenticated_confidential_receive_and_process_message: sender is not in list of principals")
     else if (not(List.Tot.mem receiver principal_list)) then (
      error "SR.Protocol: authenticated_confidential_receive_and_process_message: receiver is not in list of principals")
     else (
      parse_msg_preserves_is_msg received_serialized_msg;
      parse_serialize_list_of_principals_lemma t0 principal_list;
      parse_msg_preserves_is_publishable received_serialized_msg;
      assert(is_valid gu t0 secret_nonce);
      assert(List.Tot.mem sender principal_list);
      assert(
        is_publishable gu t0 received_serialized_msg
        ==> is_publishable gu t0 secret_nonce
      );
      assert(
        (LCA.corrupt_id t0 (P sender) /\ is_publishable gu t0 received_serialized_msg)
        ==> (LCA.corrupt_id t0 (P sender) /\ is_publishable gu t0 secret_nonce)
      );
      authn_conf_send_pred_lemma t0 sender received_serialized_msg;
      assert(authenticated_confidential_send_pred t0 received_serialized_msg);
      assert(
        principal_in_list_corrupted_and_nonce_flows_to_public t0 principal_list secret_nonce \/
        did_event_occur_before t0 (List.Tot.Base.index principal_list counter) (processed_authnconf_message principal_list secret_nonce counter)
      );
      parse_serialize_raw_msg_lemma received_serialized_msg (MsgWithCounter principal_list counter secret_nonce);
      // Counter Value:
      // principal_list[counter] = sender
      // principal_list[counter + 1] = receiver
      // principal_list[counter + 2] = next principal to send the nonce to

      if((counter + 2) > List.Tot.length principal_list) then Error "wrong counter"
      else if ((counter + 2) < List.Tot.length principal_list) then (
        // Send message to next principal in the list:
        let next_principal_in_list = List.Tot.Base.index principal_list (counter + 2) in
        let next_counter = (counter+1) in
        let message_for_next_principal = MsgWithCounter principal_list next_counter secret_nonce in
        if (List.Tot.Base.index principal_list (counter + 1) <> receiver) then (
          error "SR.Protocol: authenticated_confidential_receive_and_process_message: receiver is not in list of principals"
        ) else (
          assert(List.Tot.mem receiver principal_list);
          assert(List.Tot.memP next_principal_in_list principal_list);
          assert(List.Tot.mem next_principal_in_list principal_list);
          assert(is_publishable gu t0 received_serialized_msg ==>
            LCA.can_flow t0 (LCA.get_label key_usages received_serialized_msg) (readers (create_id_list_from_principal_list principal_list)));
          assert(principal_in_list_corrupted_and_nonce_flows_to_public t0 principal_list secret_nonce \/
            was_rand_generated_before t0 secret_nonce (readers (create_id_list_from_principal_list principal_list)) (nonce_usage "SR.Secret"));
          rand_is_secret #gu #t0 #(readers (create_id_list_from_principal_list principal_list)) #(nonce_usage "SR.Secret") secret_nonce;
          principal_in_list_corrupted_and_nonce_flows_to_public_implies_nonce_flows_to_public t0 principal_list secret_nonce;
          assert(principal_in_list_corrupted_and_nonce_flows_to_public t0 principal_list secret_nonce ==>
          is_publishable gu t0 secret_nonce);
          assert(LCA.can_flow t0 (LCA.get_label key_usages secret_nonce) (readers (create_id_list_from_principal_list principal_list)));
          let serialized_next_message = serialize_msg t0 (readers (create_id_list_from_principal_list principal_list)) message_for_next_principal in
          parse_serialize_msg_lemma t0 (readers (create_id_list_from_principal_list principal_list)) message_for_next_principal;
          parse_serialize_list_of_principals_lemma t0 principal_list;
          parse_msg_preserves_is_publishable received_serialized_msg;
          let processed_ev = processed_authnconf_message principal_list secret_nonce next_counter in

          assert(
           let previous_principal = List.Tot.Base.index principal_list (counter) in
           (principal_in_list_corrupted_and_nonce_flows_to_public t0 principal_list secret_nonce \/
            (exists (previous_ev_idx previous_msg_idx:timestamp).
              (previous_ev_idx < previous_msg_idx) /\ (previous_msg_idx < t0)
              /\ (did_event_occur_at previous_ev_idx previous_principal (processed_authnconf_message principal_list secret_nonce counter))
              /\ S.is_authenticated_confidential_message_sent_at previous_msg_idx received_serialized_msg
              )
              )
          );
          assert(epred t0 receiver processed_ev);
          S.trigger_event #sr_preds receiver processed_ev;
          let current_trace_len =  GlobalRuntimeLib.global_timestamp () in
          assert(later_than current_trace_len t0);
          assert((authenticated_confidential_send_pred t0 received_serialized_msg));
          authenticated_confidential_send_pred_holds_later t0 current_trace_len received_serialized_msg;
          assert((authenticated_confidential_send_pred current_trace_len received_serialized_msg));
          assert((authenticated_confidential_send_pred current_trace_len serialized_next_message));

          assert(LCA.can_flow current_trace_len (LCA.get_label key_usages secret_nonce) (readers (create_id_list_from_principal_list principal_list)));
          assert(is_valid_message current_trace_len message_for_next_principal (readers (create_id_list_from_principal_list principal_list)));
          parse_serialize_msg_lemma current_trace_len (readers (create_id_list_from_principal_list principal_list)) message_for_next_principal;
          assert(is_msg gu current_trace_len serialized_next_message (readers (create_id_list_from_principal_list principal_list)));
          parse_msg_label_lemma #current_trace_len #(readers (create_id_list_from_principal_list principal_list)) serialized_next_message receiver next_principal_in_list;
          assert(is_msg gu current_trace_len serialized_next_message (readers [P receiver; P next_principal_in_list]));

          // next, we show that the label of the serialized message can flow to the join label required by
          // the send function
          let (serialized_next_message:msg gu current_trace_len
              (readers [P receiver; P next_principal_in_list])) = serialized_next_message in
          LabeledCryptoAPI.can_flow_to_join_forall current_trace_len;
          assert(LCA.can_flow current_trace_len (readers [P receiver; P next_principal_in_list]) (readers [P receiver]));
          assert(LCA.can_flow current_trace_len (readers [P receiver; P next_principal_in_list]) (readers [P next_principal_in_list]));
          let (serialized_next_message:msg gu current_trace_len
              (join (readers [P receiver]) (readers [P next_principal_in_list]))) = serialized_next_message in

          let send_index = Communication.API.send #current_trace_len #sr_preds receiver next_principal_in_list serialized_next_message Communication.API.AuthNConf in
          Success send_index

        )
      ) else (
        // the receiver is the last principal in the list and creates a [finished_confidential_authenticated] event
        assert((counter + 1) = (List.Tot.length principal_list) - 1);
        let last_principal_in_list = List.Tot.Base.index principal_list (counter + 1) in
        if (last_principal_in_list <> receiver) then Error "Reached max counter, but wrong receiver"
        else(

          //create a [processed_confidential_authenticated_message] event
          let processed_ev = processed_authnconf_message principal_list secret_nonce (counter + 1) in
          assert(epred t0 receiver processed_ev);
          S.trigger_event #sr_preds receiver processed_ev;

          //create a [finished_confidential_authenticated] event
          let current_trace_len =  GlobalRuntimeLib.global_timestamp () in
          let finished_ev = finished_confidential_authenticated principal_list secret_nonce (counter+1) in
          assert((authenticated_confidential_send_pred t0 received_serialized_msg));
          principal_in_list_corrupted_and_nonce_flows_to_public_later_forall current_trace_len principal_list  secret_nonce;
          assert(epred current_trace_len receiver finished_ev);
          S.trigger_event #sr_preds receiver finished_ev;

          Error "finished"
        )
      )
     )
  )
#pop-options
