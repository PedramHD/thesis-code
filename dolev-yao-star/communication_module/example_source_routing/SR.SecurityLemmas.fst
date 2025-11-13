/// SR.SecurityLemmas
/// ====================
module SR.SecurityLemmas

open CryptoEffect
open Communication.Layer
open SR.LabeledSerializingParsing

#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let receiver_secrecy_lemma i receiver principal_list secret_nonce =
  let principal_list_bytes = serialize_list_of_principals_raw principal_list in
  match parse_list_of_principals principal_list_bytes with
  | Success parsed_principal_list ->
  parse_serialize_list_of_principals_lemma i principal_list;
  assert(parsed_principal_list == principal_list);
  let t0 = get () in
  rand_is_secret #gu
    #i #(readers (create_id_list_from_principal_list principal_list)) #(nonce_usage "SR.Secret") secret_nonce;
  assert(later_than (trace_len t0) i);
  ids_in_create_id_list_from_principal_list_lemma principal_list;
  secrecy_lemma #(pki (send_preds sr_preds)) secret_nonce;
  ()
#pop-options


let authenticated_message_integrity i initiator receiver principal_list secret_nonce counter=
  let principal_list_bytes = serialize_list_of_principals_raw principal_list in
  match parse_list_of_principals principal_list_bytes with
  | Success parsed_principal_list ->
    parse_serialize_list_of_principals_lemma i principal_list;
    let trace_length = GlobalRuntimeLib.global_timestamp () in
    principal_in_list_corrupted_and_nonce_flows_to_public_lemma trace_length i principal_list secret_nonce;
    assert(~ (principal_in_list_corrupted_and_nonce_flows_to_public i principal_list secret_nonce))

#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
val path_integrity_helper_2_equal_fixed_i_lemma: (cp: authenticated_channel_property) -> (t0:trace) -> (i:nat) -> (principal_list:list principal) -> (secret_nonce:bytes) -> (counter:nat) ->
  Lemma
  (requires (
     valid_trace (pki (send_preds sr_preds)) t0 /\
     (~ (principal_in_list_corrupted_and_nonce_flows_to_public (trace_len t0) principal_list secret_nonce)) /\
     List.Tot.Base.length principal_list > 0 /\
     counter < List.Tot.Base.length principal_list /\
     i < counter
  ))
  (ensures ((
         let p_counter = List.Tot.Base.index principal_list counter in
         let p_i = List.Tot.Base.index principal_list i in
         forall (k_j:timestamp).
         (
         (k_j < (trace_len t0) /\ did_event_occur_at k_j p_counter (processed_message_ cp principal_list secret_nonce counter)) ==>
         (exists (k_i:timestamp) i_m. (k_i <= i_m) /\ (i_m <= k_j)
            /\ (did_event_occur_at k_i p_i (processed_message_ cp principal_list secret_nonce i))
            /\ (let recv_msg = serialize_msg_raw (MsgWithCounter principal_list (counter-1) secret_nonce) in
               match cp with
               | AuthN -> exists signed_msg verif_idx. is_authenticated_message_sent_at i_m verif_idx recv_msg signed_msg
               | AuthNConf -> is_authenticated_confidential_message_sent_at i_m recv_msg
              )
         )
         )
  )))
  (decreases (counter - i))
  [SMTPat ((did_event_occur_before (trace_len t0) (List.Tot.Base.index principal_list counter) (processed_message_ cp principal_list secret_nonce counter))); SMTPat (later_than counter i)]

let rec path_integrity_helper_2_equal_fixed_i_lemma cp t0 i principal_list secret_nonce counter =
    let trace_length = trace_len t0 in
    principal_in_list_corrupted_and_nonce_flows_to_public_later_forall trace_length principal_list secret_nonce;
    let p_i = List.Tot.Base.index principal_list i in
    let p_counter = List.Tot.Base.index principal_list counter in
    parse_serialize_list_of_principals_raw_lemma principal_list;
    if (i = counter - 1) then ()
    else (
      assert(i < counter - 1);
      assert(i >= 0);
      path_integrity_helper_2_equal_fixed_i_lemma cp t0 (i+1) principal_list secret_nonce counter
    )
#pop-options


#push-options "--z3rlimit 150"
let path_integrity_helper_2_equal_authn  principal_list secret_nonce (counter:nat):
  LCrypto unit (pki (send_preds sr_preds))
  (requires ( fun t0 -> (
     (~ (principal_in_list_corrupted_and_nonce_flows_to_public (trace_len t0) principal_list secret_nonce)) /\
     List.Tot.Base.length principal_list > 0 /\
     counter < List.Tot.Base.length principal_list
  )))
  (ensures ( fun t0 _ t1 -> t0 == t1 /\ (
          forall (k_j:timestamp) (i:nat) . (i < counter) ==> (
            let p_i = List.Tot.Base.index principal_list i in
            let p_counter = List.Tot.Base.index principal_list counter in
            (
              (k_j < (trace_len t0) /\ did_event_occur_at k_j p_counter (processed_message_ AuthN principal_list secret_nonce counter))
              ==> (exists (k_i:timestamp) m_j. (k_i <= m_j) /\ (m_j <= k_j)
                   /\ (did_event_occur_at k_i p_i (processed_message_ AuthN principal_list secret_nonce i))
                   /\ ( let recv_msg = serialize_msg_raw (MsgWithCounter principal_list (counter-1) secret_nonce) in
                       exists signed_msg verif_idx. is_authenticated_message_sent_at m_j verif_idx recv_msg signed_msg
                  )
              )
            )
          )
  )))
  =
    let t0 = get () in
    assert(forall (k_j:timestamp) (i:nat) . (i < counter) ==> (
      let p_i = List.Tot.Base.index principal_list i in
      let p_counter = List.Tot.Base.index principal_list counter in
      (
        (k_j < (trace_len t0) /\ did_event_occur_at k_j p_counter (processed_message_ AuthN principal_list secret_nonce counter))
        ==> (did_event_occur_before (trace_len t0) p_counter (processed_message_ AuthN principal_list secret_nonce counter) /\ later_than counter i)
      )
     )
    )

let path_integrity_helper_2_equal_authnconf principal_list secret_nonce (counter:nat):
  LCrypto unit (pki (send_preds sr_preds))
  (requires ( fun t0 -> (
     (~ (principal_in_list_corrupted_and_nonce_flows_to_public (trace_len t0) principal_list secret_nonce)) /\
     List.Tot.Base.length principal_list > 0 /\
     counter < List.Tot.Base.length principal_list
  )))
  (ensures ( fun t0 _ t1 -> t0 == t1 /\ (
          forall (k_j:timestamp) (i:nat) . (i < counter) ==> (
            let p_i = List.Tot.Base.index principal_list i in
            let p_counter = List.Tot.Base.index principal_list counter in
            (
              (k_j < (trace_len t0) /\ did_event_occur_at k_j p_counter (processed_message_ AuthNConf principal_list secret_nonce counter))
              ==> (exists (k_i:timestamp) m_j. (k_i <= m_j) /\ (m_j <= k_j)
                   /\ (did_event_occur_at k_i p_i (processed_message_ AuthNConf principal_list secret_nonce i))
                   /\ ( let recv_msg = serialize_msg_raw (MsgWithCounter principal_list (counter-1) secret_nonce) in
                       is_authenticated_confidential_message_sent_at m_j recv_msg
                  )
              )
            )
          )
  )))
  =
    let t0 = get () in
    assert(forall (k_j:timestamp) (i:nat) . (i < counter) ==> (
      let p_i = List.Tot.Base.index principal_list i in
      let p_counter = List.Tot.Base.index principal_list counter in
      (
        (k_j < (trace_len t0) /\ did_event_occur_at k_j p_counter (processed_message_ AuthNConf principal_list secret_nonce counter))
        ==> (did_event_occur_before (trace_len t0) p_counter (processed_message_ AuthNConf principal_list secret_nonce counter) /\ later_than counter i)
      )
     )
    )
#pop-options


let rec path_integrity_helper_2 (cp: authenticated_channel_property) principal_list secret_nonce (counter:nat):
  LCrypto unit (pki (send_preds sr_preds))
  (requires ( fun t0 -> (
     (~ (principal_in_list_corrupted_and_nonce_flows_to_public (trace_len t0) principal_list secret_nonce)) /\
     List.Tot.Base.length principal_list > 0 /\
     counter < List.Tot.Base.length principal_list
  )))
  (ensures ( fun t0 _ t1 -> t0 == t1 /\ (
          forall (k_j:timestamp) i j. (i < j) /\ (j <= counter)  ==> (
            let p_i = List.Tot.Base.index principal_list i in
            let p_j = List.Tot.Base.index principal_list j in
            // principal_list = [..., p_i, ..., p_j, ...] and p_i triggered the processed_authenticated_message event prior to p_j:
            (
              (k_j < trace_len t0 /\ did_event_occur_at k_j p_j (processed_message_ cp principal_list secret_nonce j))
              ==> (exists (k_i:timestamp) m_j. (k_i <= m_j) /\ (m_j <= k_j)
                   /\ (did_event_occur_at k_i p_i (processed_message_ cp principal_list secret_nonce i))
                   /\ (let recv_msg = serialize_msg_raw (MsgWithCounter principal_list (j-1) secret_nonce) in
                      match cp with
                       | AuthN -> exists signed_msg verif_idx. is_authenticated_message_sent_at m_j verif_idx recv_msg signed_msg
                       | AuthNConf -> is_authenticated_confidential_message_sent_at m_j recv_msg
                  )
                 )
            )
          )
  )))
  =
  match counter with
  | 0 -> ()
  | _ ->
    path_integrity_helper_2 cp principal_list secret_nonce (counter - 1);
    match cp with
    | AuthN -> path_integrity_helper_2_equal_authn principal_list secret_nonce counter
    | AuthNConf -> path_integrity_helper_2_equal_authnconf principal_list secret_nonce counter


#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let rec authenticated_all_previous_principals_sent_events_helper (cp:authenticated_channel_property) principal_list secret_nonce (counter:nat):
  LCrypto unit (pki (send_preds sr_preds))
  (requires ( fun t0 -> (
     (~ (principal_in_list_corrupted_and_nonce_flows_to_public (trace_len t0) principal_list secret_nonce)) /\
     List.Tot.Base.length principal_list > 0 /\
     counter < List.Tot.Base.length principal_list /\
     did_event_occur_before (trace_len t0) (List.Tot.Base.index principal_list counter) (processed_message_ cp principal_list secret_nonce counter)
  )))
  (ensures ( fun t0 _ t1 -> t0 == t1 /\ (
      ( forall (i:nat). (i <= counter) ==>
         (
           let p_i = List.Tot.Base.index principal_list i in
           exists (k_i:timestamp) m_i.
           (k_i <= (trace_len t0))
           /\ (did_event_occur_at k_i p_i (processed_message_ cp principal_list secret_nonce i))
           /\ ( i > 0 ==> (let recv_msg = serialize_msg_raw (MsgWithCounter principal_list (i-1) secret_nonce) in
               match cp with
               | AuthN -> exists signed_msg verif_idx. is_authenticated_message_sent_at m_i verif_idx recv_msg signed_msg
               | AuthNConf -> is_authenticated_confidential_message_sent_at m_i recv_msg
             )))
         )
      )
  ))
  =
  match counter with
  | 0 -> ()
  | _ ->
     let current_trace_len = GlobalRuntimeLib.global_timestamp () in
    assert(exists (k:timestamp). (later_than current_trace_len k) /\ epred k (List.Tot.Base.index principal_list (counter)) (processed_message_ cp principal_list secret_nonce (counter )));
    principal_in_list_corrupted_and_nonce_flows_to_public_later_forall current_trace_len principal_list secret_nonce;


    let previous_principal = List.Tot.Base.index principal_list (counter -1) in
    parse_serialize_list_of_principals_raw_lemma principal_list;
    assert(did_event_occur_before current_trace_len (List.Tot.Base.index principal_list (counter -1)) (processed_message_ cp principal_list secret_nonce (counter - 1)));
    authenticated_all_previous_principals_sent_events_helper cp principal_list secret_nonce (counter -1);
    ()

#pop-options

#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let path_integrity_arbitrary_counter (cp: authenticated_channel_property) (trace_idx:nat) (principal_list:list principal) (secret_nonce:bytes) (counter:nat) :
    LCrypto unit (pki (send_preds sr_preds))
    (requires (fun t0 -> trace_idx < trace_len t0 /\
      List.Tot.Base.length principal_list > 0 /\
      counter < List.Tot.Base.length principal_list /\
      did_event_occur_before trace_idx (List.Tot.Base.index principal_list counter) (processed_message_ cp principal_list secret_nonce counter) /\
      (forall p. List.Tot.mem p principal_list ==> ~ (corrupt_at (trace_len t0) (P p)))
    ))
    (ensures (fun t0 _ t1 -> t0 == t1 /\ (
      ( forall (i:nat). (i <= counter) ==>
         (
           (let p_i = List.Tot.Base.index principal_list i in
           exists (k_i:timestamp) m_i. (k_i <= (trace_len t0)) /\ (did_event_occur_at k_i p_i (processed_message_ cp principal_list secret_nonce i))
           /\ ( i > 0 ==> (let recv_msg = serialize_msg_raw (MsgWithCounter principal_list (i-1) secret_nonce) in
               match cp with
               | AuthN -> exists signed_msg verif_idx. is_authenticated_message_sent_at m_i verif_idx recv_msg signed_msg
               | AuthNConf -> is_authenticated_confidential_message_sent_at m_i recv_msg
             )))
           )
         )
      ) /\
          (
            forall (k_j:timestamp) i j. (i < j) /\ (j <= counter)  ==>
            (
              let p_i = List.Tot.Base.index principal_list i in
              let p_j = List.Tot.Base.index principal_list j in
              ((
                k_j < trace_len t0 /\
                did_event_occur_at k_j p_j (processed_message_ cp principal_list secret_nonce j))
                ==> (exists (k_i:timestamp) m_j. (k_i <= m_j) /\ (m_j <= k_j)
                     /\ (did_event_occur_at k_i p_i (processed_message_ cp principal_list secret_nonce i))
                     /\ ( let recv_msg = serialize_msg_raw (MsgWithCounter principal_list (j-1) secret_nonce) in
                         match cp with
                         | AuthN -> exists signed_msg verif_idx. is_authenticated_message_sent_at m_j verif_idx recv_msg signed_msg
                         | AuthNConf -> is_authenticated_confidential_message_sent_at m_j recv_msg
                       )
                   )
              )
            )
          )
    )) =
  let principal_list_bytes = serialize_list_of_principals_raw principal_list in
  match parse_list_of_principals principal_list_bytes with
  | Success parsed_principal_list -> (
    parse_serialize_list_of_principals_lemma trace_idx principal_list;
    assert(parsed_principal_list = principal_list);

    let trace_length = GlobalRuntimeLib.global_timestamp () in
    principal_in_list_corrupted_and_nonce_flows_to_public_lemma trace_length trace_length principal_list secret_nonce;
    assert(trace_length <= trace_length);
    assert(forall p. List.Tot.mem p principal_list ==> ~ (corrupt_at trace_length (P p)));
    assert(~ (principal_in_list_corrupted_and_nonce_flows_to_public trace_length principal_list secret_nonce));
    assert(List.Tot.Base.length principal_list > 0);
    assert(counter < List.Tot.Base.length principal_list);
    path_integrity_helper_2 cp principal_list secret_nonce counter;
    authenticated_all_previous_principals_sent_events_helper cp principal_list secret_nonce counter
  )
#pop-options

#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let authenticated_path_integrity trace_idx receiver principal_list secret_nonce counter =
  let principal_list_bytes = serialize_list_of_principals_raw principal_list in
  match parse_list_of_principals principal_list_bytes with
  | Success parsed_principal_list -> (
    parse_serialize_list_of_principals_lemma trace_idx principal_list;
    assert(parsed_principal_list == principal_list);

    let trace_length = GlobalRuntimeLib.global_timestamp () in
    principal_in_list_corrupted_and_nonce_flows_to_public_lemma trace_length trace_idx principal_list secret_nonce;
    assert(~ (principal_in_list_corrupted_and_nonce_flows_to_public trace_idx principal_list secret_nonce));
    path_integrity_arbitrary_counter AuthN trace_idx principal_list secret_nonce counter
  )

#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let confidential_authenticated_receiver_secrecy_lemma i initiator principal_list secret_nonce counter =
  let principal_list_bytes = serialize_list_of_principals_raw principal_list in
  match parse_list_of_principals principal_list_bytes with
  | Success parsed_principal_list ->
  parse_serialize_list_of_principals_lemma i principal_list;
  assert(parsed_principal_list == principal_list);
  let t0 = get () in
  let trace_length = GlobalRuntimeLib.global_timestamp () in
  rand_is_secret #gu
    #i #(readers (create_id_list_from_principal_list principal_list)) #(nonce_usage "SR.Secret") secret_nonce;
  principal_in_list_corrupted_and_nonce_flows_to_public_lemma trace_length i principal_list secret_nonce;
  assert(is_valid gu i secret_nonce);
  assert(later_than (trace_len t0) i);
  assert(is_valid gu (trace_len t0) secret_nonce);
  ids_in_create_id_list_from_principal_list_lemma principal_list;

  secrecy_lemma #(pki (send_preds sr_preds)) secret_nonce;
  assert( (is_labeled gu (trace_len t0) secret_nonce (readers
    (create_id_list_from_principal_list principal_list)) /\
    attacker_knows_at (trace_len t0) secret_nonce) ==>
    (exists id. List.Tot.mem id (create_id_list_from_principal_list principal_list) /\ corrupt_at (trace_len t0) id));
  assert(attacker_knows_at (trace_len t0) secret_nonce ==>
    (exists id. List.Tot.mem id (create_id_list_from_principal_list principal_list) /\ corrupt_at (trace_len t0) id));
    assert(forall principal.  List.Tot.mem principal principal_list ==> ~ (corrupt_at (trace_len t0) (P principal)));
    assert(forall id. List.Tot.mem id (create_id_list_from_principal_list principal_list) ==> ~ (corrupt_at (trace_len t0) id))
#pop-options

let confidential_authenticated_message_integrity i initiator receiver principal_list secret_nonce counter=
  let principal_list_bytes = serialize_list_of_principals_raw principal_list in
  match parse_list_of_principals principal_list_bytes with
  | Success parsed_principal_list ->
    parse_serialize_list_of_principals_lemma i principal_list;
    let trace_length = GlobalRuntimeLib.global_timestamp () in
    principal_in_list_corrupted_and_nonce_flows_to_public_lemma trace_length i principal_list secret_nonce;
    assert(~ (principal_in_list_corrupted_and_nonce_flows_to_public i principal_list secret_nonce))

#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let confidential_authenticated_path_integrity trace_idx receiver principal_list secret_nonce counter =
  let principal_list_bytes = serialize_list_of_principals_raw principal_list in
  match parse_list_of_principals principal_list_bytes with
  | Success parsed_principal_list -> (
    parse_serialize_list_of_principals_lemma trace_idx principal_list;
    assert(parsed_principal_list = principal_list);

    let trace_length = GlobalRuntimeLib.global_timestamp () in
    principal_in_list_corrupted_and_nonce_flows_to_public_lemma trace_length trace_idx principal_list secret_nonce;
    assert(~ (principal_in_list_corrupted_and_nonce_flows_to_public trace_idx principal_list secret_nonce));
    path_integrity_arbitrary_counter AuthNConf trace_idx principal_list secret_nonce counter
  )
#pop-options
