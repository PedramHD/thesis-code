/// BA.SecurityLemmas
/// ====================
module BA.SecurityLemmas

friend LabeledPKI


let is_secret_in_initiator_state set_state_idx version_vector state_vector state_session_idx initiator server secret_nonce =
  state_was_set_at set_state_idx initiator version_vector state_vector /\
  state_session_idx < Seq.length state_vector /\
  (
    match LabeledPKI.parse_session_st (state_vector.[state_session_idx]) with
    | Success (LabeledPKI.APP s) -> (
      match Communication.Sessions.parse_session_st s with
      | Success (Communication.Layer.APP ba_state) ->
      (
        match BA.Sessions.parse_client_session_state ba_state with
        | Some (ClientSession initiator_in_state server_in_state _ opt_secret_in_state _) ->
        (
          initiator_in_state = initiator /\
          server_in_state = server /\
          Some? opt_secret_in_state /\
          Some?.v opt_secret_in_state == secret_nonce
        )
        | _ -> False
      )
      | _ -> False
    )
    | _ -> False
  )

let secrecy_of_secret_initiator set_state_idx version_vector state_vector state_session_idx initiator server secret_nonce =
  let t0 = get () in
  assert(later_than (trace_len t0) set_state_idx);

  assert(valid_trace (pki (Communication.Layer.send_preds ba_preds)) t0);
  assert(set_state_idx < (trace_len t0));
  assert(state_inv (pki (Communication.Layer.send_preds ba_preds)) set_state_idx initiator version_vector state_vector);

  match LabeledPKI.parse_session_st (state_vector.[state_session_idx]) with
  | Success (LabeledPKI.APP s) -> (
    match Communication.Sessions.parse_session_st s with
    | Success (Communication.Sessions.APP ba_state) ->
    (
      match BA.Sessions.parse_client_session_state ba_state with
      | Some (ClientSession initiator_in_state server_in_state _ opt_secret_in_state _) ->
        assert(BA.Preds.session_st_inv set_state_idx initiator state_session_idx (version_vector.[state_session_idx]) ba_state);
        parsed_client_state_cannot_be_parsed_by_server ba_state;
        assert(
          (was_rand_generated_before (trace_len t0) secret_nonce (readers [P initiator; P server]) (nonce_usage "BA.Secret")));
        rand_is_secret #gu #(trace_len t0) #(readers [P initiator; P server]) #(nonce_usage "BA.Secret") secret_nonce;

        assert(is_valid gu (trace_len t0) secret_nonce);

        assert(is_labeled gu (trace_len t0) secret_nonce (readers [P initiator; P server]));

        assert(forall id. List.Tot.mem id [P initiator; P server] ==> id = (P initiator) \/ id = (P server));
        assert(forall id. List.Tot.mem id [P initiator; P server] ==> ~ (corrupt_at (trace_len t0) id));


        secrecy_lemma #(pki (Communication.Layer.send_preds ba_preds)) secret_nonce
      | _ -> ()
    )
    | _ -> ()
  )
  | _ -> ()
