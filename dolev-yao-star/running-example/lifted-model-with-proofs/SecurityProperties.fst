
/// SecurityProperties
/// =======================
module SecurityProperties

open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI
open AttackerAPI


open Protocol

open SecurityLemmas

friend LabeledPKI


let correspondence_property (initiator:principal) (receiver:principal) (nonce:bytes) (event_idx:timestamp):
  LCrypto unit (pki predicates)
  (requires (fun t0 ->
    event_idx < trace_len t0 /\
    did_event_occur_at event_idx receiver (create_receive_event receiver initiator nonce)
  ))
  (ensures (fun t0 _ t1 -> (t0 == t1 /\
    (
          (corrupt_at (trace_len t0) (P initiator) \/
          (
            (exists (si:nat) (initiator_ev_idx:nat) (vvec:version_vec) (state_vec:state_vec).
               initiator_ev_idx > 0 /\
              later_than event_idx initiator_ev_idx /\
              did_event_occur_at initiator_ev_idx initiator (create_initiate_event initiator receiver nonce) /\
              state_was_set_at (initiator_ev_idx -1) initiator vvec state_vec /\
            (exists (si:nat). si < Seq.Base.length state_vec /\ initiator_stores_nonce_in_state initiator receiver nonce state_vec si)
          )
    )
  )))))
  =
    let initiate_event = create_initiate_event initiator receiver nonce in
    let current_trace_len = global_timestamp () in
    let current_trace = get () in
    assert(corrupt_at current_trace_len (P initiator) \/
      did_event_occur_before event_idx initiator (create_initiate_event initiator receiver nonce));

    assert(did_event_occur_before event_idx initiator initiate_event
      ==> (exists (i:timestamp). later_than event_idx i /\ did_event_occur_at i initiator initiate_event));

      assert(forall (i:timestamp). (later_than event_idx i /\ did_event_occur_at i initiator initiate_event)
        ==> (event_predicate i initiator initiate_event) /\ i > 0
      );

      assert(forall (i:timestamp). (later_than event_idx i) /\ (event_predicate i initiator initiate_event) ==>
        (
          match initiate_event with
          | ("initiated", [initiator_bytes; responder_bytes; nonce]) -> (
            match CryptoLib.bytes_to_string initiator_bytes, CryptoLib.bytes_to_string responder_bytes with
            | Success initiator_from_event, Success responder_from_event -> (
                      i > 0 /\
                      was_rand_generated_before i nonce (readers [P initiator_from_event; P responder_from_event]) (CryptoLib.nonce_usage "running_example_shared_secret") /\
                      initiator_from_event = initiator /\
                      responder_from_event = receiver /\
                        (exists (state_vec:CryptoEffect.state_vec) (vvec:version_vec) (si:nat).
                       si < Seq.Base.length state_vec /\
                       state_was_set_at (i-1) initiator vvec state_vec /\
                       initiator_stores_nonce_in_state initiator receiver nonce state_vec si
                     )
              )
            | _, _ -> False
          )
          | _ -> False
        )
      );

      assert(forall (i:timestamp). (later_than event_idx i) /\ (event_predicate i initiator initiate_event) ==>
        (exists (state_vec:CryptoEffect.state_vec) (vvec:version_vec) (si:nat).
                       si < Seq.Base.length state_vec /\
                       state_was_set_at (i-1) initiator vvec state_vec /\
                       initiator_stores_nonce_in_state initiator receiver nonce state_vec si
        )
      );
  ()


let nonce_is_secret (initiator:principal) (receiver:principal) (nonce:bytes) (event_idx:timestamp) :
  LCrypto unit (pki predicates)
  (requires (fun t0 ->
    event_idx < trace_len t0 /\
    did_event_occur_at event_idx initiator (create_initiate_event initiator receiver nonce)
  ))
  (ensures (fun t0 _ t1 -> (t0 == t1 /\
    (
      is_unknown_to_attacker_at (trace_len t0) nonce \/
      (corrupt_id (trace_len t0) (P initiator) \/ corrupt_id (trace_len t0) (P receiver))
    )
  )))
  =

  let current_trace_len = global_timestamp () in
  let current_trace = get () in

  assert(valid_trace (pki predicates) current_trace);

  let initiate_event = create_initiate_event initiator receiver nonce in
  assert(event_predicate event_idx initiator initiate_event);

  assert(was_rand_generated_before event_idx nonce (readers [P initiator; P receiver]) (nonce_usage "running_example_shared_secret"));

  rand_is_secret #global_crypto_usage #event_idx #(readers [P initiator; P receiver]) #(nonce_usage "running_example_shared_secret") nonce;
  assert(later_than current_trace_len event_idx);
  secrecy_lemma #(pki predicates) nonce

let nonce_is_stored_in_responder_state state_vec si initiator shared_secret =
  let session_bytes = state_vec.[si] in
    match LabeledPKI.parse_session_st session_bytes with
    | Success (APP labeledpki_session_bytes) -> (
      match Protocol.parse_session_st labeledpki_session_bytes with
      | Success (ResponderReceivedMsg initiator_stored_in_state shared_secret_stored_in_state) -> (
                  initiator_stored_in_state == initiator /\
                  shared_secret_stored_in_state == shared_secret
      )
      | _ -> False
    )
    | _ -> False

let nonce_stored_in_responder_state_is_secret (receiver:principal) (shared_secret:bytes) (initiator:principal) (state_vec:state_vec) (vvec:version_vec) (set_state_trace_idx:timestamp) (si:nat)
  : LCrypto unit (pki predicates)
  (requires ( fun t0 -> set_state_trace_idx < (trace_len t0) /\
    si < Seq.Base.length state_vec /\
    state_was_set_at set_state_trace_idx receiver vvec state_vec /\
    nonce_is_stored_in_responder_state state_vec si initiator shared_secret
  ))
  (ensures ( fun t0 _ t1 ->
    t0 == t1 /\ (
    corrupt_id (trace_len t1) (P initiator) \/
    corrupt_id (trace_len t1) (P receiver) \/
    ~(attacker_knows_at (trace_len t1) shared_secret)
    )
  ))
  =
      let t_now = global_timestamp () in
      let trace_now = get () in
      assert(trace_len trace_now = t_now);
      assert(valid_trace (pki predicates) trace_now);
      assert(set_state_trace_idx < trace_len trace_now);

      let gu = (pki predicates).global_usage in
      let pr = (pki predicates) in
      assert(gu == predicates.global_usage);
      let session_bytes = state_vec.[si] in

      assert(state_was_set_at set_state_trace_idx receiver vvec state_vec);
      assert(state_inv pr set_state_trace_idx receiver vvec state_vec);

      match LabeledPKI.parse_session_st session_bytes with
      | Success (APP labeledpki_session_bytes) -> (
        match Protocol.parse_session_st labeledpki_session_bytes with
        | Success (ResponderReceivedMsg initiator_stored_in_state shared_secret_stored_in_state) -> (
          assert(initiator_stored_in_state == initiator);
          assert(shared_secret_stored_in_state == shared_secret);

          assert(forall i. i < Seq.length vvec ==> pr.trace_preds.session_st_inv set_state_trace_idx receiver i vvec.[i] state_vec.[i]);
          assert(pr.trace_preds.session_st_inv set_state_trace_idx receiver si vvec.[si] state_vec.[si]);
          assert(pr.trace_preds.session_st_inv set_state_trace_idx receiver si vvec.[si] state_vec.[si]);

          assert(valid_state_session gu set_state_trace_idx receiver (ResponderReceivedMsg initiator_stored_in_state shared_secret_stored_in_state));

          assert((corrupt_id set_state_trace_idx (P initiator_stored_in_state) ==> corrupt_id t_now (P initiator_stored_in_state)));
          assert((was_rand_generated_before set_state_trace_idx shared_secret (readers [P initiator; P receiver]) (nonce_usage "running_example_shared_secret"))
            ==>
          (was_rand_generated_before t_now shared_secret (readers [P initiator; P receiver]) (nonce_usage "running_example_shared_secret")));

          secrecy_lemma #(pki predicates) shared_secret;
          rand_is_secret #(pki predicates).global_usage #t_now  #(readers [P initiator; P receiver]) #(nonce_usage "running_example_shared_secret") shared_secret;

          assert(forall ids. (is_labeled pr.global_usage t_now shared_secret (readers ids) /\
            attacker_knows_at t_now shared_secret) ==>
            (exists id. List.Tot.mem id ids /\ corrupt_at t_now id))
        )
        | _ -> ()
      )
      | _ -> ()

