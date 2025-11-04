/// SR.Messages.Lemmas (implementation)
/// ===================================

module SR.Messages.Lemmas

friend SR.Messages
friend SR.LabeledSerializingParsing

module C = CryptoLib

let rec parse_list_of_principals_successful_implies_publishable b i gu =
  match C.split b with
  | Success (principal_bytes, principal_list) -> (
    concat_split_lemma b;
    assert(b = C.concat principal_bytes principal_list);
    concat_not_equal_string_to_bytes_lemma ();
    assert(C.concat principal_bytes principal_list <> (C.string_to_bytes ""));
    match C.bytes_to_string principal_bytes with
    | Success p -> (
      assert(term_depth principal_list < term_depth b);
      match parse_list_of_principals principal_list with
      | Success p_list -> (
        LabeledCryptoAPI.bytes_to_string_successful_implies_publishable principal_bytes;
        parse_list_of_principals_successful_implies_publishable principal_list i gu;
        split_based_on_split_len_prefixed_lemma b;
        assert(C.is_succ2 (C.split_len_prefixed 4 b) principal_bytes principal_list);
        assert(is_publishable gu i principal_bytes);
        assert(is_publishable gu i principal_list);
        components_publishable_implies_splittable_term_publishable gu
      )
    )
  )
  | Error e -> (
    match C.bytes_to_string b with
    | Success "" -> (
      assert(Success? (C.bytes_to_string b));
      LabeledCryptoAPI.bytes_to_string_successful_implies_publishable b
    )
  )


let principal_in_list_corrupted_and_nonce_flows_to_public_lemma trace_idx i principal_list nonce = ()
let principal_in_list_corrupted_and_nonce_flows_to_public_later_forall trace_idx principal_list nonce = ()
let parse_msg_preserves_is_msg #gu #i #l m = ()
let parse_msg_preserves_is_publishable m = ()




#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 2"
let parse_msg_label_lemma_2_MsgWithCounter (#i:nat) (#l:label) (msg:msg gu i l) (receiver:principal) (next_principal:principal) :
  Lemma
  (requires (
    match parse_msg msg with
    | Success (MsgWithCounter principal_list counter secret_nonce) -> (
      List.Tot.mem receiver principal_list /\
      List.Tot.mem next_principal principal_list
    )
    | _ -> False
  ))
  (ensures(
    match parse_msg msg with
    | Success (MsgWithCounter principal_list counter secret_nonce) -> (
       (authenticated_confidential_send_pred i msg) ==>
       LabeledCryptoAPI.can_flow i (LabeledCryptoAPI.get_label key_usages msg) (readers [P receiver; P next_principal])
    )
    | _ -> False
  ))
  =
  assert(Success? (parse_msg msg));
  assert(Success? (parse_msg_raw msg));
  match split msg with
  | Success (part_1, nonce) ->  (
     match parse_list_of_principals part_1 with
     | Error e -> (
        match split part_1 with
        | Success (counter_bytes, principal_list_bytes) -> (
          match bytes_to_nat counter_bytes with
          | Success counter -> (
            match parse_list_of_principals principal_list_bytes with
            | Success principal_list -> (
              assert(parse_msg msg == Success (MsgWithCounter principal_list counter nonce));
              assert(List.Tot.mem receiver principal_list);
              assert(List.Tot.mem next_principal principal_list);
              serialize_parse_list_of_principals_lemma i l principal_list_bytes;
              create_id_list_from_principal_list_lemma receiver principal_list;
              create_id_list_from_principal_list_lemma next_principal principal_list;
              assert_norm(forall x. List.Tot.mem x [P receiver; P next_principal] ==> x = (P receiver) \/ x = (P next_principal));
              rand_is_secret #gu
                #i #(readers (create_id_list_from_principal_list principal_list)) #(nonce_usage "SR.Secret") nonce;
              assert((authenticated_confidential_send_pred i msg) ==>
              A.can_flow i (A.get_label key_usages nonce) public \/
              (is_secret gu i nonce
                (readers (create_id_list_from_principal_list principal_list)) (nonce_usage "SR.Secret")));
             concat_split_lemma msg;
             concat_split_lemma part_1;
             assert(msg = concat part_1 nonce);
             assert(part_1 = concat counter_bytes principal_list_bytes);
             assert(is_valid gu i msg);
             assert(A.can_flow i (A.get_label key_usages msg) public ==>
               LabeledCryptoAPI.can_flow i (LabeledCryptoAPI.get_label key_usages msg) (readers [P receiver; P next_principal])
             );


             split_based_on_split_len_prefixed_lemma msg;
             assert(C.is_succ2 (C.split_len_prefixed 4 msg) part_1 nonce);
             splittable_term_publishable_implies_components_publishable_forall gu;

             assert(is_publishable gu i msg ==>
               is_publishable gu i nonce);

             assert(A.can_flow i (A.get_label key_usages msg) public ==>
               A.can_flow i (A.get_label key_usages nonce) public);

             assert(A.can_flow i (A.get_label key_usages msg) public ==>
                LabeledCryptoAPI.can_flow i (LabeledCryptoAPI.get_label key_usages nonce) (readers [P receiver; P next_principal]));

             assert(
              (is_secret
                gu i nonce
                (readers (create_id_list_from_principal_list principal_list)) (nonce_usage "SR.Secret"))
                ==>
                LabeledCryptoAPI.can_flow i (LabeledCryptoAPI.get_label key_usages nonce) (readers [P receiver; P next_principal])
                );

            assert((authenticated_confidential_send_pred i msg) ==> LabeledCryptoAPI.can_flow i (LabeledCryptoAPI.get_label key_usages nonce) (readers [P receiver; P next_principal]));
            bytes_to_nat_successful_implies_publishable counter_bytes;

            assert(is_publishable gu i counter_bytes );
            assert(LabeledCryptoAPI.can_flow i  (LabeledCryptoAPI.get_label key_usages  counter_bytes) public);

            parse_list_of_principals_successful_implies_publishable principal_list_bytes i gu;
            assert(LabeledCryptoAPI.can_flow i (LabeledCryptoAPI.get_label key_usages principal_list_bytes) public);
            split_based_on_split_len_prefixed_lemma part_1;
            assert(C.is_succ2 (C.split_len_prefixed 4 part_1) counter_bytes principal_list_bytes);
            components_publishable_implies_splittable_term_publishable gu;
            assert(LabeledCryptoAPI.can_flow i (LabeledCryptoAPI.get_label key_usages part_1) public);
            assert(LabeledCryptoAPI.can_flow i (LabeledCryptoAPI.get_label key_usages part_1) (readers [P receiver; P next_principal]));
            assert((authenticated_confidential_send_pred i msg) ==> msg = concat #gu #i #(readers [P receiver; P next_principal]) part_1 nonce);
            assert((is_secret gu i nonce
               (readers (create_id_list_from_principal_list principal_list)) (nonce_usage "SR.Secret")) ==>
            LabeledCryptoAPI.can_flow i (LabeledCryptoAPI.get_label key_usages msg) (readers [P receiver; P next_principal])
               )
          )
          )
        )
     )
  )
#pop-options


#push-options "--z3rlimit 150 --max_fuel 4 --max_ifuel 4"
let parse_msg_label_lemma #i #l msg p1 p2 =
  assert(Success? (parse_msg msg));
  assert(Success? (parse_msg_raw msg));
  match split msg with
  | Success (part_1, nonce) ->  (
     match parse_list_of_principals part_1 with
     | Success principal_list -> (
       assert(parse_msg msg == Success (Msg principal_list nonce));
       assert(List.Tot.mem p1 principal_list);
       assert(List.Tot.mem p2 principal_list);
       serialize_parse_list_of_principals_lemma i l part_1;
       create_id_list_from_principal_list_lemma p1 principal_list;
       create_id_list_from_principal_list_lemma p2 principal_list;
       assert_norm(forall x. List.Tot.mem x [P p1; P p2] ==> x = (P p1) \/ x = (P p2));
       rand_is_secret #gu #i #(readers (create_id_list_from_principal_list principal_list)) #(nonce_usage "SR.Secret") nonce;
       concat_split_lemma msg;
       assert(msg = concat part_1 nonce);
       assert((confidential_send_pred i msg) ==> msg = concat #gu #i #(readers [P p1; P p2]) part_1 nonce)
     )
     | Error e -> (
        match split part_1 with
        | Success (counter_bytes, principal_list_bytes) -> (
          match bytes_to_nat counter_bytes with
          | Success counter -> (
            match parse_list_of_principals principal_list_bytes with
            | Success principal_list -> (
              assert(parse_msg msg == Success (MsgWithCounter principal_list counter nonce));
              parse_msg_label_lemma_2_MsgWithCounter #i #l msg p1 p2
          )
          )
        )
     )
  )
#pop-options



let principal_in_list_corrupted_and_nonce_flows_to_public_implies_nonce_flows_to_public trace_idx principal_list nonce = ()


let nonce_flows_to_principals_contained_in_principal_list i gu p1 p2 nonce principal_list =
  create_id_list_from_principal_list_lemma p1 principal_list;
  create_id_list_from_principal_list_lemma p2 principal_list;
  assert(List.Tot.mem (P p1) (create_id_list_from_principal_list principal_list));
  assert(List.Tot.mem (P p2) (create_id_list_from_principal_list principal_list));

  assert(contains_id (create_id_list_from_principal_list principal_list) (P p1));
  assert(contains_id (create_id_list_from_principal_list principal_list) (P p2));
  assert_norm(forall x. List.Tot.mem x [P p1; P p2] ==> x = (P p1) \/ x = (P p2));
  assert(forall v. List.Tot.mem v ([P p1; P p2]) ==> contains_id (create_id_list_from_principal_list principal_list) v);
  assert(includes_ids (create_id_list_from_principal_list principal_list) ([P p1; P p2]));
  assert(A.can_flow i (readers (create_id_list_from_principal_list principal_list)) (readers [P p1; P p2]));
  assert(is_msg gu i nonce (readers [P p1; P p2]))


let authenticated_send_pred_holds_later i j m = ()
let authenticated_confidential_send_pred_holds_later i j m = ()



#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let authn_send_pred_lemma i p received_serialized_msg =
  match parse_msg_raw received_serialized_msg with
  | Success (MsgWithCounter principal_list counter nonce) -> (
    assert(List.Tot.mem p principal_list)
  )
  | _ -> ()
#pop-options

#push-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let authn_conf_send_pred_lemma i p received_serialized_msg =
  match parse_msg_raw received_serialized_msg with
  | Success (MsgWithCounter principal_list counter nonce) -> (
    assert(List.Tot.mem p principal_list)
  )
  | _ -> ()
#pop-options
