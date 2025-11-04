/// Communication.Sessions.Lemmas
/// =============================

module Communication.Sessions.Lemmas

friend Communication.Sessions

let serialized_session_st_flows_to_principal_state_session pr gu i p si vi st =
   match st with
   | APP _ -> ()
   | CommunicationState request_send_idx sym_key responder -> (

     assert(was_rand_generated_before i sym_key (join (readers [P p]) (readers [P responder])) (aead_usage "AEAD.Symmetric_Send_Key"));
     LC.rand_is_secret #gu #i #(join (readers [P p]) (readers [P responder])) #(aead_usage "AEAD.Symmetric_Send_Key") sym_key;
     assert(LC.can_flow i (LC.get_label gu.LC.key_usages sym_key) (join (readers [P p]) (readers [P responder])));

     assert(
       concat (string_to_bytes "CommunicationState") (concat (nat_to_bytes 0 request_send_idx) (concat sym_key (string_to_bytes responder))) ==
       LC.concat #gu #i #(join (readers [P p]) (readers [P responder])) (LC.string_to_bytes #gu #i "CommunicationState")  (LC.concat #gu #i #(join (readers [P p]) (readers [P responder]))
         (LC.nat_to_bytes #gu #i 0 request_send_idx) (LC.concat #gu #i #(join (readers [P p]) (readers [P responder])) sym_key (LC.string_to_bytes #gu #i responder))));

     LC.can_flow_from_join i (readers [P p]) (readers [P responder]);
     assert(includes_ids [P p] [V p si 0]);
     LC.includes_can_flow_lemma i [P p] [V p si vi]
    )


let parse_serialize_session_st_lemma ss = ()


let serialized_session_st_is_msg extended_gu i l ss =
  let serialized_ss = LC.concat #(send_preds_global_usage extended_gu) #i #l (LC.string_to_bytes #(send_preds_global_usage extended_gu) #i "SEND_APP") ss in
  ()


let parsed_app_session_st_is_msg extended_gu i l ss =
  match split ss with
  | Success (tn, o) -> (
    match bytes_to_string tn with
    | Success "SEND_APP" -> (
      LC.splittable_term_flows_to_label_implies_components_flow_to_label_forall i 4 (send_preds_global_usage extended_gu) l ss;
      split_based_on_split_len_prefixed_lemma ss;
      assert(is_succ2 (CryptoLib.split_len_prefixed 4 ss) tn o)
    )
    | _ -> ()
  )
  | _ -> ()
