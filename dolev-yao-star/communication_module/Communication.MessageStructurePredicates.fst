/// Communication.MessageStructurePredicates
/// ========================================
module Communication.MessageStructurePredicates


let is_authenticated_message verify_index message signed_msg =
  match split signed_msg with
  | Success (msg_with_idx, tag) -> (
    match split msg_with_idx with
    | Error _ -> False
    | Success (verify_idx_bytes, msg) -> (
      match bytes_to_nat verify_idx_bytes with
      | Error _ -> False
      | Success verify_idx' -> (
        exists (key:bytes).
        verify_idx' = verify_index /\
        msg = message /\
       (verify key msg_with_idx tag)
      )
    )
  )
  | _ -> False


let is_confidential_message message confidential_message =
  (exists key rand. confidential_message == (pke_enc key rand message))

let is_authenticated_confidential_message message authn_conf_message =
  exists key rand sender_bytes sign_key sign_nonce confidential_part authenticated_part verify_idx.
  confidential_part == (pke_enc key rand (concat (concat sender_bytes verify_idx) message)) /\
  authenticated_part == sign sign_key sign_nonce confidential_part /\
  authn_conf_message == concat confidential_part authenticated_part



let is_authenticated_message_sent_at trace_index verify_index message signed_msg =
  exists sender' receiver.
    was_message_sent_at trace_index sender' receiver signed_msg /\
    is_authenticated_message verify_index message signed_msg


let is_confidential_message_sent_at trace_index message confidential_msg =
  exists sender' receiver'.
    was_message_sent_at trace_index sender' receiver' confidential_msg /\
    (is_confidential_message message confidential_msg \/
    (exists key iv ad. confidential_msg == (aead_enc key iv message ad)))
    
let is_authenticated_confidential_message_sent_at trace_index message =
  exists sender' receiver' authn_conf_message.
    was_message_sent_at trace_index sender' receiver' authn_conf_message /\
    is_authenticated_confidential_message message authn_conf_message

let is_request_at_idx_injective_forall () =
  let is_request_at_idx_injective (request_payload1:bytes) (request_payload2:bytes) (send_idx1:nat) (send_idx2:nat) (sym_key1:bytes) (sym_key2:bytes) :
  Lemma (requires (
                  is_request_at_idx request_payload1 send_idx1 sym_key1 /\
                  is_request_at_idx request_payload2 send_idx2 sym_key2 /\
                  send_idx1 = send_idx2
        ))
        (ensures (request_payload1 == request_payload2 /\ sym_key1 == sym_key2))
        [SMTPat (is_request_at_idx request_payload1 send_idx1 sym_key1); SMTPat (is_request_at_idx request_payload2 send_idx2 sym_key2)]
  =
    concat_uniqueness_lemma ();
    assert(forall a b c d. (concat a b) = (concat c d) ==> a = c /\ b = d);

    aead_uniqueness_lemma();
    assert(forall a b c d a' b' c' d' req_payload1 req_payload2.
     (aead_enc a b (concat c req_payload1) d)  == (aead_enc a' b' (concat c' req_payload2) d')
     ==>
     req_payload1 == req_payload2);

    concat_not_equal_pke_enc_lemma ();
    concat_not_equal_aead_enc_lemma ();
    pke_enc_not_equal_aead_enc_lemma ();
    // assert(forall pke_key pke_rand sym_key sym_key1 receiver_bytes sender_bytes rpayload1 rpayload2 tag ad sym_key2 iv iv1 enc_sym_key ad1.
    //         ~ ( (pke_enc pke_key pke_rand (concat (concat sym_key1 (concat sender_bytes receiver_bytes)) rpayload1)) ==
    assert(forall pke_key pke_rand sym_key sym_key1 receiver_bytes sender_bytes rpayload1 rpayload2 tag ad sym_key2 iv iv1 enc_sym_key ad1.
            ~ ( (pke_enc pke_key pke_rand (concat sym_key1 rpayload1)) ==
                (concat enc_sym_key (concat iv (aead_enc sym_key2 iv (concat tag rpayload2) ad)))
              ) /\
	    ~ ( (pke_enc pke_key pke_rand (concat (concat sym_key1 (concat sender_bytes receiver_bytes)) rpayload1)) ==
                aead_enc sym_key iv1 (concat enc_sym_key (concat sender_bytes receiver_bytes)) ad1
              ) /\
	    ~ ( (concat enc_sym_key (concat iv (aead_enc sym_key2 iv (concat tag rpayload2) ad))) ==
                aead_enc sym_key iv1 (concat enc_sym_key (concat sender_bytes receiver_bytes)) ad1
              )  
           )
  in ()
