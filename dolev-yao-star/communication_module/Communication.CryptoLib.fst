/// Communication.CryptoLib (Implementation)
/// ========================================

module Communication.CryptoLib

let is_valid_later extended_gu i j t = ()

let empty_lemma #extended_gu #i = ()

let len_lemma #extended_gu #i #l b = ()

let string_to_bytes_lemma #extended_gu #i s = ()

let bytes_to_string_lemma #extended_gu #i #l t = ()

let nat_to_bytes_lemma #extended_gu #i len s = ()

let bytes_to_nat_lemma #extended_gu #i #l t = ()

let bytestring_to_bytes_lemma #extended_gu #i s = ()

let bytes_to_bytestring_lemma #extended_gu #i #l t = ()

let bool_to_bytes_lemma #extended_gu #i s = ()

let bytes_to_bool_lemma #extended_gu #i #l t = ()

let concat_len_prefixed_lemma #extended_gu #i #l ll t1 t2 = ()

let split_len_prefixed_lemma #extended_gu #i #l ll t = ()

let concat_lemma #extended_gu #i #l t1 t2 = ()

let split_lemma #extended_gu #i #l t = ()

let split_at_lemma #extended_gu #i #l len t = ()

let pk_lemma #extended_gu #i #l sk = ()

let sk_label_lemma extended_gu i t l = LC.sk_label_lemma (send_preds_global_usage extended_gu) i t l

let pke_enc_lemma #extended_gu #i #nl pk n m = ()


let pke_dec_lemma #extended_gu #i #l private_key ciphertext = ()

let aead_enc_lemma #extended_gu #i #l k iv m ad = ()

let aead_dec_lemma #extended_gu #i #l k iv c ad = ()

let vk_lemma #extended_gu #i #l sk = ()

let sign_lemma #extended_gu #i #l #l' k n m = ()

let verify_lemma #extended_gu #i #l1 #l2 pk m s =
  assert(forall l s. is_verification_key extended_gu i pk l s ==> LC.is_verification_key (send_preds_global_usage extended_gu) i pk l s )

let verification_key_label_lemma extended_gu i t l =
  LC.verification_key_label_lemma (send_preds_global_usage extended_gu) i t l


let mac_lemma #extended_gu #i #l #l' k m = ()

let hash_lemma #extended_gu #i #l m = ()


let extract_lemma #extended_gu #i #l #l' k salt = ()
let expand_lemma #extended_gu #i #l #l' k info = ()

let dh_pk_lemma #extended_gu #i #l sk = ()

let dh_key_label_lemma extended_gu i b = 
   LC.dh_key_label_lemma (send_preds_global_usage extended_gu) i b

let dh_lemma #extended_gu #i #l sk pk = ()


let strings_are_publishable_forall p = LC.strings_are_publishable_forall (send_preds_global_usage p)
let nats_are_publishable_forall p = LC.nats_are_publishable_forall (send_preds_global_usage p)
let bytestrings_are_publishable_forall p = LC.bytestrings_are_publishable_forall (send_preds_global_usage p)

let bools_are_publishable_forall p = LC.bools_are_publishable_forall (send_preds_global_usage p)

let splittable_term_publishable_implies_components_publishable_forall p = 
    LC.splittable_term_publishable_implies_components_publishable_forall (send_preds_global_usage p)

let splittable_at_term_publishable_implies_components_publishable_forall p = 
  LC.splittable_at_term_publishable_implies_components_publishable_forall (send_preds_global_usage p)

let concatenation_publishable_implies_components_publishable_forall p = LC.concatenation_publishable_implies_components_publishable_forall (send_preds_global_usage p)

let public_key_is_publishable_if_private_key_is_publishable_forall p = LC.public_key_is_publishable_if_private_key_is_publishable_forall (send_preds_global_usage p)

let pke_ciphertext_publishable_if_key_and_msg_are_publishable_forall p = LC.pke_ciphertext_publishable_if_key_and_msg_are_publishable_forall (send_preds_global_usage p)

let pke_plaintext_publishable_if_key_and_ciphertext_publishable_forall p = LC.pke_plaintext_publishable_if_key_and_ciphertext_publishable_forall (send_preds_global_usage p)

let aead_enc_ciphertext_publishable_if_key_and_msg_are_publishable_forall p = LC.aead_enc_ciphertext_publishable_if_key_and_msg_are_publishable_forall (send_preds_global_usage p)

let aead_dec_plaintext_publishable_if_key_and_ciphertext_publishable_forall p = LC.aead_dec_plaintext_publishable_if_key_and_ciphertext_publishable_forall (send_preds_global_usage p)

let verif_key_is_publishable_if_private_key_is_publishable_forall p = LC.verif_key_is_publishable_if_private_key_is_publishable_forall (send_preds_global_usage p)

let sig_is_publishable_if_key_and_msg_are_publishable_forall p = LC.sig_is_publishable_if_key_and_msg_are_publishable_forall (send_preds_global_usage p)

let mac_is_publishable_if_key_and_msg_are_publishable_forall p = LC.mac_is_publishable_if_key_and_msg_are_publishable_forall (send_preds_global_usage p)

let expand_value_publishable_if_secrets_are_publishable_forall p = LC.expand_value_publishable_if_secrets_are_publishable_forall (send_preds_global_usage p)

let extract_value_publishable_if_secrets_are_publishable_forall p = LC.extract_value_publishable_if_secrets_are_publishable_forall (send_preds_global_usage p )

let hash_value_publishable_if_message_is_publishable_forall p = LC.hash_value_publishable_if_message_is_publishable_forall (send_preds_global_usage p)

let dh_public_key_is_publishable_if_private_key_is_publishable_forall p = LC.dh_public_key_is_publishable_if_private_key_is_publishable_forall (send_preds_global_usage p)

let dh_is_publishable_if_keys_are_publishable_forall p = LC.dh_is_publishable_if_keys_are_publishable_forall (send_preds_global_usage p)


let bytes_to_nat_successful_implies_publishable b = LC.bytes_to_nat_successful_implies_publishable b

let bytes_to_string_successful_implies_publishable b = LC.bytes_to_string_successful_implies_publishable b

let components_publishable_implies_splittable_term_publishable p = LC.components_publishable_implies_splittable_term_publishable (send_preds_global_usage p)

let splittable_term_flows_to_label_implies_components_flow_to_label_forall i ll p l t = LC.splittable_term_flows_to_label_implies_components_flow_to_label_forall i ll (send_preds_global_usage p) l t

let rand_is_secret #extended_gu #i #l #u r =
 LC.rand_is_secret #(send_preds_global_usage extended_gu) #i #l #u r

let rand_is_secret_forall_labels #extended_gu #i #u r =
  LC.rand_is_secret_forall_labels #(send_preds_global_usage extended_gu) #i #u r
