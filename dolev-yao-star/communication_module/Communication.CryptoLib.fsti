/// Communication.CryptoLib
/// =======================
///
/// The CryptoLib API, lifted to the Communication Layer.

module Communication.CryptoLib

open SecrecyLabels
module C = CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
module LC = LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI
open Communication.MessageStructurePredicates
open Communication.UsagePredicates
open Communication.Sessions
open Communication.Preds

(**
    The application layer should not care about the global usages used by the send layer internally,
    but only about those that are exposed to the application layer (i.e.: the crypto usage
    predicates and the send function predicates).
*)

let pke_pred (extended_gu:extended_global_usage) i s k p = exists j. later_than i j /\ extended_gu.higher_layer_gu.usage_preds.can_pke_encrypt j s k p
let aead_pred (extended_gu:extended_global_usage) i s k p ad = exists j. later_than i j /\ extended_gu.higher_layer_gu.usage_preds.can_aead_encrypt j s k p ad
let mac_pred (extended_gu:extended_global_usage) i s k p = exists j. later_than i j /\ extended_gu.higher_layer_gu.usage_preds.can_mac j s k p
let sign_pred (extended_gu:extended_global_usage) i s k p = exists j. later_than i j /\ extended_gu.higher_layer_gu.usage_preds.can_sign j s k p


let is_valid (extended_gu:extended_global_usage) i b = LC.is_valid (send_preds_global_usage extended_gu) i b


val is_valid_later : (extended_gu:extended_global_usage) -> i:timestamp -> j:timestamp -> t:C.bytes ->
    Lemma ((is_valid extended_gu i t /\ later_than j i) ==> (is_valid extended_gu j t))
          [SMTPat (is_valid extended_gu i t); SMTPat (later_than j i)]

let is_labeled (extended_gu:extended_global_usage) (i:timestamp) (b:C.bytes) (l:label) = LC.is_labeled (send_preds_global_usage extended_gu) i b l

let has_usage (extended_gu:extended_global_usage) (i:timestamp) (b:C.bytes) (u:C.usage) = LC.has_usage (send_preds_global_usage extended_gu) i b u

let is_secret (extended_gu:extended_global_usage) (i:timestamp) (b:C.bytes) (l:label) (u:C.usage) = LC.is_secret (send_preds_global_usage extended_gu) i b l u

let is_msg (extended_gu:extended_global_usage) i b l = LC.is_msg (send_preds_global_usage extended_gu) i b l

let is_publishable (extended_gu:extended_global_usage) i b = LC.is_publishable (send_preds_global_usage extended_gu) i b

let lbytes (extended_gu:extended_global_usage) i l = LC.lbytes (send_preds_global_usage extended_gu) i l
let msg (extended_gu:extended_global_usage) i l = LC.msg (send_preds_global_usage extended_gu) i l
let secret (extended_gu:extended_global_usage) i l u = LC.secret (send_preds_global_usage extended_gu) i l u



(* Produces an emtpy term (always labeled public) *)
let empty (#extended_gu:extended_global_usage) (#i:timestamp) : lbytes extended_gu i public = LC.empty #(send_preds_global_usage extended_gu) #i

val empty_lemma: (#extended_gu:extended_global_usage) -> #i:timestamp ->
  Lemma (empty #extended_gu #i == C.empty)
        [SMTPat (empty #extended_gu #i)]


(* Length of the term (only relevant for concrete execution) *)
let len (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (t:lbytes extended_gu i l) : nat = LC.len #(send_preds_global_usage extended_gu) #i #l t

val len_lemma: (#extended_gu:extended_global_usage) -> #i:timestamp -> #l:label -> b:lbytes extended_gu i l ->
  Lemma (len #extended_gu #i #l b == C.len b)
        [SMTPat (len #extended_gu #i #l b)]

(* Produce a "literal" term from a string, always labeled public *)
let string_to_bytes (#extended_gu:extended_global_usage) (#i:timestamp) (s:string) : Tot (lbytes extended_gu i public) = LC.string_to_bytes #(send_preds_global_usage extended_gu) #i s
val string_to_bytes_lemma: (#extended_gu:extended_global_usage) -> #i:timestamp -> s:string ->
  Lemma (ensures (string_to_bytes #extended_gu #i s == C.string_to_bytes s))
        [SMTPat (string_to_bytes #extended_gu #i s)]
// Produce a "literal" term with a specific can_flow (note that these terms are still labeled public!).
let string_to_labeled_bytes (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (s:string) : msg extended_gu i l =
  string_to_bytes #extended_gu #i s

(* Extract the string from a term - if the term was a literal string to begin with *)
let bytes_to_string (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (t:msg extended_gu i l) : result string = LC.bytes_to_string #(send_preds_global_usage extended_gu) #i #l t
val bytes_to_string_lemma: (#extended_gu:extended_global_usage) -> #i:timestamp -> #l:label -> t:msg extended_gu i l ->
  Lemma (match bytes_to_string t with
          | Success s -> C.bytes_to_string t == Success s
          | Error e -> C.bytes_to_string t == Error e)
        [SMTPat (bytes_to_string t)]

let nat_to_bytes (#extended_gu:extended_global_usage) (#i:timestamp) (len:nat) (s:nat) : lbytes extended_gu i public = nat_to_bytes #(send_preds_global_usage extended_gu) #i len s
val nat_to_bytes_lemma: (#extended_gu:extended_global_usage) -> #i:timestamp -> len:nat -> s:nat ->
  Lemma (ensures (nat_to_bytes #extended_gu #i len s == C.nat_to_bytes len s))
        [SMTPat (nat_to_bytes #extended_gu #i len s)]


let nat_to_labeled_bytes (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (len s:nat) :  msg extended_gu i l =
  nat_to_bytes #extended_gu #i len s


let bytes_to_nat (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (t:msg extended_gu i l) : result nat = LC.bytes_to_nat #(send_preds_global_usage extended_gu) #i #l t

val bytes_to_nat_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> t:msg extended_gu i l ->
  Lemma (match bytes_to_nat t with
          | Success s -> C.bytes_to_nat t == Success s
          | Error e -> C.bytes_to_nat t == Error e)
        [SMTPat (bytes_to_nat t)]

let bytestring_to_bytes (#extended_gu:extended_global_usage) (#i:timestamp) (s:C.bytestring) : lbytes extended_gu i public = LC.bytestring_to_bytes #(send_preds_global_usage extended_gu) #i s

val bytestring_to_bytes_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> s:C.bytestring ->
  Lemma (ensures (bytestring_to_bytes #extended_gu #i s == C.bytestring_to_bytes s))
        [SMTPat (bytestring_to_bytes #extended_gu #i s)]

let bytes_to_bytestring (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (t:msg extended_gu i l) : result C.bytestring = LC.bytes_to_bytestring #(send_preds_global_usage extended_gu) #i #l t
val bytes_to_bytestring_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> t:msg extended_gu i l ->
  Lemma (match bytes_to_bytestring t with
          | Success s -> C.bytes_to_bytestring t == Success s
          | Error e -> C.bytes_to_bytestring t == Error e)
        [SMTPat (bytes_to_bytestring t)]


let bool_to_bytes (#extended_gu:extended_global_usage) (#i:timestamp) (s:bool) : lbytes extended_gu i public = LC.bool_to_bytes #(send_preds_global_usage extended_gu) #i s
val bool_to_bytes_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> s:bool ->
  Lemma (ensures (bool_to_bytes #extended_gu #i s == C.bool_to_bytes s))
        [SMTPat (bool_to_bytes #extended_gu #i s)]

let bytes_to_bool (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (t:msg extended_gu i l) : result bool = LC.bytes_to_bool #(send_preds_global_usage extended_gu) #i #l t
val bytes_to_bool_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> t:msg extended_gu i l ->
  Lemma (match bytes_to_bool t with
          | Success s -> C.bytes_to_bool t == Success s
          | Error e -> C.bytes_to_bool t == Error e)
        [SMTPat (bytes_to_bool t)]

/// Paring and splitting
/// ~~~~~~~~~~~~~~~~~~~~
let concat_len_prefixed (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (ll:nat) (m1:msg extended_gu i l) (m2:msg extended_gu i l) : msg extended_gu i l = LC.concat_len_prefixed #(send_preds_global_usage extended_gu) #i #l ll m1 m2
val concat_len_prefixed_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> ll:nat -> t1:msg extended_gu i l -> t2:msg extended_gu i l ->
    Lemma (ensures (concat_len_prefixed #extended_gu #i #l ll t1 t2 == C.concat_len_prefixed ll t1 t2))
          [SMTPat (concat_len_prefixed #extended_gu #i #l ll t1 t2)]

let split_len_prefixed (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (ll:nat) (t:msg extended_gu i l) : result (msg extended_gu i l & msg extended_gu i l) =
    LC.split_len_prefixed #(send_preds_global_usage extended_gu) #i #l ll t

val split_len_prefixed_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> ll:nat -> t:msg extended_gu i l ->
    Lemma (match split_len_prefixed ll t with
           | Error x -> C.split_len_prefixed ll t == Error x
           | Success (x,y) -> C.split_len_prefixed ll t == Success (x,y))
          [SMTPat (split_len_prefixed ll t)]

let concat
  (#extended_gu:extended_global_usage)
  (#i:timestamp)
  (#l:label)
  (b1:msg extended_gu i l)
  (b2:msg extended_gu i l)
  :
  b:msg extended_gu i l{get_label extended_gu.higher_layer_gu.key_usages b == meet (get_label extended_gu.higher_layer_gu.key_usages b1) (get_label extended_gu.higher_layer_gu.key_usages b2)}
  = LC.concat #(send_preds_global_usage extended_gu) #i #l b1 b2 //note that the send layer does not change the key usages that are provided by the higher layer


val concat_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> t1:msg extended_gu i l -> t2:msg extended_gu i l ->
    Lemma (ensures (concat #extended_gu #i #l t1 t2 == C.concat t1 t2))
          [SMTPat (concat #extended_gu #i #l t1 t2)]

let split (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (t:msg extended_gu i l) : result (msg extended_gu i l & msg extended_gu i l) = LC.split #(send_preds_global_usage extended_gu) #i #l t

val split_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> t:msg extended_gu i l ->
    Lemma (match split t with
           | Error x -> C.split t == Error x
           | Success (x,y) -> C.split t == Success (x,y))
          [SMTPat (split t)]

let raw_concat #extended_gu #i l t1 t2 = concat_len_prefixed #extended_gu #i #l 0 t1 t2

let split_at (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (len:nat) (t:msg extended_gu i l) : result (msg extended_gu i l & msg extended_gu i l) =
  LC.split_at #(send_preds_global_usage extended_gu) #i #l len t

val split_at_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> len:nat -> t:msg extended_gu i l ->
    Lemma (match split_at len t with
           | Error x -> C.split_at len t == Error x
           | Success (x,y) -> C.split_at len t == Success (x,y))
          [SMTPat (split_at len t)]

/// Asymmetric Encryption
/// ~~~~~~~~~~~~~~~~~~~~~

let is_private_dec_key extended_gu i b l s = is_secret extended_gu i b l (C.pke_usage s)

let is_public_enc_key extended_gu i b l s = is_publishable extended_gu i b /\ (exists sk. is_secret extended_gu i sk l (C.pke_usage s) /\ b == C.pk sk)

let is_public_enc_key_later_lemma extended_gu i b l s :
    Lemma (forall j. is_public_enc_key extended_gu i b l s /\ i < j ==> is_public_enc_key extended_gu j b l s)
          [SMTPat (is_public_enc_key extended_gu i b l s)] = assert (forall j. i < j ==> later_than j i)

type private_dec_key extended_gu (i:timestamp) (l:label) s = b:C.bytes{is_private_dec_key extended_gu i b l s}
type public_enc_key extended_gu (i:timestamp) (l:label) s = b:C.bytes{is_public_enc_key extended_gu i b l s}

let pk (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (k:lbytes extended_gu i l) : lbytes extended_gu i public = LC.pk #(send_preds_global_usage extended_gu) #i #l k

val pk_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> sk:lbytes extended_gu i l ->
  Lemma (ensures (pk sk == C.pk sk /\
                  (forall s. is_private_dec_key extended_gu i sk l s ==>
                        (is_public_enc_key extended_gu i (pk sk) l s /\
                         get_sk_label extended_gu.higher_layer_gu.key_usages (pk sk) == get_label extended_gu.higher_layer_gu.key_usages sk))))
        [SMTPat (pk sk)]

val sk_label_lemma : extended_gu:extended_global_usage -> i:timestamp -> t:C.bytes -> l:label -> Lemma (forall s. is_public_enc_key extended_gu i t l s ==> get_sk_label extended_gu.higher_layer_gu.key_usages t == l)


/// Randomness used in asymmetric encryption
let is_pke_nonce extended_gu i b l = is_secret extended_gu i b l (C.nonce_usage "PKE_NONCE")
let pke_nonce extended_gu i l = b:C.bytes{is_pke_nonce extended_gu i b l}


let does_not_interfere_with_send_layer_conf_authn_send m =
  match C.split m with
    | Error e -> True
    | Success (sender_and_timestamp_bytes, msg) -> (
      match C.split sender_and_timestamp_bytes with
      | Error e -> True
      | Success (sender_bytes, timestamp_bytes) -> False
    )

let pke_string_match s m = (match s with
            | "SEND_LAYER_CONF_SEND" -> False
            | "SEND_LAYER_CONF_AUTHN_SEND" -> does_not_interfere_with_send_layer_conf_authn_send m
            | "SEND_LAYER_CONF_REQUEST_ONLY_PKE" -> False
            | "SEND_LAYER_CONF_REQUEST_HYBRID" -> False
            | _ -> True
            )

let pke_enc
    (#extended_gu:extended_global_usage)
    (#i:timestamp)
    (#nl:label)
    (public_key:msg extended_gu i public)
    (nonce:pke_nonce extended_gu i nl)
    (message:msg extended_gu i (get_sk_label extended_gu.higher_layer_gu.key_usages public_key){
      can_flow i (get_label extended_gu.higher_layer_gu.key_usages message) nl /\
      (forall s. is_public_enc_key extended_gu i public_key (get_sk_label extended_gu.higher_layer_gu.key_usages public_key) s ==>
            pke_pred extended_gu i s public_key message
            /\ pke_string_match s message
      )
      }
    )
    :
    msg extended_gu i public
    = LC.pke_enc #(send_preds_global_usage extended_gu) #i #nl public_key nonce message

val pke_enc_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #nl:label ->
      pk:msg extended_gu i public
    -> n:pke_nonce extended_gu i nl
    -> m:msg extended_gu i (get_sk_label extended_gu.higher_layer_gu.key_usages pk){
        can_flow i (get_label extended_gu.higher_layer_gu.key_usages m) nl /\
        (forall s. is_public_enc_key extended_gu i pk (get_sk_label extended_gu.higher_layer_gu.key_usages pk) s ==>
            pke_pred extended_gu i s pk m
            /\ pke_string_match s m
            )}
    -> Lemma (ensures (pke_enc #extended_gu #i #nl pk n m == C.pke_enc pk n m))
        [SMTPat (pke_enc #extended_gu #i #nl pk n m)]

let pke_dec
    (#extended_gu:extended_global_usage)
    (#i:timestamp)
    (#l:label)
    (private_key:lbytes extended_gu i l{is_publishable extended_gu i private_key \/
                           (exists s. is_private_dec_key extended_gu i private_key l s)} )
    (ciphertext:msg extended_gu i public)
    : result (msg extended_gu i l)
 = LC.pke_dec #(send_preds_global_usage extended_gu) #i #l private_key ciphertext

val pke_dec_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label ->
    private_key:lbytes extended_gu i l{is_publishable extended_gu i private_key \/
                           (exists s. is_private_dec_key extended_gu i private_key l s)} ->
    ciphertext:msg extended_gu i public ->
    Lemma (match pke_dec private_key ciphertext with
           | Success plaintext ->
             C.pke_dec private_key ciphertext == Success plaintext /\
             (forall s. is_private_dec_key extended_gu i private_key l s
               /\ pke_string_match s plaintext
             ==>
             (is_publishable extended_gu i plaintext \/ pke_pred extended_gu i s (C.pk private_key) plaintext)
             )
           | Error x -> C.pke_dec private_key ciphertext == Error x)
          [SMTPat (pke_dec private_key ciphertext)]


let is_aead_key (extended_gu:extended_global_usage) i k l s = LC.is_aead_key (send_preds_global_usage extended_gu) i k l s

type aead_key (extended_gu:extended_global_usage) i l s = LC.aead_key (send_preds_global_usage extended_gu) i l s

let does_not_interfere_with_send_layer_aead (b:C.bytes) = (
      match C.split b with
      | Error e -> True
      | Success (msg_tag_bytes, message) -> (
        match C.bytes_to_string msg_tag_bytes with
        | Error _ -> True
        | Success msg_tag -> (
          match msg_tag with
          | "Send.Layer.Request" -> False
          | "Send.Layer.Response" -> False
          | _ -> True
        )
      )
    )


let aead_enc (#extended_gu:extended_global_usage) (#i:timestamp)  (#l:label)
    (k:lbytes extended_gu i l{is_publishable extended_gu i k \/ (exists s. is_aead_key extended_gu i k l s )})
    (iv:msg extended_gu i public)
    (m:msg extended_gu i l{is_aead_key extended_gu i k l "AEAD.Symmetric_Send_Key" ==> does_not_interfere_with_send_layer_aead m})
    (ad:msg extended_gu i public{forall s. is_aead_key extended_gu i k l s ==>
            aead_pred extended_gu i s k m ad
    })
    : msg extended_gu i public
    =
    LC.aead_enc #(send_preds_global_usage extended_gu) #i #l k iv m ad


val aead_enc_lemma: (#extended_gu:extended_global_usage) -> #i:timestamp -> #l:label ->
    k:lbytes extended_gu i l{is_publishable extended_gu i k \/ (exists s. is_aead_key extended_gu i k l s)} ->
    iv:msg extended_gu i public ->
    m:msg extended_gu i l{is_aead_key extended_gu i k l "AEAD.Symmetric_Send_Key" ==> does_not_interfere_with_send_layer_aead m} ->
    ad:msg extended_gu i public{forall s. is_aead_key extended_gu i k l s ==> aead_pred extended_gu i s k m ad} ->
  Lemma (ensures (aead_enc k iv m ad == C.aead_enc k iv m ad))
        [SMTPat (aead_enc k iv m ad)]


let aead_dec (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label)
    (k:lbytes extended_gu i l{is_publishable extended_gu i k \/ (exists s. is_aead_key extended_gu i k l s)})
    (iv:msg extended_gu i public)
    (c:msg extended_gu i public)
    (ad:msg extended_gu i public)
    :
    result (msg extended_gu i l)
    =
    LC.aead_dec #(send_preds_global_usage extended_gu) #i #l k iv c ad


val aead_dec_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label ->
    k:lbytes extended_gu i l{is_publishable extended_gu i k \/ (exists s. is_aead_key extended_gu i k l s)} ->
    iv:msg extended_gu i public ->
    c:msg extended_gu i public ->
    ad:msg extended_gu i public ->
    Lemma (
      match aead_dec k iv c ad with
      | Success pt ->
        C.aead_dec k iv c ad == Success pt /\
        (
          is_publishable extended_gu i k \/
          (
            exists s. is_aead_key extended_gu i k l s /\
            (
              //if the key is not used by the send layer, or if the message of the plaintext does
              //not collide with messages encrypted on the send layer, then the aead predicate of
              //the higher layer holds true
              (s <> "AEAD.Symmetric_Send_Key"  \/ does_not_interfere_with_send_layer_aead pt) ==>
              (exists j. later_than i j /\ aead_pred extended_gu j s k pt ad)
            )
          )
        )
      | Error s -> C.aead_dec k iv c ad == Error s
    )
    [SMTPat (aead_dec k iv c ad)]



let is_signing_key p i b l s = LC.is_signing_key (send_preds_global_usage p) i b l s
let is_verification_key p i b l s = LC.is_verification_key (send_preds_global_usage p) i b l s
let sign_key p i l s = LC.sign_key (send_preds_global_usage p) i l s
let verify_key p i l s = LC.verify_key (send_preds_global_usage p) i l s


let vk (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (sk:lbytes extended_gu i l) : lbytes extended_gu i public
  = LC.vk #(send_preds_global_usage extended_gu) #i #l sk

val vk_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> sk:lbytes extended_gu i l ->
  Lemma (ensures (vk sk == C.vk sk /\
                  (forall s. is_signing_key extended_gu i sk l s  ==> is_verification_key extended_gu i (vk sk) l s /\ (get_signkey_label extended_gu.higher_layer_gu.key_usages (vk sk) == get_label extended_gu.higher_layer_gu.key_usages sk))))
        [SMTPat (vk sk)]

let does_not_interfere_with_send_layer_sign s =
  (match s with
        | "SEND_LAYER_AUTHN_SEND" -> False
        | "SEND_LAYER_CONF_AUTHN_SEND" -> False
	| "SEND_LAYER_CONF_AUTHN_REQUEST" -> False
        | _ -> True
        )

let sign (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (#l':label)
    (k:lbytes extended_gu i l{is_publishable extended_gu i k \/ (exists s. is_signing_key extended_gu i k l s)})
    (n:lbytes extended_gu i l)
    (m:msg extended_gu i l'{forall s. is_signing_key extended_gu i k l s ==> sign_pred extended_gu i s (C.vk k) m
      /\ does_not_interfere_with_send_layer_sign s
    })
    : msg extended_gu i l'
   = LC.sign #(send_preds_global_usage extended_gu) #i #l #l' k n m

val sign_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> #l':label -> k:lbytes extended_gu i
    l{is_publishable extended_gu i k \/ (exists s. is_signing_key extended_gu i k l s)} -> n:lbytes extended_gu i l
    -> m:msg extended_gu i l'{forall s. is_signing_key extended_gu i k l s ==> sign_pred extended_gu i s (C.vk k) m /\ does_not_interfere_with_send_layer_sign s }
    -> Lemma (ensures(sign k n m == C.sign k n m)) [SMTPat (sign k n m)]

let verify
  (#extended_gu:extended_global_usage) (#i:timestamp) (#l1:label) (#l2:label)
  (pk:msg extended_gu i public) (m:msg extended_gu i l1) (s:msg extended_gu i l2)
  : bool
= LC.verify #(send_preds_global_usage extended_gu) #i #l1 #l2 pk m s

val verify_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l1:label -> #l2:label ->
    pk:msg extended_gu i public -> m:msg extended_gu i l1 -> s:msg extended_gu i l2 ->
    Lemma (if verify pk m s then
            C.verify pk m s /\
            (forall l s. is_verification_key extended_gu i pk l s /\ does_not_interfere_with_send_layer_sign s ==>
                    (can_flow i l public \/ sign_pred extended_gu i s pk m))
         else (C.verify pk m s = false))
  [SMTPat (verify pk m s)]

val verification_key_label_lemma : extended_gu:extended_global_usage -> i:timestamp -> t:C.bytes -> l:label
  -> Lemma (forall s. is_verification_key extended_gu i t l s /\ does_not_interfere_with_send_layer_sign s
      ==> get_signkey_label extended_gu.higher_layer_gu.key_usages t == l)



let is_mac_key p i b l s = LC.is_mac_key (send_preds_global_usage p) i b l s
let mac_key p i l s = LC.mac_key (send_preds_global_usage p) i l s

(*
   The current implementations of the send layer do not use MACs.
*)
let does_not_interfere_with_send_layer_mac s = True

let mac (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (#l':label)
    (k:lbytes extended_gu i l{is_publishable extended_gu i k \/ (exists s. is_mac_key extended_gu i k l s)})
    (m:msg extended_gu i l'{forall s. is_mac_key extended_gu i k l s ==> mac_pred extended_gu i s k m /\ does_not_interfere_with_send_layer_mac s })
    : msg extended_gu i l'
    = LC.mac #(send_preds_global_usage extended_gu) #i #l #l' k m

val mac_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> #l':label ->
    k:lbytes extended_gu i l{is_publishable extended_gu i k \/ (exists s. is_mac_key extended_gu i k l s)} ->
    m:msg extended_gu i l'{forall s. is_mac_key extended_gu i k l s ==> mac_pred extended_gu i s k m /\ does_not_interfere_with_send_layer_mac s} ->
    Lemma (mac k m == C.mac k m)
    [SMTPat (mac k m)]



let hash (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (m:msg extended_gu i l)
 : msg extended_gu i l
 = LC.hash #(send_preds_global_usage extended_gu) #i #l m

val hash_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> m:msg extended_gu i l ->
  Lemma (ensures (hash m == C.hash m /\ get_label extended_gu.higher_layer_gu.key_usages m == get_label extended_gu.higher_layer_gu.key_usages (hash m)))
	[SMTPat (hash m)]




let is_kdf_key p i b l s = is_secret p i b l (C.kdf_usage s)
let kdf_key p i l s = b:C.bytes{is_kdf_key p i b l s}

let extract
  (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (#l':label)
  (k:lbytes extended_gu i l{is_publishable extended_gu i k \/ (exists s. is_kdf_key extended_gu i k l s)})
  (salt:lbytes extended_gu i l')
  : (k':C.bytes{((is_publishable extended_gu i k /\ is_publishable extended_gu i salt) ==> is_publishable extended_gu i k') /\
              (forall s. is_kdf_key extended_gu i k l s ==> (is_labeled extended_gu i k' (join_opt (meet l l') (extended_gu.higher_layer_gu.key_usages.kdf_extend_label s k salt l l')) /\
					      get_usage extended_gu.higher_layer_gu.key_usages k' == extended_gu.higher_layer_gu.key_usages.kdf_extract_usage s k salt))})
    = LC.extract #(send_preds_global_usage extended_gu) #i #l #l' k salt

val extract_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> #l':label ->
    k:lbytes extended_gu i l{is_publishable extended_gu i k \/ (exists s. is_kdf_key extended_gu i k l s)} -> salt:lbytes extended_gu i l' ->
    Lemma (extract #extended_gu #i #l k salt == C.extract k salt) [SMTPat (extract #extended_gu #i #l k salt)]

let expand
  (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (#l':label)
  (k:lbytes extended_gu i l{is_publishable extended_gu i k \/ (exists s. is_kdf_key extended_gu i k l s)})
  (info:msg extended_gu i l')
  : (k':lbytes extended_gu i l{((is_publishable extended_gu i k) ==> is_publishable extended_gu i k') /\
                      (forall s. is_kdf_key extended_gu i k l s ==> (is_labeled extended_gu i k' l /\ get_usage extended_gu.higher_layer_gu.key_usages k' == extended_gu.higher_layer_gu.key_usages.kdf_expand_usage s k info))})
 = LC.expand #(send_preds_global_usage extended_gu) #i #l #l' k info

val expand_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> #l':label -> k:lbytes extended_gu i l{is_publishable extended_gu i k \/ (exists s. is_kdf_key extended_gu i k l s)} -> info:msg extended_gu i l' ->
    Lemma (expand #extended_gu #i #l k info == C.expand k info) [SMTPat (expand #extended_gu #i #l k info)]



let is_dh_private_key p i b l s = LC.is_dh_private_key (send_preds_global_usage p) i b l s
let is_dh_public_key p i b l s = LC.is_dh_public_key (send_preds_global_usage p) i b l s
type dh_private_key p (i:timestamp) (l:label) s = LC.dh_private_key (send_preds_global_usage p) i l s
type dh_public_key p (i:timestamp) (l:label) s = LC.dh_public_key (send_preds_global_usage p) i l s

let dh_pk
  (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label) (sk:lbytes extended_gu i l)
  : lbytes extended_gu i public
= LC.dh_pk #(send_preds_global_usage extended_gu) #i #l sk

val dh_pk_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> sk:lbytes extended_gu i l ->
  Lemma (ensures (dh_pk #extended_gu #i #l sk == C.dh_pk sk /\
                  (forall s. is_dh_private_key extended_gu i sk l s <==> is_dh_public_key extended_gu i (dh_pk #extended_gu #i #l sk) l s)))
        [SMTPat (dh_pk #extended_gu #i #l sk)]
val dh_key_label_lemma : extended_gu:extended_global_usage -> i:timestamp -> b:C.bytes -> Lemma (forall s l. is_dh_public_key extended_gu i b l s ==> get_dhkey_label extended_gu.higher_layer_gu.key_usages b == l)
// val dh_private_key_cannot_be_split : b:C.bytes ->
//   Lemma (forall p i l s. is_dh_private_key p i b l s ==> Error? (CryptoLib.split b))



let dh 
  (#extended_gu:extended_global_usage) (#i:timestamp) (#l:label)
  (sk:lbytes extended_gu i l{is_publishable extended_gu i sk \/ (exists s. is_dh_private_key extended_gu i sk l s)})
  (pk:msg extended_gu i public)
  : (k:lbytes extended_gu i (join l (get_dhkey_label extended_gu.higher_layer_gu.key_usages pk)){
                (is_publishable extended_gu i sk ==> is_publishable extended_gu i k) /\ // can be derived from type of k
                (forall s s' l'. (is_dh_private_key extended_gu i sk l s /\ is_dh_public_key extended_gu i pk l' s') ==>
                            get_usage extended_gu.higher_layer_gu.key_usages k == extended_gu.higher_layer_gu.key_usages.dh_shared_secret_usage s s' k) /\
                (forall s. (is_dh_private_key extended_gu i sk l s /\ extended_gu.higher_layer_gu.key_usages.dh_unknown_peer_usage s k =!= None) ==>
                               get_usage extended_gu.higher_layer_gu.key_usages k == extended_gu.higher_layer_gu.key_usages.dh_unknown_peer_usage s k)})
    = LC.dh #(send_preds_global_usage extended_gu) #i #l sk pk

val dh_lemma: #extended_gu:extended_global_usage -> #i:timestamp -> #l:label ->
              sk:lbytes extended_gu i l{is_publishable extended_gu i sk \/ (exists s. is_dh_private_key extended_gu i sk l s)} -> pk:msg extended_gu i public ->
              Lemma (dh #extended_gu #i #l sk pk == C.dh sk pk)
              [SMTPat (dh sk pk)]



val strings_are_publishable_forall : p:extended_global_usage -> Lemma (forall i (s:string). is_publishable p i (C.string_to_bytes s))
val nats_are_publishable_forall : p:extended_global_usage -> Lemma (forall i (len s:nat). is_publishable p i (C.nat_to_bytes len s))
val bytestrings_are_publishable_forall : p:extended_global_usage -> Lemma (forall i (s:C.bytestring). is_publishable p i (C.bytestring_to_bytes s))
val bools_are_publishable_forall : p:extended_global_usage -> Lemma (forall i (s:bool). is_publishable p i (C.bool_to_bytes s))

val splittable_term_publishable_implies_components_publishable_forall: p:extended_global_usage ->
    Lemma (forall i t ll t_part1 t_part2. (C.is_succ2 (C.split_len_prefixed ll t) t_part1 t_part2 /\ is_publishable p i t) ==>
                                  (is_publishable p i t_part1 /\ is_publishable p i t_part2))

val splittable_at_term_publishable_implies_components_publishable_forall: p:extended_global_usage ->
    Lemma (forall i t ll t_part1 t_part2. (C.is_succ2 (C.split_at ll t) t_part1 t_part2 /\ is_publishable p i t) ==>
                                  (is_publishable p i t_part1 /\ is_publishable p i t_part2))

val concatenation_publishable_implies_components_publishable_forall : p:extended_global_usage ->
    Lemma (forall i l t1 t2. (is_publishable p i (C.concat_len_prefixed l t1 t2)) ==> (is_publishable p i t1 /\ is_publishable p i t2))
val public_key_is_publishable_if_private_key_is_publishable_forall : p:extended_global_usage ->
    Lemma (forall i t. is_publishable p i t  ==> is_publishable p i (C.pk t))
val pke_ciphertext_publishable_if_key_and_msg_are_publishable_forall: p:extended_global_usage ->
    Lemma (forall i pub_key n msg. (is_publishable p i pub_key /\ is_publishable p i n /\ is_publishable p i msg) ==> (is_publishable p i (C.pke_enc pub_key n msg)))
val pke_plaintext_publishable_if_key_and_ciphertext_publishable_forall: p:extended_global_usage ->
  Lemma (forall i priv_key ciphertext plaintext. (C.is_succ (C.pke_dec priv_key ciphertext) plaintext /\ is_publishable p i priv_key /\
                                            is_publishable p i ciphertext) ==> is_publishable p i plaintext)
val aead_enc_ciphertext_publishable_if_key_and_msg_are_publishable_forall: p:extended_global_usage ->
    Lemma (forall i key iv msg ad. (is_publishable p i key /\ is_publishable p i iv /\ is_publishable p i msg /\ is_publishable p i ad) ==>
                           (is_publishable p i (C.aead_enc key msg iv ad)))
val aead_dec_plaintext_publishable_if_key_and_ciphertext_publishable_forall: p:extended_global_usage ->
  Lemma (forall i key iv ciphertext plaintext ad. (C.is_succ (C.aead_dec key iv ciphertext ad) plaintext /\ is_publishable p i key /\
                                          is_publishable p i ciphertext /\ is_publishable p i ad) ==> is_publishable p i plaintext)
val verif_key_is_publishable_if_private_key_is_publishable_forall : p:extended_global_usage ->
    Lemma (forall i t. is_publishable p i t  ==> is_publishable p i (C.vk t))
val sig_is_publishable_if_key_and_msg_are_publishable_forall: p:extended_global_usage ->
    Lemma (forall i t1 t2 t3. (is_publishable p i t1 /\ is_publishable p i t2  /\ is_publishable p i t3) ==> is_publishable p i (C.sign t1 t2 t3))
val mac_is_publishable_if_key_and_msg_are_publishable_forall: p:extended_global_usage ->
    Lemma (forall i t1 t2. (is_publishable p i t1 /\ is_publishable p i t2) ==> is_publishable p i (C.mac t1 t2))
val expand_value_publishable_if_secrets_are_publishable_forall: p:extended_global_usage ->
    Lemma (forall i t1 t2. (is_publishable p i t1 /\ is_publishable p i t2) ==> is_publishable p i (C.expand t1 t2))
val extract_value_publishable_if_secrets_are_publishable_forall: p:extended_global_usage ->
    Lemma (forall i t1 t2. (is_publishable p i t1 /\ is_publishable p i t2) ==> is_publishable p i (C.extract t1 t2))
val hash_value_publishable_if_message_is_publishable_forall: p:extended_global_usage ->
    Lemma (forall i t1. (is_publishable p i t1) ==> is_publishable p i (C.hash t1))
val dh_public_key_is_publishable_if_private_key_is_publishable_forall : p:extended_global_usage ->
    Lemma (forall i t. is_publishable p i t  ==> is_publishable p i (C.dh_pk t))
val dh_is_publishable_if_keys_are_publishable_forall: p:extended_global_usage ->
    Lemma (forall i t1 t2. (is_publishable p i t1 /\ is_publishable p i t2) ==> is_publishable p i (C.dh t1 (C.dh_pk t2)))

val bytes_to_nat_successful_implies_publishable : b:C.bytes -> Lemma (forall i (gu:extended_global_usage). Success? (C.bytes_to_nat b) ==> is_publishable gu i b)
val bytes_to_string_successful_implies_publishable : b:C.bytes -> Lemma (forall i (gu:extended_global_usage). Success? (C.bytes_to_string b) ==> is_publishable gu i b)

val components_publishable_implies_splittable_term_publishable: p:extended_global_usage ->
    Lemma (forall i t ll t_part1 t_part2. (C.is_succ2 (C.split_len_prefixed ll t) t_part1 t_part2 /\ (is_publishable p i t_part1 /\ is_publishable p i t_part2))
                                      ==> is_publishable p i t)

val splittable_term_flows_to_label_implies_components_flow_to_label_forall: i:nat -> ll:nat -> p:extended_global_usage -> l:label -> t:msg p i l ->
    Lemma (forall t_part1 t_part2. (C.is_succ2 (C.split_len_prefixed ll t) t_part1 t_part2  ==>
                                  (is_msg p i t_part1 l) /\ (is_msg p i t_part2 l)))





val rand_is_secret : #extended_gu:extended_global_usage -> #i:timestamp -> #l:label -> #u:C.usage -> r:C.bytes -> Lemma (was_rand_generated_before i r l u ==> is_secret extended_gu i r l u)

val rand_is_secret_forall_labels : #extended_gu:extended_global_usage -> #i:timestamp -> #u:C.usage -> r:C.bytes -> Lemma (forall l. was_rand_generated_before i r l u ==> is_secret extended_gu i r l u)


let restrict
  (#extended_gu:extended_global_usage) (#i:timestamp) (#l1:label) (t:msg extended_gu i l1) (l2:label{can_flow i l1 l2})
  : (t':msg extended_gu i l2{t' == t})
  = LC.restrict #(send_preds_global_usage extended_gu) #i #l1 t l2
