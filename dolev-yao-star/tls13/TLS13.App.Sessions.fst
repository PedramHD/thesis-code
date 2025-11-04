/// TLS13.App.Sessions (implementation)
/// ====================================
module TLS13.App.Sessions

module A = LabeledCryptoAPI
module R = LabeledRuntimeAPI

let parse_session_st (serialized_session:bytes) : result session_st =
  r <-- split serialized_session ;
  let (tn,o) = r in
  r <-- bytes_to_string tn ;
  (match r with
  | "InitiatorState" ->
    r <-- split o; let (b,o) = r in
    (match bytes_to_string b with
    | Success (b) ->
      r <-- split o; let (ak,akrr) = r in
      Success (InitiatorState b ak akrr)
    | _ -> Error "not a principal")
  | "InitiatorStSymKey" ->
    r <-- split o; let (b,o) = r in
    (match bytes_to_string b with
    | Success (b) ->
      r <-- split o; let (ak,akrr) = r in
      r <-- split akrr; let (akrr,sym_key) = r in
      Success (InitiatorStSymKey b ak akrr sym_key)
    | _ -> Error "not a principal")
  | "ResponderState" -> 
    r <-- split o; let (b,o) = r in
    (match bytes_to_string b with
    | Success (b) -> 
      r <-- split o; let (ak,akrr) = r in
      Success (ResponderState b ak akrr)
    | _ -> Error "Not a principal")
  | _ -> Error "not a session state")

let includes_lemma (p:principal) (s:nat) (v:nat) : Lemma (includes_ids [P p] [V p s v]) [SMTPat (includes_ids [P p] [V p s v])] = ()

let serialize_valid_session_st pred i p si vi st =
  match st with
   |InitiatorState b ak akrr -> 
     assert(A.can_flow i (A.get_label (tls13_app_key_usages pred) ak) (readers [P p])); 
     A.can_flow_principal i p;
     assert(A.can_flow i (A.get_label (tls13_app_key_usages pred) ak) (readers [V p si vi]));
     A.concat (A.string_to_labeled_bytes #(tls13_app_global_usage pred) #i #(readers [V p si vi]) ("InitiatorState"))
       (A.concat (A.string_to_labeled_bytes #(tls13_app_global_usage pred) #i #(readers [V p si vi]) (b))
	    (A.concat ak akrr))
   |InitiatorStSymKey b ak akrr sym_key -> 
     assert(A.can_flow i (A.get_label (tls13_app_key_usages pred) ak) (readers [P p])); 
     A.can_flow_principal i p;
     assert(A.can_flow i (A.get_label (tls13_app_key_usages pred) ak) (readers [V p si vi]));
     A.can_flow_from_join i (readers [P b]) (readers [P p]);
     A.rand_is_secret #(tls13_app_global_usage pred) #i #(join (readers [P p]) (readers [P b])) #(aead_usage "AEAD.Symmetric_Send_Key")  sym_key;
     assert(A.get_label (tls13_app_key_usages pred) sym_key == join (readers [P p]) (readers [P b]));
     assert(A.can_flow i (A.get_label (tls13_app_key_usages pred) sym_key) (readers [P p]));
     assert(A.can_flow i (A.get_label (tls13_app_key_usages pred) sym_key) (readers [V p si vi]));
     A.concat (A.string_to_labeled_bytes #(tls13_app_global_usage pred) #i #(readers [V p si vi]) ("InitiatorStSymKey"))
       (A.concat (A.string_to_labeled_bytes #(tls13_app_global_usage pred) #i #(readers [V p si vi]) (b))
	    (A.concat ak (A.concat akrr sym_key)))
   |ResponderState b ak akrr ->
     A.can_flow_transitive i (A.get_label (tls13_app_key_usages pred) ak) (readers [P p]) (readers [V p si vi]);
     A.can_flow_transitive i (A.get_label (tls13_app_key_usages pred) akrr) (readers [P p]) (readers [V p si vi]);
     A.concat (A.string_to_labeled_bytes #(tls13_app_global_usage pred) #i #(readers [V p si vi]) ("ResponderState")) 
	      (A.concat (A.string_to_labeled_bytes #(tls13_app_global_usage pred) #i #(readers [V p si vi]) (b)) (A.concat ak akrr))

#push-options "--z3rlimit 100"
let parse_valid_serialize_session_st_lemma pred i p si vi ss =
   match ss with
   |InitiatorState b ak akrr -> 
      A.can_flow_transitive i (A.get_label (tls13_app_key_usages pred) ak) (readers [P p]) (readers [V p si vi]);
      A.can_flow_transitive i (A.get_label (tls13_app_key_usages pred) akrr) (readers [P p]) (readers [V p si vi])
   |InitiatorStSymKey b ak akrr sym_key -> 
      A.can_flow_transitive i (A.get_label (tls13_app_key_usages pred) ak) (readers [P p]) (readers [V p si vi]);
      A.can_flow_transitive i (A.get_label (tls13_app_key_usages pred) akrr) (readers [P p]) (readers [V p si vi]);
      A.can_flow_from_join i (readers [P b]) (readers [P p]);
      A.rand_is_secret #(tls13_app_global_usage pred) #i #(join (readers [P p]) (readers [P b])) #(aead_usage "AEAD.Symmetric_Send_Key")  sym_key;
      A.can_flow_transitive i (A.get_label (tls13_app_key_usages pred) sym_key) (readers [P p]) (readers [V p si vi])
   |ResponderState b ak akrr -> 
     A.can_flow_transitive i (A.get_label (tls13_app_key_usages pred) ak) (readers [P p]) (readers [V p si vi]);
     A.can_flow_transitive i (A.get_label (tls13_app_key_usages pred) akrr) (readers [P p]) (readers [V p si vi])
#pop-options

