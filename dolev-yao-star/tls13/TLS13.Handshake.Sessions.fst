/// TLS13.Handshake.Sessions (implementation)
/// ==========================================
module TLS13.Handshake.Sessions

module A = LabeledCryptoAPI
module R = LabeledRuntimeAPI

let parse_session_st (serialized_session:bytes) : result session_st =
 r <-- split serialized_session ;
  let (tn,o) = r in
  r <-- bytes_to_string tn ;
  (match r with
  | "InitiatorSentMsg1" ->
    r <-- split o; let (b,x) = r in
    (match bytes_to_string b with
    | Success (b) -> Success (InitiatorSentMsg1 b x)
    | _ -> Error "Not a principal")
  | "ResponderSentMsg2" -> 
    r <-- split o; let (b,o) = r in
    (match bytes_to_string b with
    | Success (b) -> 
      r <-- split o; let (gx,gyk) = r in
      r <-- split gyk; let (gy,k) = r in
      Success (ResponderSentMsg2 b gx gy k)
    | _ -> Error "Not a principal")
  | "InitiatorSentMsg3" ->
    r <-- split o; let (b,o) = r in
    (match bytes_to_string b with
    | Success (b) ->
      r <-- split o; let (gy,k) = r in
      r <-- split k; let (mk, ak) = r in
      r <-- split ak; let (ak, akrr) = r in
      Success (InitiatorSentMsg3 b gy mk ak akrr)
    | _ -> Error "not a principal")
  | "ResponderReceivedMsg3" ->
    r <-- split o; let (b,o) = r in
    (match bytes_to_string b with
    | Success (b) -> 
      r <-- split o; let (gx,gyk) = r in
      r <-- split gyk; let (gy,k) = r in
      r <-- split k; let (k,akrr) = r in
      Success (ResponderReceivedMsg3 b gx gy k akrr)
    | _ -> Error "Not a principal")
  | "TLSApp" -> Success (TLSApp o)
  | _ -> Error "not a session state")

let includes_lemma (p:principal) (s:nat) (v:nat) : Lemma (includes_ids [P p] [V p s v]) [SMTPat (includes_ids [P p] [V p s v])] = ()

let serialize_valid_session_st pred i p si vi st =
  match st with
   |TLSApp s -> A.concat (A.string_to_labeled_bytes #(tls13_gu pred) #i #(readers [V p si vi]) ("TLSApp")) s
   |InitiatorSentMsg1 b x ->
    A.concat (A.string_to_labeled_bytes #(tls13_gu pred) #i #(readers [V p si vi]) ("InitiatorSentMsg1"))
	      (A.concat (A.string_to_labeled_bytes #(tls13_gu pred) #i #(readers [V p si vi]) (b)) x)
   |ResponderSentMsg2 b gx gy k ->
    A.can_flow_transitive i (A.get_label (tls13_key_usages pred) k) (readers [P p]) (readers [V p si vi]);
    A.concat (A.string_to_labeled_bytes #(tls13_gu pred) #i #(readers [V p si vi]) ("ResponderSentMsg2"))
	     (A.concat (A.string_to_labeled_bytes #(tls13_gu pred) #i #(readers [V p si vi]) (b)) (A.concat gx (A.concat gy k)))
   |InitiatorSentMsg3 b gy mk ak akrr ->
    assert(A.can_flow i (A.get_label (tls13_key_usages pred) ak) (readers [V p si vi]));
    assert(A.can_flow i (A.get_label (tls13_key_usages pred) mk) (readers [V p si vi]));
    A.concat (A.string_to_labeled_bytes #(tls13_gu pred) #i #_ ("InitiatorSentMsg3"))
	   (A.concat (A.string_to_labeled_bytes #(tls13_gu pred) #i (b)) (A.concat gy (A.concat mk (A.concat ak akrr))))
   |ResponderReceivedMsg3 b gx gy k akrr ->
    A.can_flow_transitive i (A.get_label (tls13_key_usages pred) k) (readers [P p]) (readers [V p si vi]);
    A.concat (A.string_to_labeled_bytes #(tls13_gu pred) #i #(readers [V p si vi]) ("ResponderReceivedMsg3"))
	     (A.concat (A.string_to_labeled_bytes #(tls13_gu pred) #i #(readers [V p si vi]) (b)) (A.concat gx (A.concat gy (A.concat k akrr))))
    
#push-options "--z3rlimit 100"
let parse_valid_serialize_session_st_lemma pred i p si vi ss =
   match ss with
   |TLSApp s -> ()
   |InitiatorSentMsg1 b x -> ()
   |ResponderSentMsg2 b gx gy k -> 
     A.can_flow_transitive i (A.get_label (tls13_key_usages pred) k) (readers [P p]) (readers [V p si vi])
   |InitiatorSentMsg3 b gy mk ak akrr -> 
     A.can_flow_transitive i (A.get_label (tls13_key_usages pred) ak) (readers [P p]) (readers [V p si vi]);
          A.can_flow_transitive i (A.get_label (tls13_key_usages pred) akrr) (readers [P p]) (readers [V p si vi])
   |ResponderReceivedMsg3 b gx gy k akrr -> 
     A.can_flow_transitive i (A.get_label (tls13_key_usages pred) k) (readers [P p]) (readers [V p si vi]);
          A.can_flow_transitive i (A.get_label (tls13_key_usages pred) akrr) (readers [P p]) (readers [V p si vi])
#pop-options

let get_responder_session_tls pred i initiator responder = 
  let filter si vi st = match parse_session_st st with
    | Success (InitiatorSentMsg3 b _ _ _ _) 
    | Success (InitiatorSentMsg1 b _) -> b = responder
    | _ -> false in
  match LabeledPKI.find_session #(tls13 pred) #i initiator filter with
  | Some (|si,vi,st|) ->
    (match parse_session_st st with
    | Success (InitiatorSentMsg3 b gy ak mk akrr) -> Some (si, vi, InitiatorSentMsg3 b gy ak mk akrr) 
    | Success (InitiatorSentMsg1 b x) -> Some (si, vi, InitiatorSentMsg1 b x) 
    |_ -> error "not the right state")
  | None -> None

let get_initiator_session_tls pred i initiator responder = 
  let filter si vi st = match parse_session_st st with
    | Success (ResponderReceivedMsg3 a _ _ _ _) 
    | Success (ResponderSentMsg2 a _ _ _) -> a = initiator
    | _ -> false in
  match LabeledPKI.find_session #(tls13 pred) #i responder filter with
  | Some (|si,vi,st|) ->
    (match parse_session_st st with
    | Success (ResponderReceivedMsg3 a gx gy k ak) -> Some (si, vi, ResponderReceivedMsg3 a gx gy k ak) 
    | Success (ResponderSentMsg2 a gx gy k) -> Some (si, vi, ResponderSentMsg2 a gx gy k) 
    | _ -> error "not the right state")
  | None -> None

