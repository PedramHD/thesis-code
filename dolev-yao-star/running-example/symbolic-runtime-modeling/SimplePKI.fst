/// LabeledPKI (implementation)
/// ============================
module SimplePKI

let serialize_session_st st : bytes =
   match st with
   |SigningKey t secret_key -> concat ((string_to_bytes "SigningKey")) (concat ((string_to_bytes t)) (secret_key))
   |VerificationKey t p public_key -> concat ((string_to_bytes "VerificationKey")) (concat ((string_to_bytes t)) (concat ((string_to_bytes p)) public_key))
   |DHPrivateKey t secret_key -> concat ((string_to_bytes "DHPrivateKey")) (concat ((string_to_bytes t)) secret_key)
   |DHPublicKey t p public_key -> concat ((string_to_bytes "DHPublicKey")) (concat ((string_to_bytes t)) (concat ((string_to_bytes p)) public_key))
   |OneTimeDHPrivKey t secret_key -> concat ((string_to_bytes "OneTimeDHPrivKey")) (concat ((string_to_bytes t)) secret_key)
   |OneTimeDHPubKey t p public_key -> concat ((string_to_bytes "OneTimeDHPubKey")) (concat ((string_to_bytes t)) (concat ((string_to_bytes p)) public_key))
   |DeletedOneTimeKey t -> concat ((string_to_bytes "DeletedOneTimeKey")) ((string_to_bytes t))
   |DecryptionKey t secret_key -> concat ((string_to_bytes "DecryptionKey")) (concat ((string_to_bytes t)) secret_key)
   |EncryptionKey t p public_key -> concat ((string_to_bytes "EncryptionKey")) (concat ((string_to_bytes t)) (concat ((string_to_bytes p)) public_key))
   |APP s -> concat ((string_to_bytes "APP")) s

let parse_session_st (serialized_session:bytes) : result session_st =
  let? r = split serialized_session in
  let (tn,o) = r in
  match? bytes_to_string tn with
  | "APP" -> Success (APP o)
  | "SigningKey" -> (
    let? (tb,sk) = split o in
    let? t = bytes_to_string tb in
    Success (SigningKey t sk))
  | "VerificationKey" -> (
    let? (tb,ppk) = split o in
    let? t = bytes_to_string tb in
    let? (pb,pk) = split ppk in
    let? p = bytes_to_string pb in
    Success (VerificationKey t p pk))
  | "DHPrivateKey" -> (
    let? (tb,sk) = split o in
    let? t = bytes_to_string tb in
    Success (DHPrivateKey t sk))
  | "DHPublicKey" -> (
    let? (tb,ppk) = split o in
    let? t = bytes_to_string tb in
    let? (pb,pk) = split ppk in
    let? p = bytes_to_string pb in
    Success (DHPublicKey t p pk))
  | "OneTimeDHPrivKey" -> (
    let? (tb,sk) = split o in
    let? t = bytes_to_string tb in
    Success (OneTimeDHPrivKey t sk))
  | "OneTimeDHPubKey" -> (
    let? (tb,ppk) = split o in
    let? t = bytes_to_string tb in
    let? (pb,pk) = split ppk in
    let? p = bytes_to_string pb in
    Success (OneTimeDHPubKey t p pk))
  | "DeletedOneTimeKey" -> (
    let? t = bytes_to_string o in
    Success (DeletedOneTimeKey t))
  | "DecryptionKey" -> (
    let? (tb,sk) = split o in
    let? t = bytes_to_string tb in
    Success (DecryptionKey t sk))
  | "EncryptionKey" -> (
    let? (tb,ppk) = split o in
    let? t = bytes_to_string tb in
    let? (pb,pk) = split ppk in
    let? p = bytes_to_string pb in
    Success (EncryptionKey t p pk))
  | _ -> Error "unknown key name"


val parse_serialize_session_st_lemma : ss:session_st ->
    Lemma (Success ss == parse_session_st (serialize_session_st ss))
          [SMTPat (parse_session_st (serialize_session_st ss))]
let parse_serialize_session_st_lemma ss =
  assert_norm(Success ss == parse_session_st (serialize_session_st ss))

let includes_lemma (p:principal) (s:nat) (v:nat) : Lemma (includes_ids [P p] [V p s v]) [SMTPat (includes_ids [P p] [V p s v])] = ()

let new_session p si vi ss =
  let sst = serialize_session_st (APP ss) in
  let now = global_timestamp () in
  if now > 0 then
    match get_last_state_before (now - 1) p with
    | Some (i,v,st) ->
      if si <> Seq.length v then error "incorrect new session number" else
      let new_st = Seq.snoc st sst in
      let new_v = Seq.snoc v vi in
      if(Seq.length new_st <> Seq.length new_v) then error "length of version vector and state vector differ" else
      set_state p new_v new_st
    | _ ->
      if si <> 0 then error "incorrect new session number" else
      let new_st = Seq.create 1 sst in
      let new_v = Seq.create 1 vi in
      set_state p new_v new_st
  else
      if si <> 0 then error "incorrect new session number" else
      let new_st = Seq.create 1 sst in
      let new_v = Seq.create 1 vi in
      set_state p new_v new_st


let update_session p si vi ss =
  let sst = serialize_session_st (APP ss) in
  let now = global_timestamp () in
  if now = 0 then error "no prior session to update" else
    match get_last_state_before (now - 1) p with
    | Some (i,v,st) ->
      if si >= Seq.length v then error "incorrect update session number" else
      if(Seq.length st <> Seq.length v) then error "length of version vector and state vector differ" else
      let new_st = Seq.upd st si sst in
      let new_v = Seq.upd v si vi in
      set_state p new_v new_st
    | _ -> error "no prior session to update"

let get_session p si =
  let now = global_timestamp () in
  if now = 0 then error "no prior session to get" else
    match get_last_state_before (now - 1) p with
    | Some (i,v,st) -> (
      if si >= Seq.length v then error "incorrect get session number" else
      if(Seq.length st <> Seq.length v) then error "length of version vector and state vector differ" else
      let vi = v.[si] in
      let s = st.[si] in
      match parse_session_st s with
      | Success (APP s') -> (|vi,s'|)
      | _ -> error "get_session: not an application state"
    )
    | _ -> error "no prior session to update"

let rec find_session_
  (pi:timestamp) (p:principal) (v:version_vec)
  (st:state_vec)
  (f:nat -> nat -> bytes -> bool) (i:nat{i <= Seq.length st}) :
  Pure (option (si:nat & vi:nat & bytes))
    (requires True)
    (ensures (fun r -> match r with | None -> True
                    | Some (|si,vi,st|) -> f si vi st ))
    (decreases (Seq.length st - i))
=  if i = Seq.length st then None else
   if Seq.length st <> Seq.length v then None else
   if f i v.[i] st.[i] then (
     Some (|i,v.[i],st.[i]|))
   else find_session_ pi p v st f (i+1)

let find_session p f =
  let f' si vi st =
    match parse_session_st st with
    | Success (APP s) -> f si vi s
    | _ -> false in
  let now = global_timestamp () in
  if now = 0 then None else
    match get_last_state_before (now - 1) p with
    | Some (i,v,st) -> (
      match find_session_ now p v st f' 0 with
      | None -> None
      | Some (|si,vi,st|) -> (
          (match parse_session_st st with
          | Success (APP s') ->(assert(f' si vi st);assert(f si vi s'); Some (|si,vi,s'|))
          | _ -> error "find_session: not an application state")
      )
      )
    | _ -> None

let keygen p si kt ts :
  Crypto bytes
  (requires (fun _ -> True))
  (ensures (fun t0 r t1 ->
    match r with
    | Error _ -> t0 == t1
    | Success _ -> trace_len t1 == trace_len t0 + 1)
  ) = gen public (nonce_usage "")

let private_key_st i p si vi (kt:key_type{kt <> OneTimeDH}) ts (sk:bytes) : s:session_st  =
  match kt with
  | SIG -> SigningKey ts sk
  | DH -> DHPrivateKey ts sk
  | PKE -> DecryptionKey ts sk

let public_key_st p peer si vi (kt:key_type{kt <> OneTimeDH}) ts (sk:bytes) : s:session_st =
  match kt with
  | SIG -> VerificationKey ts p (vk sk)
  | DH -> DHPublicKey ts p (dh_pk sk)
  | PKE -> EncryptionKey ts p (pk sk)

let kt2string (kt:key_type) =
  match kt with
  | SIG -> "SIG"
  | DH -> "DH"
  | PKE -> "PKE"
  | OneTimeDH -> "OneTimeDH"

let gen_private_key p kt ts =
  print_string ("generating private key '"^ts^"' of type "^(kt2string kt)^" for '"^p^"'\n");
  let si = new_session_number p in
  let sk = keygen p si kt ts in
  let t1 = global_timestamp () in
  let st = (match kt with | OneTimeDH -> OneTimeDHPrivKey ts sk | _ -> private_key_st t1 p si 0 kt ts sk) in
  let new_ss_st = serialize_session_st st in
  new_session p si 0 new_ss_st;
  si

let get_private_key p kt ts =
  let filter si vi b = match kt, parse_session_st b with
    | SIG, Success (SigningKey ts' sk)
    | DH, Success (DHPrivateKey ts' sk)
    | PKE, Success (DecryptionKey ts' sk)
    | OneTimeDH, Success (OneTimeDHPrivKey ts' sk) -> ts = ts'
    | _ -> false in
  match find_session p filter with
  | Some (|si,vi,st|) ->
    (match kt, parse_session_st st with
     | SIG, Success (SigningKey ts' sk) -> (|si, sk|)
     | DH, Success (DHPrivateKey ts' sk) -> (|si, sk|)
     | PKE, Success (DecryptionKey ts' sk) -> (|si, sk|)
     | OneTimeDH, Success (OneTimeDHPrivKey ts' sk) -> (|si, sk|)
     |_ -> error "not the right kind of key")
  | None -> error ("private key named '" ^ ts ^ "' not found in " ^ p ^ "'s state")

let install_public_key p peer kt ts =
  print_string ("installing public key for "^p^" at "^peer^"\n");
  let (|osi, sk|) = get_private_key p kt ts in
  let si = new_session_number peer in
  let st = (match kt with | OneTimeDH -> OneTimeDHPubKey ts p (dh_pk sk) | _ -> public_key_st p peer si 0 kt ts sk) in
  let new_st = serialize_session_st st in
  new_session peer si 0 new_st;
  si

let get_public_key p peer kt ts =
  let filter si vi b = match kt, parse_session_st b with
    | SIG, Success (VerificationKey ts' pr _)
    | DH, Success (DHPublicKey ts' pr _)
    | PKE, Success (EncryptionKey ts' pr _)
    | OneTimeDH, Success (OneTimeDHPubKey ts' pr _) -> pr = peer && ts = ts'
    | _ -> false in
  match find_session p filter with
  | Some (|si,vi,st|) ->
    (match kt, parse_session_st st with
     | SIG, Success (VerificationKey ts' _ sk) -> sk
     | DH, Success (DHPublicKey ts' _ sk) -> sk
     | PKE, Success (EncryptionKey ts' _ sk) -> sk
     | OneTimeDH, Success (OneTimeDHPubKey ts' peer sk) -> sk
     |_ -> error "not the right kind of key")
  | None -> error ("Could not find " ^ peer ^ "'s public key (with name " ^ ts ^ ") in " ^ p ^ "'s state")
