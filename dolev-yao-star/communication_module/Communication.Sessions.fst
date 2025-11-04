/// Communication.Sessions
/// ======================
module Communication.Sessions

let serialize_session_st st =
   match st with
   | CommunicationState request_send_idx sym_key responder ->
     concat (string_to_bytes "CommunicationState") (concat (nat_to_bytes 0 request_send_idx) (concat sym_key (string_to_bytes responder)))
   | APP app_st -> concat (string_to_bytes "SEND_APP") app_st

let parse_session_st (serialized_session_st:bytes)
  =
  let? (tn,o) = split serialized_session_st in
  match? bytes_to_string tn with
  | "SEND_APP" -> Success (APP o)
  | "CommunicationState" -> (
      match split o with
      | Error e -> Error "Send Layer [parse_session_st]: can't split into request index and (symmetric key + responder)"
      | Success (request_send_idx_bytes, sym_key_and_responder) -> (
        match split sym_key_and_responder with
        | Error e -> Error "Send Layer [parse_session_st]: cant' split into symmetric key and responder"
        | Success (sym_key, responder_bytes) -> (
        match bytes_to_nat request_send_idx_bytes, bytes_to_string responder_bytes with
        | Success request_send_idx, Success responder -> Success (CommunicationState request_send_idx sym_key responder)
        | _, _ -> Error "Send Layer [parse_session_st]: can't parse request index or responder"
      )
    )
  )
  | _ -> Error "Send Layer: parse_session_st: unknown key name"

