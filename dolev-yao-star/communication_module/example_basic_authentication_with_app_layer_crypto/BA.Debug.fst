/// BA.Debug (implementation)
/// ===========================
module BA.Debug

open SecrecyLabels
open CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI
open AttackerAPI
open Communication.Layer
open BA.Messages
open BA.Protocol
open BA.Preds
open SecurityLemmas

val benign_attacker_tmp:
  unit ->
  LCrypto unit (pki (Communication.Layer.send_preds ba_preds))
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

let benign_attacker_tmp () =
  let keystring = "SEND_LAYER_CONF_REQUEST_ONLY_PKE" in
  let alice:principal = "alice" in
  let bob:principal = "bob" in
  let t0 = global_timestamp () in
  let pka_conf = gen_private_key #(ba_preds) #t0 alice PKE keystring in
  let t1 = global_timestamp () in
  let pkb_conf = gen_private_key #(ba_preds) #t1 bob PKE keystring in
  let t2 = global_timestamp () in
  assert (later_than t1 t0);
  assert (later_than t2 t1);
  let t3 = global_timestamp () in
  let idx_pka_b = install_public_key #(ba_preds) #t3 bob alice PKE keystring in

  let (|t4, ba_pwd|) = rand_gen #(ba_preds) (readers [(P alice); (P bob)]) (nonce_usage "BA.Password") in
  print_string("\nCreating Account\n");
  match initiator_send_account_registration_request #t4 alice bob ba_pwd with
  | Error s -> ()
  | Success (|sym_key_session_state_idx, client_app_data_idx, request_send_idx|) -> (
    match responder_receive_account_registration_request_and_respond bob request_send_idx with
    | Error s -> ()
    | Success (|response_send_idx, responder_state_idx|) -> (
      match initiator_process_account_registration_response alice sym_key_session_state_idx response_send_idx with
      | Error s -> ()
      | Success msg_status -> (
        print_string ("Status of first response: " ^ msg_status ^ "\n");
        match initiator_send_get_secret_request #t4 alice client_app_data_idx with
        | Error s -> ()
        | Success (|req_2_sym_key_session_state_idx, req_2_request_send_idx|) -> (
          match responder_receive_get_secret_request_and_respond bob req_2_request_send_idx with
          | Error s -> ()
          | Success resp_2_response_send_idx -> (
            match initiator_process_response_with_secret alice req_2_sym_key_session_state_idx resp_2_response_send_idx with
            | Error s -> ()
            | Success msg_status -> (
            ()
            )
          )
        )
      )
    )
  )


let benign_attacker () : LCrypto unit (pki (Communication.Layer.send_preds ba_preds))
  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
= let t0 = get() in
  let x = benign_attacker_tmp () in
  print_trace ()


let main =
  IO.print_string "============================\n";
  IO.print_string "Basic Authentication Example\n";
  IO.print_string "============================\n";
  let t0 = Seq.empty in
  IO.print_string "Starting Benign Attacker:\n";
  assume(valid_trace (pki (Communication.Layer.send_preds ba_preds)) t0);
  let r,t1 = (reify (benign_attacker ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN (SUCCESS for jenkins): Successful execution of Basic Authentication example.\n");
  IO.print_string "Finished Benign Attacker\n\n\n\n"
