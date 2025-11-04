/// SR.Debug (implementation)
/// ===========================
module SR.Debug

open SecrecyLabels
open CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI
open AttackerAPI
open Communication.Layer
open SR.Messages
open SR.Protocol
open SR.Preds
open SecurityLemmas

val benign_attacker_confidential:
  unit ->
  LCrypto unit (pki (Communication.Layer.send_preds sr_preds))
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

let benign_attacker_confidential () =
  let alice:principal = "alice" in
  let bob:principal = "bob" in
  let charlie:principal = "charlie" in
  let (principal_list:list principal) = [alice; bob; charlie] in
  let _ = generate_and_distribute_send_keys #sr_preds #(List.Tot.length principal_list) principal_list in
  match confidential_initiator_send_msg alice principal_list with
  | Error s -> ()
  | Success idx_msg_1 -> (
    match confidential_receive_and_process_message bob idx_msg_1 with
    | Error s -> ()
    | Success idx_msg_2 -> (
      match confidential_receive_and_process_message charlie idx_msg_2 with
      | Error s -> ()
      | Success idx_msg_3 -> ()
    )
  )

let benign_confidential () : LCrypto unit (pki (Communication.Layer.send_preds sr_preds))
  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
= let t0 = get() in
  let x = benign_attacker_confidential () in
  print_trace ()

val benign_attacker_confidential_authenticated:
  unit ->
  LCrypto unit (pki (Communication.Layer.send_preds sr_preds))
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

let benign_attacker_confidential_authenticated () =
  let alice:principal = "alice" in
  let bob:principal = "bob" in
  let charlie:principal = "charlie" in
  let (principal_list:list principal) = [alice; bob; charlie] in
  let _ = generate_and_distribute_send_keys #sr_preds #(List.Tot.length principal_list) principal_list in
  match authenticated_confidential_initiator_send_msg alice principal_list with
  | Error s -> ()
  | Success idx_msg_1 -> (
    match authenticated_confidential_receive_and_process_message bob idx_msg_1 with
    | Error s -> ()
    | Success idx_msg_2 -> (
      match authenticated_confidential_receive_and_process_message charlie idx_msg_2 with
      | Error s -> ()
      | Success idx_msg_3 -> ()
    )
  )

let benign_confidential_authenticated () : LCrypto unit (pki (Communication.Layer.send_preds sr_preds))
  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
= let t0 = get() in
  let x = benign_attacker_confidential_authenticated () in
  print_trace ()


val benign_attacker_authenticated:
  unit ->
  LCrypto unit (pki (Communication.Layer.send_preds sr_preds))
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

let benign_attacker_authenticated () =
  let alice:principal = "alice" in
  let bob:principal = "bob" in
  let charlie:principal = "charlie" in
  let (principal_list:list principal) = [alice; bob; charlie] in
  let _ = generate_and_distribute_send_keys #sr_preds #(List.Tot.length principal_list) principal_list in
  match authenticated_initiator_send_msg alice principal_list with
  | Error s -> ()
  | Success idx_msg_1 -> (
    match authenticated_receive_and_process_message bob idx_msg_1 with
    | Error s -> ()
    | Success idx_msg_2 -> (
      match authenticated_receive_and_process_message charlie idx_msg_2 with
      | Error s -> ()
      | Success idx_msg_3 -> ()
    )
  )

let benign_authenticated () : LCrypto unit (pki (Communication.Layer.send_preds sr_preds))
  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
= let t0 = get() in
  let x = benign_attacker_authenticated () in
  print_trace ()

let main =
  IO.print_string "======================\n";
  IO.print_string "SR\n";
  IO.print_string "======================\n";
  let t0 = Seq.empty in
  IO.print_string "Starting Benign Attacker (Confidential):\n";
  assume(valid_trace (pki (Communication.Layer.send_preds sr_preds)) t0);
  let r,t1 = (reify (benign_confidential ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN (SUCCESS for jenkins): Successful execution of Source Routing example with confidential send/receive.\n");
  IO.print_string "Finished Benign Attacker (Confidential)\n\n\n\n";

  IO.print_string "Starting Benign Attacker (Authenticated):\n";
  let r,t1 = (reify (benign_authenticated ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN (SUCCESS for jenkins): Successful execution of Source Routing example with authenticated send/receive.\n");
  IO.print_string "Finished Benign Attacker (Authenticated)\n\n\n\n";

  IO.print_string "Starting Benign Attacker (Confidential+Authenticated):\n";
  let r,t1 = (reify (benign_confidential_authenticated ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN (SUCCESS for jenkins): Successful execution of Source Routing example with confidential+authenticated send/receive.\n");
  IO.print_string "Finished Benign Attacker (Confidential+Authenticated)\n"
