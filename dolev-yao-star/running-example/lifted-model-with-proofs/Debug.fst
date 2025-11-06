/// Debug (implementation)
/// ===========================
module Debug

open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open LabeledRuntimeAPI
open LabeledPKI
open Protocol


val benign_attacker:
  unit ->
  LCrypto unit (pki predicates)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)


let benign_attacker () =
  let alice:principal = "alice" in
  let bob:principal = "bob" in

  // encryption key of Bob
  let t1 = global_timestamp () in
  let pkb = gen_private_key #predicates #t1 bob PKE "enc_key" in
  let t2 = global_timestamp () in
  let idx_pka_b = install_public_key #predicates #t2 bob alice PKE "enc_key" in

  // signing key of Alice
  let t3 = global_timestamp () in
  let _ = gen_private_key #predicates #t3 alice SIG "running_example_sig_key" in
  let t4 = global_timestamp () in
  let _ = install_public_key #predicates #t4 alice bob SIG "running_example_sig_key" in

  let send_index_of_first_msg = initiator_send_message alice bob in
  receiver_receive_message bob send_index_of_first_msg;
  print_trace ()


let main =
  IO.print_string "===============================\n";
  IO.print_string "        Simple Example\n";
  IO.print_string "===============================\n";
  let t0 = Seq.empty in
  IO.print_string "Starting Benign Attacker:\n";
  assume(valid_trace (pki predicates) t0);
  let r,t1 = (reify (benign_attacker ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN: Successful execution of example protocol.\n");
  IO.print_string "Finished Benign Attacker:\n"
