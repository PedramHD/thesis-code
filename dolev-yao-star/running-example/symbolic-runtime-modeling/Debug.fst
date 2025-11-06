/// Debug (implementation)
/// ===========================
module Debug

open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open SimplePKI
open Protocol


val benign_attacker:
  unit ->
  Crypto unit
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)


let benign_attacker () =
  let alice:principal = "alice" in
  let bob:principal = "bob" in

  // encryption key of Bob
  let pkb = gen_private_key bob PKE "enc_key" in
  let idx_pka_b = install_public_key bob alice PKE "enc_key" in

  // signing key of Alice
  let _ = gen_private_key alice SIG "running_example_sig_key" in
  let _ = install_public_key alice bob SIG "running_example_sig_key" in

  let send_index_of_first_msg = initiator_send_message alice bob in
  receiver_receive_message bob send_index_of_first_msg;
  print_trace ()

let main =
  IO.print_string "===============================\n";
  IO.print_string "        Simple Example\n";
  IO.print_string "===============================\n";
  let t0 = Seq.empty in
  IO.print_string "Starting Benign Attacker:\n";
  let r,t1 = (reify (benign_attacker ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN: Successful execution of example protocol.\n");
  IO.print_string "Finished Benign Attacker:\n"
