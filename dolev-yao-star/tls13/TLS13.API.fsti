/// TLS13.API
/// ================
module TLS13.API

open SecrecyLabels
open RelaxLabels
open CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
open Communication.MessageStructurePredicates
open TLS13.Handshake.Messages
open TLS13.Handshake.Sessions
open TLS13.Handshake.Protocol
open TLS13.App.Messages
open TLS13.App.Sessions

let tls_app pred = (tls (tls13_app pred))

(* Transport-layer API *)
val send: 
    #i:nat -> 
    #preds:tls13_layer_preds ->
    sender:principal -> 
    receiver:principal -> 
    m:msg preds i (join (readers [P sender]) (readers [P receiver])) -> 
    LCrypto (si:nat & m':bytes & mi:nat) (tls_app preds) 
	    (requires (fun t -> i <= trace_len t /\ 
			     (is_publishable (tls13_app_global_usage preds) i m \/
					     preds.extended_higher_layer_gu.send_function_predicates.confidential_send_pred i m)
		      ))
	    (ensures (fun t0 (|si, m', mi|) t1 ->
			   (was_message_sent_at mi sender receiver m' /\ (exists key iv ad. m' = CryptoLib.aead_enc key iv m ad))))
				 
val recv: 
    #preds:tls13_layer_preds ->
    index_of_send_event:timestamp -> 
    receiver:principal -> 
    LCrypto (now:nat & sender:principal & msg:msg preds now (readers [P receiver])) (tls_app preds)
	    (requires (fun t -> True))
	    (ensures (fun t0 (|now,sender,msg|) t1 -> 
			   now == trace_len t1 /\
			   (index_of_send_event < trace_len t1) /\ 
			   (is_publishable (tls13_app_global_usage preds) now msg \/
			       (exists j. later_than now j /\ preds.extended_higher_layer_gu.send_function_predicates.confidential_send_pred j msg)) /\
			   (exists m' sender receiver. was_message_sent_at index_of_send_event sender receiver m' /\
								      (exists key iv ad. m' = CryptoLib.aead_enc key iv msg ad))))

(**
  Send the request message to the receiver and return the session index at which the symmetric key is stored. 
*)
val send_request:
    #i:timestamp ->
    #higher_level_preds:tls13_layer_preds ->
    sender:principal ->
    receiver:principal ->
    message:msg higher_level_preds i (join (readers [P sender]) (readers [P receiver])) ->
    LCrypto (sym_key_session_state_idx:nat & sym_key:bytes & message_idx:timestamp) (tls_app higher_level_preds)
    (requires (fun t0 -> let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
		      (i <= trace_len t0) /\ send_predicates.request_pred i message))
    (ensures (fun t0 (|_, sym_key, message_idx|) t1 -> (is_request_at_idx message message_idx sym_key)))

(**
   Functions for the responder to receive requests.
 *)

val receive_request:
    #i:timestamp ->
    #higher_level_preds:tls13_layer_preds ->
    index_of_send_event_of_request:timestamp ->
    receiver:principal ->
    LCrypto (now:timestamp & sender:principal & sym_key:bytes & msg:msg higher_level_preds now (readers [P receiver])) 
	    (tls_app higher_level_preds)
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,sender,sym_key,msg|) t1 ->
	     let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
	     t0 == t1 /\ now = trace_len t0 /\
	     (index_of_send_event_of_request < trace_len t0) /\ 
	     (is_request_at_idx msg index_of_send_event_of_request sym_key) /\
	     (((is_publishable (tls13_app_global_usage higher_level_preds) now msg /\
			       is_publishable (tls13_app_global_usage higher_level_preds) now sym_key) \/
               ((is_aead_key (tls13_app_global_usage higher_level_preds) now sym_key 
			     (join (readers [P sender]) (readers [P receiver])) "AEAD.Symmetric_Send_Key") /\
					    (exists j. later_than now j /\ send_predicates.request_pred j msg))) /\
	      (can_flow now (get_label (tls13_app_key_usages higher_level_preds) msg) (get_label (tls13_app_key_usages higher_level_preds) sym_key))
	     ))) 

(**
   Function for sending the response to a request.
 *)
val send_response:
    #i:timestamp ->
    #l:label ->
    #higher_level_preds:tls13_layer_preds ->
    initiator:principal -> // the principal that sent the request
    responder:principal -> // the principal calling this function
    sym_key:lbytes (tls13_app_global_usage higher_level_preds) i l ->
    send_idx_of_request:timestamp ->
    request:bytes -> 
    message:msg higher_level_preds i l ->
    LCrypto (message_idx:timestamp) (tls_app higher_level_preds)
    (requires (fun t0 -> let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
		      (i <= trace_len t0) /\
		      ((is_publishable (tls13_app_global_usage higher_level_preds) (trace_len t0) message /\
			is_publishable (tls13_app_global_usage higher_level_preds) (trace_len t0) sym_key) \/
		       (send_predicates.response_pred i message request sym_key /\ is_request_at_idx request send_idx_of_request sym_key /\
		        is_aead_key (tls13_app_global_usage higher_level_preds) (trace_len t0) sym_key l "AEAD.Symmetric_Send_Key")
	      )))
    (ensures (fun t0 message_idx t1 -> True))


(**
   Function for the initiator to receive the response.
 *)
val receive_response:
    #higher_level_preds:tls13_layer_preds ->
    sym_key_state_session_idx:nat ->
    index_of_send_event_of_response:timestamp ->
    initiator:principal ->
    LCrypto (now:timestamp & responder:principal & response:msg higher_level_preds now (readers [P initiator]) & request_send_idx:timestamp) 
	    (tls_app higher_level_preds)
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,responder,response,request_send_idx|) t1 ->
	     let send_predicates = higher_level_preds.extended_higher_layer_gu.send_function_predicates in
	     let higher_layer_key_usages = tls13_app_key_usages higher_level_preds in
	     t0 == t1 /\ now = trace_len t0 /\
	     is_msg higher_level_preds now response (readers [P responder]) /\
	     (((corrupt_id now (P initiator) \/ corrupt_id now (P responder)) /\
               can_flow now (get_label higher_layer_key_usages response) public) \/
               (exists sym_key j request. later_than now j /\ send_predicates.response_pred j response request sym_key /\ 
				     is_request_at_idx request request_send_idx sym_key))
	     ))
