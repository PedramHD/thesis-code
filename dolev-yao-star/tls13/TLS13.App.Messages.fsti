/// TLS13.App.Messages
/// ===================
module TLS13.App.Messages

open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib
open RelaxLabels
open TLS13.Handshake.Messages
 
module A = LabeledCryptoAPI

(* Events *)
let request (c:principal) (si:nat) (s:principal) (m:bytes): event = ("Request", [(string_to_bytes c);(nat_to_bytes 8 si);(string_to_bytes s);m])
let response (s:principal) (si:nat) (c:principal) (m:bytes): event = ("Response", [(string_to_bytes s);(nat_to_bytes 8 si);(string_to_bytes c);m])

(* SEND LAYER PREDICATES FOR HIGHER LAYERS *)
open Communication.Preds 
open Communication.UsagePredicates

type tls13_layer_preds_ = Communication.Preds.send_layer_preds

// let default_higher_layer_gu : A.global_usage = {
//     usage_preds = tls13_usage_preds;
//     key_usages = tls13_key_usages;
// }

// let def_pred_for_send_functions = { 
//   confidential_send_pred = (fun tid m -> True);
//   confidential_send_pred_later = (fun m -> ());
//   authenticated_send_pred = (fun tid m -> True);
//   authenticated_confidential_send_pred = (fun tid m -> True);
//   request_pred = (fun tid m -> True);
//   response_pred = (fun tid m r rs -> True)
// }

// let default_ext_gu : extended_global_usage = { 
//   higher_layer_gu=default_higher_layer_gu;
//   send_function_predicates=def_pred_for_send_functions;
// }

// let default_send_layer_preds : tls13_layer_preds = {
//   extended_higher_layer_gu = default_ext_gu;
//   epred = (fun i e s -> True);
//   session_st_inv = (fun i p s v st -> True); 
//   session_st_inv_later = (fun i j p s v st -> ()); 
// }

// let tls13_ku (preds) = tls13_key_usages

let pred_key_usage (pred:tls13_layer_preds_) : A.key_usages = pred.extended_higher_layer_gu.higher_layer_gu.key_usages

let tls13_layer_preds = pred:tls13_layer_preds_{key_usage_preds (pred_key_usage pred)}

let tls13_app_key_usages (pred:tls13_layer_preds) : (k:A.key_usages{key_usage_preds k}) = 
    // A.default_key_usages (* key_usages_are_unique_ k needs to be true in the higher layers *)
    pred.extended_higher_layer_gu.higher_layer_gu.key_usages

let ppred (pred:tls13_layer_preds) (i:nat) (s:string) (pk:bytes) (m:bytes) : Type0 = False
let apred (pred:tls13_layer_preds) (i:nat) (s:string) (k:bytes) (m:bytes) (ad:bytes) : Type0 = 
  (match s with 
  | "TLS13.aead_key_conf" -> A.can_flow i (A.get_label (tls13_app_key_usages pred) m) public \/
  			    pred.extended_higher_layer_gu.send_function_predicates.confidential_send_pred i m
  | "TLS13.aead_key_req_resp" -> 
    A.can_flow i (A.get_label (tls13_app_key_usages pred) m) public \/
    (match split m with
    | Error e -> False
    | Success (sym_key, msg) -> (
      (exists (sender receiver:string). was_rand_generated_before i sym_key (join (readers [P sender]) (readers [P receiver])) (aead_usage "AEAD.Symmetric_Send_Key") /\
	 (A.can_flow i (A.get_label (tls13_app_key_usages pred) k) public \/ 
		     A.can_flow i (A.get_label (tls13_app_key_usages pred) k) (join (readers [P sender]) (readers [P receiver])))) /\
      (exists (j:timestamp). j <= i /\ pred.extended_higher_layer_gu.send_function_predicates.request_pred j msg) /\
      A.can_flow i (A.get_label (tls13_app_key_usages pred) msg) (A.get_label (tls13_app_key_usages pred) sym_key)
    ))
  | "AEAD.Symmetric_Send_Key" -> 
    A.can_flow i (A.get_label (tls13_app_key_usages pred) k) public \/
    (match split m with
      | Error e -> False
      | Success (msg_tag_bytes, message) -> (
        match bytes_to_string msg_tag_bytes with
        | Error _ -> False
        | Success msg_tag -> (
    	  let request_pred = pred.extended_higher_layer_gu.send_function_predicates.request_pred in
    	  let response_pred = pred.extended_higher_layer_gu.send_function_predicates.response_pred in
          match msg_tag with
          | "Communication.Layer.Request" -> (exists j. j <= i /\ request_pred j message)
          | "Communication.Layer.Response" -> (
            match split message with
            | Error _ -> False
            | Success (request_send_idx_bytes, response) -> (
              match bytes_to_nat request_send_idx_bytes with
              | Error _ -> False
              | Success request_send_idx -> exists sym_key j request. j <= i /\ response_pred j response request sym_key /\ 
    					   Communication.MessageStructurePredicates.is_request_at_idx request request_send_idx sym_key
              )
            )
          | _ -> False
        )
      )
    )
  | _ -> True)
  
let spred (pred:tls13_layer_preds) (i:nat) (s:string) (k:bytes) (m:bytes) : Type0 = False
let mpred (pred:tls13_layer_preds) (i:nat) (s:string) (k:bytes) (m:bytes) : Type0 = False

let tls13_app_usage_preds (pred:tls13_layer_preds) : (u:A.usage_preds{usage_pred_cond_ u}) = {
  A.can_pke_encrypt = ppred pred;
  A.can_aead_encrypt =  apred pred;
  A.can_sign = spred pred;
  A.can_mac = mpred pred
} 

let tls13_app_global_usage (pred:tls13_layer_preds) : A.global_usage = {
  A.key_usages = tls13_app_key_usages pred;
  A.usage_preds = tls13_app_usage_preds pred;
}

let msg pred i l = A.msg (tls13_app_global_usage pred) i l

let is_msg pred i b l = A.is_msg (tls13_app_global_usage pred) i b l


