/// SR.Events (implementation)
/// ==========================

module SR.Events

open SR.Messages

open SecrecyLabels
open CryptoLib
open Communication.Layer

(*! Events *)


let initiate (initiator:principal) (principal_list:list principal) (secret_nonce:bytes) : event
  = ("Initiate",[serialize_list_of_principals_raw principal_list;secret_nonce])

let received_confidential (principal_list:list principal) (secret_nonce:bytes) : event
  = ("Received_Confidential",[serialize_list_of_principals_raw principal_list;secret_nonce])

// [processed_message] is used for showing integrity properties, and therefore, only used when using
// authenticated channels.

type authenticated_channel_property = cp:send_layer_channel_property{cp == AuthN \/ cp == AuthNConf}

let processed_message_ (cp: authenticated_channel_property) (principal_list:list principal) (secret_nonce:bytes) (counter:nat) : event
  = match cp with
    | AuthN -> ("Processed_AuthN_Message",[serialize_list_of_principals_raw principal_list;secret_nonce;(CryptoLib.nat_to_bytes 0 counter)])
    | AuthNConf -> ("Processed_AuthNConf_Message",[serialize_list_of_principals_raw principal_list;secret_nonce;(CryptoLib.nat_to_bytes 0 counter)])

// macros to keep the old code running
let processed_authn_message  = processed_message_ AuthN
let processed_authnconf_message = processed_message_ AuthNConf

let finished_authenticated (principal_list:list principal) (secret_nonce:bytes) (counter:nat) : event
  = ("Finished_Authenticated",[serialize_list_of_principals_raw principal_list;secret_nonce;(CryptoLib.nat_to_bytes 0 counter)])

let finished_confidential_authenticated (principal_list:list principal) (secret_nonce:bytes) (counter:nat) : event
  = ("Finished_Confidential_Authenticated",[serialize_list_of_principals_raw principal_list;secret_nonce;(CryptoLib.nat_to_bytes 0 counter)])
