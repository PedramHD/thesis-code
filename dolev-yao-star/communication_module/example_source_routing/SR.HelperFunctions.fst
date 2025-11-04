/// SR.HelperFunctions (implementation)
/// ===================================
module SR.HelperFunctions


let rec create_id_list_from_principal_list_lemma (p:principal) (principal_list:list principal) =
  match principal_list with
  | hd::tl -> (
    if hd = p then assert(List.Tot.mem (P p) (create_id_list_from_principal_list principal_list))
    else create_id_list_from_principal_list_lemma p tl
  )
  | _ -> ()


let rec ids_in_create_id_list_from_principal_list_lemma (principal_list:list principal) =
    match principal_list with
    | hd::tl -> ids_in_create_id_list_from_principal_list_lemma tl
    | _ -> ()


let rec get_next_principal_in_list current_principal principal_list =
   match List.Tot.length principal_list with
   | 0 -> None
   | 1 -> None
   | _ ->
     let hd::tl = principal_list in
     if (hd = current_principal) then Some (List.Tot.Base.index tl 0)
     else get_next_principal_in_list current_principal tl

