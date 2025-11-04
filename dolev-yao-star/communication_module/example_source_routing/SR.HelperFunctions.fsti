/// SR.HelperFunctions (interface)
/// ===================================
module SR.HelperFunctions

open SecrecyLabels


(**
  Given a list of principals = [id_1, ..., id_n], this function creates the list
  of ids [P id_1, ..., P id_n].
*)
let rec create_id_list_from_principal_list (principal_list:list principal) : list id =
  match principal_list with
  | hd::tl -> (P hd) :: create_id_list_from_principal_list tl
  | _ -> []


(**
  Each principal p contained in a list of principals is also contained in the list of ids (as (P p))
  returned by [create_id_list_from_principal_list].
*)
val create_id_list_from_principal_list_lemma: (p:principal) -> (principal_list:list principal) ->
  Lemma (ensures (
    List.Tot.mem p principal_list ==> contains_id (create_id_list_from_principal_list principal_list) (P p)
  ))


(**
  This lemma states properties about ids contained in (create_id_list_from_principal_list
  principal_list), in particular, that the id has the form (P principal), where the principal is
  contained in the original principal list.
*)
val ids_in_create_id_list_from_principal_list_lemma: (principal_list:list principal) ->
  Lemma (ensures (
    forall id. exists principal.
      List.Tot.mem id (create_id_list_from_principal_list principal_list) ==>
      (id == (P principal) /\ List.Tot.mem principal principal_list)
  ))


(**
  Given a principal current_principal and a list of principals principal_list, this function returns
  the next principal in the list immediately following the first occurence of current_principal (if
  possible).
*)
val get_next_principal_in_list:
  current_principal:principal ->
  principal_list:list principal ->
  opt_next_principal:option principal{Some? opt_next_principal
    ==> ((List.Tot.mem current_principal principal_list) /\ (List.Tot.mem (Some?.v opt_next_principal) principal_list))}
