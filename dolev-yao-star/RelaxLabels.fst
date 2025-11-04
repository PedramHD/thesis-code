/// RelaxLabels (implementation)
/// ===============================

module RelaxLabels

open SecrecyLabels
friend SecrecyLabels

let unversion_id (i:id) : id = 
  match i with
  | P p -> P p
  | S p si -> S p si
  | V p si vi -> S p si

let rec unversion_ids (i:list id) : (list id) =
  match i with 
  | [] -> []
  | hd::tl -> (unversion_id hd)::(unversion_ids tl)

let unsession_id (i:id) : id = 
  match i with
  | P p 
  | S p _ 
  | V p _ _ -> P p

let rec unsession_ids (i:list id) : (list id) =
  match i with 
  | [] -> []
  | hd::tl -> (unsession_id hd)::(unsession_ids tl)

let rec unversion l = 
  match l with 
  | ReadableBy ids -> ReadableBy (unversion_ids ids)
  | Join l1 l2 -> join (unversion l1) (unversion l2)
  | Meet l1 l2 -> meet (unversion l1) (unversion l2)
  | Public -> Public

let rec unsession l = 
  match l with 
  | ReadableBy ids -> ReadableBy (unsession_ids ids)
  | Join l1 l2 -> join (unsession l1) (unsession l2)
  | Meet l1 l2 -> meet (unsession l1) (unsession l2)
  | Public -> Public

let rec includes_unversion_ids (i:list id) : Lemma (includes_ids (unversion_ids i) i) =
  match i with 
  | [] -> ()
  | (V p si vi)::tl -> assert (covers (S p si) (V p si vi)); includes_unversion_ids tl
  | hd::tl -> includes_unversion_ids tl

let rec includes_unsession_ids (i:list id) : Lemma (includes_ids (unsession_ids i) i) =
  match i with 
  | [] -> ()
  | (V p si vi)::tl -> assert (covers (P p) (V p si vi)); includes_unsession_ids tl
  | (S p si)::tl -> assert (covers (P p) (S p si)); includes_unsession_ids tl
  | (P p)::tl -> includes_unsession_ids tl

let rec can_flow_unversion_to_label p i l = 
  match l with 
  | ReadableBy ids -> includes_unversion_ids ids
  | Join l1 l2 
  | Meet l1 l2 -> can_flow_unversion_to_label p i l1; can_flow_unversion_to_label p i l2
  | Public -> ()

let can_flow_join_unversion p i l1 l2 = 
  assert (can_flow_p p i (unversion (join l1 l2)) (unversion l1));
  assert (can_flow_p p i (unversion (join l1 l2)) (unversion l2));
  can_flow_unversion_to_label p i l1; can_flow_unversion_to_label p i l2;
  assert (can_flow_p p i (unversion l1) l1);
  assert (can_flow_p p i (unversion l2) l2);
  assert (can_flow_p p i (join (unversion l1) l2) (join l1 l2))
    
let unversion_si_vi p si vi = ()

let rec can_flow_unversion_ids p i (i1:list id) : Lemma (ensures (includes_ids (unversion_ids i1) i1)) (decreases (List.length i1)) =
  match i1 with 
  | [] -> ()
  | (V p si vi)::tl -> assert (covers (S p si) (V p si vi)); can_flow_unversion_ids p i tl
  | hd::tl -> can_flow_unversion_ids p i tl

let rec unversion_contains_ids p i i1 i2 : Lemma (contains_id i1 i2 ==> contains_id (unversion_ids i1) (unversion_id i2)) =
  match i1 with 
  | [] -> ()
  | id1::tl1 -> assert (covers id1 i2 ==> covers (unversion_id id1) (unversion_id i2)); 
	      unversion_contains_ids p i tl1 i2

let rec unversion_includes_ids p i i1 i2 : 
    Lemma (includes_ids i1 i2 ==> includes_ids (unversion_ids i1) (unversion_ids i2)) =
  match i2 with 
  | [] -> ()
  | hd::tl -> unversion_contains_ids p i i1 hd; unversion_includes_ids p i i1 tl

let rec unsession_contains_ids p i i1 i2 : 
    Lemma (contains_id i1 i2 ==> contains_id (unsession_ids i1) (unsession_id i2)) =
  match i1 with 
  | [] -> ()
  | id1::tl1 -> assert (covers id1 i2 ==> covers (unsession_id id1) (unsession_id i2)); 
	      unsession_contains_ids p i tl1 i2

let rec unsession_includes_ids p i i1 i2 : 
    Lemma (includes_ids i1 i2 ==> includes_ids (unsession_ids i1) (unsession_ids i2)) =
  match i2 with 
  | [] -> ()
  | hd::tl -> unsession_contains_ids p i i1 hd; unsession_includes_ids p i i1 tl
  
let rec can_flow_unversion p i l1 l2 = 
    can_flow_unversion_to_label p i l1; 
    can_flow_unversion_to_label p i l2; 
    can_flow_unversion_to_label p i public; 
    match l1,l2 with
      | Public, _ -> ()
      | ReadableBy ps, Public -> can_flow_transitive p i (unversion l1) l1 l2
      | ReadableBy ps1, ReadableBy ps2 -> unversion_includes_ids p i ps1 ps2	    
      | ReadableBy ps, Join l21 l22
      | ReadableBy ps, Meet l21 l22 -> can_flow_unversion p i l1 l21; can_flow_unversion p i l1 l22 
      | Join l11 l12, Public | Join l11 l12, ReadableBy _ 
      | Meet l11 l12, Public | Meet l11 l12, ReadableBy _ -> can_flow_unversion p i l11 l2; can_flow_unversion p i l12 l2
      | Join l11 l12, Meet l21 l22 | Join l11 l12, Join l21 l22 
      | Meet l11 l12, Meet l21 l22 | Meet l11 l12, Join l21 l22 -> 
	can_flow_unversion p i l1 l21; can_flow_unversion p i l1 l22; can_flow_unversion p i l11 l2; can_flow_unversion p i l12 l2

let unversion_of_join l1 l2 = ()

let rec can_flow_unsession_to_label p l = 
  match l with 
  | ReadableBy ids -> includes_unsession_ids ids
  | Join l1 l2 
  | Meet l1 l2 -> can_flow_unsession_to_label p l1; can_flow_unsession_to_label p l2
  | Public -> ()

let can_flow_join_unsession p i l1 l2 = 
  assert (can_flow_p p i (unsession (join l1 l2)) (unsession l1));
  assert (can_flow_p p i (unsession (join l1 l2)) (unsession l2));
  can_flow_unsession_to_label p l1; can_flow_unsession_to_label p l2;
  assert (can_flow_p p i (unsession l1) l1);
  assert (can_flow_p p i (unsession l2) l2);
  assert (can_flow_p p i (join (unsession l1) l2) (join l1 l2))

let unsession_of_si_vi p si vi = ()

let rec can_flow_unsession p i l1 l2 = 
    can_flow_unsession_to_label p l1; 
    can_flow_unsession_to_label p l2; 
    can_flow_unsession_to_label p public; 
    match l1,l2 with
      | Public, _ -> ()
      | ReadableBy ps, Public -> can_flow_transitive p i (unsession l1) l1 l2
      | ReadableBy ps1, ReadableBy ps2 -> unsession_includes_ids p i ps1 ps2	    
      | ReadableBy ps, Join l21 l22
      | ReadableBy ps, Meet l21 l22 -> can_flow_unsession p i l1 l21; can_flow_unsession p i l1 l22 
      | Join l11 l12, Public | Join l11 l12, ReadableBy _ 
      | Meet l11 l12, Public | Meet l11 l12, ReadableBy _ -> can_flow_unsession p i l11 l2; can_flow_unsession p i l12 l2
      | Join l11 l12, Meet l21 l22 | Join l11 l12, Join l21 l22 
      | Meet l11 l12, Meet l21 l22 | Meet l11 l12, Join l21 l22 -> 
	can_flow_unsession p i l1 l21; can_flow_unsession p i l1 l22; 
	can_flow_unsession p i l11 l2; can_flow_unsession p i l12 l2

let unsession_of_join l1 l2 = ()
