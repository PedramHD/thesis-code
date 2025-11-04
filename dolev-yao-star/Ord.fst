/// Ord (implementation)
/// ====================

module Ord

module LB = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
open FStar.List.Tot

open FStar.Tactics

let min_swap {| ord_leq 'a |} (x y : 'a)
  : Lemma (min x y = min y x)
//   [SMTPat (min x y); SMTPat (min y x)]
= ()

let min_assoc {| ord_leq 'a |} (x y z : 'a)
  : Lemma (min x (min y z) = min y (min x z))
  //[SMTPat (min x (min y z))]
= ()


(** Instances *)

(* Pairs *)

let _ =
    assert ((1,2) `pair_leq` (4,5))
  ; assert ((1,2) `pair_leq` (1,5))

let pair_refl x = ()

let pair_total x y =
  let (xa, xb) = x in
  let (ya, yb) = y in
  if xa `leq` ya
    then ()
    else
      if ya `leq` xa then () else ()

let pair_anti_symm x y = 
  let (xa, xb) = x in
  let (ya, yb) = y in
  if xa `leq` ya
    then ()
    else ()

let pair_trans (#a #b:eqtype) {| ord_leq a |} {| ord_leq b |} (x y z: a * b)
  : Lemma (x `pair_leq` y /\ y `pair_leq` z ==> x `pair_leq` z)
= let (xa, xb) = x in
  let (ya, yb) = y in
  let (za, zb) = z in
  transitivity xa ya za

let pair3_refl x = ()
let pair3_total x y = ()
let pair3_anti_symm x y = ()
let pair3_trans x y z = ()


let _ =
    assert ((1,1,5) `leq` (1,1,7))
  ; assert ((1,1,5) `leq` (1,2,7))
  ; assert ((1,1,5) `leq` (3,1,4))

(** Lists *)


let rec list_refl xs
  = match xs with
    | [] -> ()
    | x::xs -> list_refl xs
  
let rec list_total #a xs ys
  = match xs,ys with
    | [], _ -> ()
    | x::xs, y::ys ->
        if x `leq` y
          then list_total xs ys
          else ()
    | _ -> ()

let rec list_antisymm #a xs ys
= match xs, ys with
  | [], _ -> ()
  | x::xs, y::ys -> list_antisymm xs ys
  | _ -> ()

let rec list_trans #a xs ys zs
= match xs, ys, zs with
  | [], _ , _ -> ()
  | x::xs, y::ys, z::zs -> list_trans xs ys zs
  | _ -> ()


val listable_list_leq_lemma (#a #b :eqtype) {| ord_leq a |} {| ord_leq b |} {| l : listable a b |} (x y : a)
  : Lemma (let xs = l.toList x in
           let ys = l.toList y in
           xs `leq` ys <==> (ord_leq_listable #a #b).leq_ x  y
    )
let listable_list_leq_lemma x y = ()


let _ =
    assert (([0;1]<:list int) `leq` [1;2;3])
  ; assert (([]<:list int) `leq` [])
  ; assert ('a' `leq` 'b')
  ; assert_norm ("ab" `leq` "ab")
  ; assert_norm ("ab" `leq` "d" )
  ; assert_norm ("aa" `leq` "ac")



(*** Lemmas on Sorting *)


let rec pos_count_is_member_lemma (#a:eqtype) (xs : list a)
  : Lemma (forall e. LB.count e xs > 0 ==> e `LB.mem` xs)
  = match xs with
    | [] -> ()
    | y::ys -> pos_count_is_member_lemma ys

let rec member_is_pos_count_lemma (#a: eqtype) (xs : list a)
  : Lemma (forall x. x `LB.mem` xs ==> LB.count x xs > 0)
  = match xs with
    | [] -> ()
    | y::ys -> member_is_pos_count_lemma ys

let permutation_member_lemma #a xs ys
  =   member_is_pos_count_lemma xs
    ; pos_count_is_member_lemma ys
    ; member_is_pos_count_lemma ys
    ; pos_count_is_member_lemma xs


let sorted_is_permutation xs
  = LP.sortWith_permutation (LB.compare_of_bool leq) xs

let sort_is_sorted xs
= LP.sortWith_sorted (LB.compare_of_bool leq) xs

let rec min_elem {| ord_leq 'a |} (xs : list 'a{xs <> []}) : 'a =
  match xs with
  | [x] -> x
  | x::xs -> min x (min_elem xs)

let rec min_elem_is_smallest {| ord_leq 'a |} (xs : list 'a{xs <> []})
  : Lemma (LB.for_all (fun x -> min_elem xs `leq` x) xs)
  = match xs with
    | [] -> ()
    | [x] -> ()
    | y::ys ->
            assert (min_elem xs `leq` y)
          ; min_elem_is_smallest ys // forall z. z in ys ==> min_elem ys <= z
          ; assert (min_elem xs `leq` min_elem ys)
          ; LB.for_all_mem ((fun x -> min_elem ys `leq` x)) ys
          ; LB.for_all_mem (fun x -> min_elem xs `leq` x) xs

let rec min_is_member_lemma {| ord_leq 'a |} (xs : list 'a{xs <> []})
  : Lemma (min_elem xs `LB.mem` xs)
  = match xs with
    | [x] -> ()
    | x::xs -> min_is_member_lemma xs

let nonEmpty_has_non_null_count_elem (#a:eqtype) (xs : list a)
  : Lemma (xs <> [] ==> (exists x. LB.count x xs <> 0))
  = match xs with
    | [] -> ()
    | x::xs -> ()


let rec remove (#a:eqtype) (x :  a) (xs : list a) : list a =
  match xs with
  | [] -> []
  | y::ys -> if x = y then ys else y::remove x ys

let _ =
    assert(remove 3 [3;2;1] = [2;1])
  ; assert (remove 2 [3;2;1] = [3;1])
  ; assert (remove 4 [3;2;1] = [3;2;1])
  ; assert (remove 2 [1;2] = [1])
  ; assert (remove 1 [1] = [])



// not needed
let remove_head_lemma (#a:eqtype) (xs : list a{xs <> []})
  : Lemma (let hd::tl = xs in
      tl = remove hd xs
    )
  = ()

// not needed
let rec remove_decreases_length_lemma (#a:eqtype) (x: a) (xs : list a{xs <> []})
  : Lemma (LB.length (remove x xs) <= LB.length xs)
  = match xs with
    | [x] -> ()
    | y::ys ->
        if y = x then ()
        else remove_decreases_length_lemma x ys


let rec remove_member_length_lemma (#a:eqtype) (e:a) (xs : list a)
  : Lemma
      (requires e `LB.mem` xs)
      (ensures LB.length (remove e xs) = LB.length xs -1)
= match xs with
  | [] -> ()
  | x::xs ->
      if x = e then ()
      else remove_member_length_lemma e xs

//not needed
let rec remove_non_member_id_lemma (#a:eqtype) (e : a) (xs : list a)
  : Lemma (not (e `LB.mem` xs) ==> remove e xs = xs)
  = match xs with
    | [] -> ()
    | y::ys -> remove_non_member_id_lemma e ys



let rec remove_count_lemma (#a:eqtype) (x : a) (xs : list a)
  : Lemma (x `LB.mem` xs ==>
      ((LB.count x xs - 1 = LB.count x (remove x xs))
     /\ (forall y. y <> x ==> LB.count y xs = LB.count y (remove x xs))
     )
     )
 = match xs with
   | [] ->  ()
   | y::ys -> remove_count_lemma x ys

let remove_same_set_lemma (#a:eqtype) (e:a) (xs : list a)
  : Lemma ( e `LB.mem` xs ==> is_permutation xs (e::remove e xs))
= remove_count_lemma e xs

let rec remove_length_lemma (#a:eqtype) (e : a) (xs : list a{xs <> []})
  : Lemma
      (requires e `LB.mem` xs)
      (ensures LB.length xs = LB.length (e::remove e xs))
= match xs with
  | [x] -> ()
  | x::xs' ->
      if e = x then ()
      else remove_length_lemma e xs'

let rec same_count_same_length (#a:eqtype) (xs ys : list a)
  : Lemma
      (requires (is_permutation xs ys))
      (ensures (LB.length xs = LB.length ys))
  = match xs,ys with
    | [], ys -> nonEmpty_has_non_null_count_elem ys
    | x::xs , [] -> ()
    | x::xs', ys -> begin
          pos_count_is_member_lemma ys
        ; remove_same_set_lemma x ys
        ; same_count_same_length xs' (remove x ys)
        ; remove_length_lemma x ys
      end

let rec remove_min_lemma (#a:eqtype) {| ord_leq a |} (x : a) (xs : list a{x `LB.mem` xs})
  : Lemma
      (requires (remove x xs <> [] ))
      (ensures min_elem xs = min x (min_elem (remove x xs)))
  = match xs with
    | [y] -> ()
    | [y;y'] -> ()
    | y::ys ->
        if y = x then ()
        else begin
            remove_min_lemma x ys // min_elem ys = min x (min_elem (remove x ys))
          ; min_assoc y x (min_elem (remove x ys))
        end

let rec same_set_same_min (#a:eqtype) {| ord_leq a |} (l1 l2 : list a)
  : Lemma
      (requires (not (LB.isEmpty l1) /\ (not (LB.isEmpty l2)))
                /\ is_permutation l1 l2
      )
      (ensures min_elem l1 = min_elem l2 )
  = same_count_same_length l1 l2;
    assert (LB.length l1 = LB.length l2);
    match l1,l2 with
    | [x], ys -> ()
    | x::xs, ys -> begin
        let ys' = remove x ys in
          remove_count_lemma x ys // count x ys - 1 = count x ys', andere gleich
        ; pos_count_is_member_lemma ys
        ; same_set_same_min xs ys' // min_elem xs = min_elem ys'
        ; remove_min_lemma x ys
      end


let remove_min_decreases_length {| ord_leq 'a |} (xs : list 'a{xs <> []})
  : Lemma (LB.length (remove (min_elem xs) xs) < LB.length xs )
=  min_is_member_lemma xs
 ; remove_member_length_lemma (min_elem xs) xs


let rec sorted_head_lemma {| ord_leq 'a |} (xs : list 'a{xs <> []})
  : Lemma
      (requires sorted xs)
      (ensures (forall x. x `LB.mem` xs ==> LB.hd xs `leq` x))
= match xs with
  | [x] -> ()
  | x::y::xs' -> sorted_head_lemma (y::xs')


let sorted_starts_with_min {| ord_leq 'a |} (xs : list 'a{xs <> []})
  : Lemma (requires sorted xs)
      (ensures (LB.hd xs = min_elem xs))
  = match xs with
    | [x] -> ()
    | [x;y] -> ()
    | x::y::ys ->
          sorted_head_lemma xs
        ; min_is_member_lemma xs
        ; min_elem_is_smallest xs

let rec same_set_and_sorted_equal {| ord_leq 'a |} (xs ys : list 'a)
  : Lemma
      (requires
        ( sorted xs /\ sorted ys
        /\ is_permutation xs ys
        )
      )
      (ensures xs = ys)
= same_count_same_length xs ys;
  match xs with
  | [] -> ()
  | [x] -> ()
  | xs -> begin
      same_set_same_min xs ys
    ; sorted_starts_with_min xs
    ; sorted_starts_with_min ys
    ; same_set_and_sorted_equal (LB.tail xs) (LB.tail ys)
    end

let same_set_same_sort #a l1 l2 =
    same_count_same_length l1 l2
  ; match l1, l2 with
    | [], _ -> ()
    | xs,ys -> begin
          sorted_is_permutation l1
        ; sorted_is_permutation l2
        ; sort_is_sorted l1
        ; sort_is_sorted l2
        ; same_set_and_sorted_equal (sort l1) (sort l2)
      end
