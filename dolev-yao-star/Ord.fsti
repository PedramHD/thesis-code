/// Ord
/// ===
/// Total Orderings + Lemmas on Sorted Lists

module Ord

/// The Ord Typeclass
/// -----------------
///
/// * total order defined by a "less or equal" operator ``leq_``
/// * containing proofs that ``leq_`` is a total order
///   (reflexivity ``refl``, totality ``total_``, anti-symmetry ``anti_symm``, transitivity ``trans`` )

class ord_leq (a:eqtype) =
  { leq_: a -> a -> bool
  ; refl: (x:a) -> Lemma (x `leq_` x)
  ; total_: (x:a) -> (y:a) -> Lemma (x `leq_` y \/ y `leq_` x)
  ; anti_symm: (x:a) -> (y:a) -> Lemma (x `leq_` y /\ y `leq_` x ==> x = y)
  ; trans: (x:a) -> (y:a) -> (z:a) ->  Lemma (x `leq_` y /\ y `leq_` z ==> x `leq_` z)
  }


/// comparison functions derived from ``leq_``
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
///
/// corresponding to "<", "<=", ">" and ">="

let lt (#a:eqtype){|ord_leq a|} (x y : a) : bool =
  match (leq_ x y, x = y) with
  | (true, false) -> true
  | _ -> false

let leq (#a:eqtype){|ord_leq a|} (x y : a) : bool = leq_ x y

let gt (#a:eqtype){|ord_leq a|} (x y : a) : bool =
  match (leq_ x y, x = y) with
  | (false,false) -> true
  | _ -> false

let geq (#a:eqtype){|ord_leq a|} (x y : a) : bool =
  match (leq_ x y, x = y) with
  | (false,_) -> true
  | _ -> false

/// the total order properties as separate lemmas
/// (needed for helpful SMTPats)

let reflexivity {|ord_leq 'a |} (x : 'a)
  : Lemma (x `leq` x)
    [SMTPat (x `leq` x)]
  = refl x

let totality {| ord_leq 'a |} (x y : 'a)
  : Lemma (x `leq` y \/ y `leq` x)
  [SMTPat (x `leq` y); SMTPat (y `leq` x)]
  = total_ x y

let anti_symmetry #a {| oa: ord_leq a |} (x y : a)
  : Lemma (x `leq` y /\ y `leq` x ==> x = y)
  [SMTPat (leq #a #oa x  y)] //; SMTPat (y `leq` x)]
 = anti_symm x y

let transitivity {| ord_leq 'a |} (x y z : 'a)
  : Lemma (x `leq` y /\ y `leq` z ==> x `leq` z)
  [SMTPat (x `leq` y); SMTPat (y `leq` z)]
  = trans x y z

let transitivity_forall #a {| ord_leq a |} unit
  : Lemma (forall (x y z : a). x `leq` y /\ y `leq` z ==> x `leq` z )
= ()

/// Minimum and Maximum
/// ~~~~~~~~~~~~~~~~~~~

let min {| ord_leq 'a |} (x y : 'a) =
  if x `leq` y then x else y

let max {| ord_leq 'a |} (x y : 'a) =
  if x `leq` y then y else x


/// Instances
/// ---------

/// Int
/// ~~~

instance ord_leq_int : ord_leq int =
  { leq_ = (<=)
  ; refl = (fun _ -> ())
  ; total_ = (fun _ _ -> ())
  ; anti_symm = (fun _ _ -> ())
  ; trans = (fun _ _ _ -> ())
  }

/// Nat
/// ~~~

instance ord_leq_nat : ord_leq nat =
  { leq_ = (<=)
  ; refl = (fun _ -> ())
  ; total_ = (fun _ _ -> ())
  ; anti_symm = (fun _ _ -> ())
  ; trans = (fun _ _ _ -> ())
  }

/// Char
/// ~~~~

open FStar.Char
instance ord_leq_char: ord_leq char =
  { leq_ = (fun x y -> int_of_char x <= int_of_char y)
  ; refl = (fun _ -> ())
  ; total_ = (fun _ _ -> ())
  ; anti_symm = (fun _ _ -> ())
  ; trans = (fun _ _ _ -> ())
  }


/// Pairs
/// ~~~~~

/// 2 Tuples
/// ........
// private val pair_leq (#a #b:eqtype) {| ord_leq a |} {| ord_leq b |} (x y : a * b) : bool
let pair_leq  (#a #b:eqtype) {| ord_leq a |} {| ord_leq b |}
  (x y : a * b) : bool
  = let (xa, xb) = x in
    let (ya, yb) = y in
    if xa `lt` ya then true
    else
      if xa = ya
      then xb `leq` yb
      else false

private val pair_refl (#a #b:eqtype) {| ord_leq a |} {| ord_leq b |}
  (x : (a * b))
  : Lemma (x `pair_leq` x)

private val pair_total (#a #b:eqtype) {| ord_leq a |} {| ord_leq b |}
  (x y : a * b)
  : Lemma (x `pair_leq` y \/ y `pair_leq` x)

private val pair_anti_symm (#a #b:eqtype) {| ord_leq a |} {| ord_leq b |}
  (x y : a * b)
  : Lemma (x `pair_leq` y /\ y `pair_leq` x ==> x = y)

private val pair_trans (#a #b:eqtype) {| ord_leq a |} {| ord_leq b |}
  (x y z : a * b)
  : Lemma (x `pair_leq` y /\ y `pair_leq` z ==> x `pair_leq` z)

instance ord_leq_pair (#a #b:eqtype) {| ord_leq a |} {| ord_leq b |} : ord_leq (a * b)=
  { leq_ = pair_leq
  ; refl = pair_refl
  ; total_ = pair_total
  ; anti_symm = pair_anti_symm
  ; trans = pair_trans
  }

/// 3 Tuples
/// ........
///
/// needed for comparing version ids

// private val pair3_leq (#a #b #c:eqtype)  {| ord_leq a |} {| ord_leq b |} {| ord_leq c |} (x y : a * b * c) : bool
let pair3_leq (#a #b #c:eqtype) {| ord_leq a |} {| ord_leq b |} {| ord_leq c |} (x y : a * b * c) : bool
  = let (xa, xb, xc) = x in
    let (ya, yb, yc) = y in
    (xa, (xb, xc)) `leq` (ya, (yb, yc))

private val pair3_refl (#a #b #c:eqtype)  {| ord_leq a |} {| ord_leq b |} {| ord_leq c |} (x : a * b * c)
  : Lemma (x `pair3_leq` x)

private val pair3_total (#a #b #c:eqtype)  {| ord_leq a |} {| ord_leq b |} {| ord_leq c |} (x y: a * b * c)
  : Lemma (x `pair3_leq` y \/ y `pair3_leq` x)

private val pair3_anti_symm (#a #b #c:eqtype)  {| ord_leq a |} {| ord_leq b |} {| ord_leq c |} (x y: a * b * c)
  : Lemma (x `pair3_leq` y /\ y `pair3_leq` x ==> x = y)

private val pair3_trans  (#a #b #c:eqtype)  {| ord_leq a |} {| ord_leq b |} {| ord_leq c |} (x y z: a * b * c)
  : Lemma (x `pair3_leq` y /\ y `pair3_leq` z ==> x `pair3_leq` z)


instance ord_leq_pair3 (#a #b #c:eqtype) {| ord_leq a |} {| ord_leq b |} {| ord_leq c |} : ord_leq (a * b * c)=
  { leq_ = pair3_leq
  ; refl = pair3_refl
  ; total_ = pair3_total
  ; anti_symm = pair3_anti_symm
  ; trans = pair3_trans
  }


/// Lists
/// ~~~~~

//val list_leq: (#a:eqtype) -> {| ord_leq a |} -> (xs : list a) -> ( ys : list a) -> bool
//let rec list_leq (#a :eqtype) xs ys =
let rec list_leq #a {| ord_leq a |} (xs ys : list a) : bool =
  match (xs,ys) with
  | [], _ -> true
  | (x::xs', y::ys') -> x `leq` y && (if (x = y) then list_leq xs' ys' else true)
  | _ -> false



private val list_refl (#a:eqtype) {|ord_leq a|} (xs : list a)
  : Lemma (xs `list_leq` xs)

private val list_total (#a:eqtype) {| ord_leq a |} (xs ys: list a)
  : Lemma (xs `list_leq` ys \/ ys `list_leq` xs)

private val list_antisymm (#a:eqtype) {| ord_leq a |} (xs ys : list a)
  : Lemma (xs `list_leq` ys /\ ys `list_leq` xs ==> xs = ys)

private val list_trans (#a:eqtype) {| ord_leq a |} (xs ys zs : list a)
  : Lemma (xs `list_leq` ys /\ ys `list_leq` zs ==> xs `list_leq` zs)


instance ord_leq_list {|ord_leq 'a|}: ord_leq (list 'a) =
  { leq_ = list_leq
  ; refl = list_refl
  ; total_ = list_total
  ; anti_symm = list_antisymm
  ; trans = list_trans
  }

/// Listable Class
/// ..............
/// to reuse the list instance of ord
/// (should probably go to a different module at some point)


class listable (a:eqtype) (b:Type) =
  { toList: a -> list b
  ; fromList : list b -> a
  ; conversions_inverse: (x:a) ->
      Lemma ( fromList (toList x) = x)
  }

instance listable_list (a:eqtype): listable (list a) a =
  { toList = id
  ; fromList = id
  ; conversions_inverse = (fun _ -> ())
  }

instance ord_leq_listable (#a:eqtype) (#b:eqtype) {| listable a b |} {| ord_leq b |} : ord_leq a =
  { leq_ = (fun x y -> list_leq #b (toList x) (toList y) )
  ; refl = (fun x -> list_refl #b (toList x))
  ; total_ = (fun x y -> list_total #b (toList x) (toList y))
  ; anti_symm = (fun x y -> list_antisymm #b (toList x) (toList y)
              ; conversions_inverse #a #b x
              ; conversions_inverse #a #b y
              )
  ; trans = (fun x y z -> list_trans #b (toList x) (toList y) (toList z))
  }



/// Strings
/// ~~~~~~~
/// the ord instance of Strings is derived from showing that Strings can be converted to lists of Chars
open FStar.String

instance listable_string: listable string char =
  { toList = list_of_string
  ; fromList = string_of_list
  ; conversions_inverse = string_of_list_of_string
  }

instance ord_leq_string : ord_leq string = ord_leq_listable #string #char



/// Lemmas on Sorting
/// -----------------

module LB = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties

/// define sort w.r.t. ``leq``

let leq_comp {| ord_leq 'a |} = LB.compare_of_bool (leq #'a)
let sort {| ord_leq 'a |} (l: list 'a) : list 'a =  LB.sortWith leq_comp l
let sorted {| ord_leq 'a |} (xs : list 'a) : bool = LP.sorted (LB.bool_of_compare leq_comp) xs

/// auxiliary Lemmas
/// ~~~~~~~~~~~~~~~~

let sort_one (#a:eqtype) {| oa: ord_leq a |} (x:a)
  : Lemma (sort [x] = [x])
    [SMTPat (sort #a #oa [x])]
  = ()

let is_permutation (#a:eqtype) (xs ys : list a)
  = forall x. LB.count x xs = LB.count x ys

val permutation_member_lemma (#a:eqtype) (xs ys: list a)
  : Lemma
      (requires is_permutation xs ys)
      (ensures (forall i. i `LB.mem` xs <==> i `LB.mem` ys))
      [SMTPat (is_permutation xs ys)]

val sorted_is_permutation (#a:eqtype) {|l: ord_leq a|} (xs : list a)
  : Lemma (is_permutation xs (sort xs))
    [SMTPat (sort #a #l xs)]

val sort_is_sorted (#a:eqtype) {| ord_leq a |} (xs : list a)
  : Lemma (sorted (sort xs))

/// the Key Lemma
/// ~~~~~~~~~~~~~
/// this is needed for normalizing the ``readers`` label

val same_set_same_sort (#a:eqtype) {|ord_leq a|} (l1 : list a) (l2:list a)
  : Lemma
     (requires (is_permutation l1 l2))
     (ensures (sort l1 = sort l2))
    (decreases l1)
