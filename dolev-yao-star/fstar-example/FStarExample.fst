(**
  Simple example: Formalizing and proving a well-known equivalence of an arithmetic series.
*)
module FStarExample

open FStar.Mul


val seq: (i:nat{i>0}) -> nat


let rec seq i =
 match i with
 | 1 -> 1
 | _ -> 7 + seq (i-1)


let rec arithmetic_sum (n:nat{n>0}) =
  match n with
  | 1 -> seq n
  | _ -> seq n + arithmetic_sum (n-1)


let test_cases =
  assert(seq 1 == 1);
  assert(seq 2 == 8);
  assert(seq 3 == 15);
  assert(arithmetic_sum 3 == 24);
  assert(arithmetic_sum 5 == 75)


val arithmetic_sequence_sum_lemma (n:nat{n>0}) :
  Lemma (requires True)
        (ensures arithmetic_sum n  = (n * (seq 1 + seq n)) / 2 )


let rec helper_lemma (n:nat) :
  Lemma (requires n>1)
        (ensures 2*(seq n) - seq 1 + n*seq (n-1) - seq (n-1) == n*seq n)
  =
  match n with
  | 2 -> ()
  | _ -> helper_lemma (n-1)


let rec arithmetic_sequence_sum_lemma n
  =
  match n with
  | 1 -> ()
  | _ -> (
    arithmetic_sequence_sum_lemma (n-1);
    assert(arithmetic_sum (n-1) = ((n-1) * (seq 1 + seq (n-1))) / 2);
    helper_lemma n;
    assert(2*(seq n) - seq 1 + n*seq (n-1) - seq (n-1) == n*seq n)
  )


let example_func (x:nat{x>0}) : (res:nat{res > 100 /\ res > x}) = x + 100


let example_func_2 (x:nat{x>0}) : Tot (res:nat{res > 100 /\ res > x}) = x + 100
