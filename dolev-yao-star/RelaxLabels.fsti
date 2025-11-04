/// RelaxLabels
/// ==============

module RelaxLabels

open SecrecyLabels

val unversion: label -> label

val unsession: label -> label

val can_flow_unversion_to_label: p:corrupt_pred -> i:timestamp -> l:label ->
  Lemma (can_flow_p p i (unversion l) l)

val can_flow_join_unversion: p:corrupt_pred -> i:timestamp -> l1:label -> l2:label ->
  Lemma (can_flow_p p i (unversion (join l1 l2)) (unversion l1) /\
	 can_flow_p p i (unversion (join l1 l2)) (unversion l2) /\
	 can_flow_p p i (join (unversion l1) l2) (join l1 l2))

val unversion_si_vi: pr:principal -> si:nat -> vi:nat ->
  Lemma (unversion (readers [V pr si vi]) == readers [S pr si] /\ unversion (readers [S pr si]) == readers [S pr si] /\ unversion (readers [P pr]) == readers [P pr]) 

val can_flow_unversion: p:corrupt_pred -> i:timestamp -> l1:label -> l2:label ->
  Lemma (can_flow_p p i l1 l2 ==> can_flow_p p i (unversion l1) (unversion l2))

val unversion_of_join: l1:label -> l2:label ->
  Lemma (unversion (join l1 l2) == join (unversion l1) (unversion l2))  

val can_flow_unsession_to_label: p:corrupt_pred -> l:label ->
  Lemma (forall i. can_flow_p p i (unsession l) l)

val can_flow_join_unsession: p:corrupt_pred -> i:timestamp -> l1:label -> l2:label ->
  Lemma (can_flow_p p i (unsession (join l1 l2)) (unsession l1) /\
	 can_flow_p p i (unsession (join l1 l2)) (unsession l2) /\
	 can_flow_p p i (join (unsession l1) l2) (join l1 l2))

val unsession_of_si_vi: pr:principal -> si:nat -> vi:nat ->
  Lemma (unsession (readers [V pr si vi]) == readers [P pr] /\ 
	unsession (readers [S pr si]) == readers [P pr] /\ 
	unsession (readers [P pr]) == readers [P pr]) 

val can_flow_unsession: p:corrupt_pred -> i:timestamp -> l1:label -> l2:label ->
  Lemma (can_flow_p p i l1 l2 ==> can_flow_p p i (unsession l1) (unsession l2))

val unsession_of_join: l1:label -> l2:label ->
  Lemma (unsession (join l1 l2) == join (unsession l1) (unsession l2))  

