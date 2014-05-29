Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import sort.
Require Import Recdef.

Local Open Scope list_scope.

Fixpoint vstavi (x : Z) (l : list Z) :=
  match l with
    | nil => x :: nil
    | y :: l' => if (Z.leb x y) then x :: y :: l' else y :: (vstavi x l')
  end.

Fixpoint insertsort (l : list Z) :=
  match l with 
    | nil => nil
    | x :: l' => vstavi x (insertsort l')
  end.

Eval compute in (insertsort (2 :: 5 :: 3 :: 1 :: 10 :: 7 :: nil)%Z).

Lemma urejen_dodatek (x y : Z) (l : list Z) :
  (x<=y)%Z /\ urejen (y :: l) -> urejen (x :: y :: l).
Proof.
  intro.
  induction l; firstorder.
Qed.

Lemma urejen_menjava (x y : Z) (l : list Z) :
  (x<=y)%Z /\ urejen (y :: l) -> urejen (x :: l).
Proof.
  intro.
  induction l ; firstorder.
Qed.

Lemma urejen_pod (x : Z) (l : list Z) :
  urejen (x :: l) -> urejen l.
Proof.
  induction l; firstorder.
Qed.  

Lemma urejen_prvi (x y : Z) (l : list Z) :
  urejen (x :: l) -> In y l -> (x <= y)%Z.
Proof.
  intros G H.
  induction l; firstorder.
  apply IHl.
  apply (urejen_menjava x a l).
  firstorder.
  assumption.
Qed.

Lemma vstavi_min (x : Z) (l : list Z) :
  urejen (x :: l) -> vstavi x l = x :: l.
Proof.
  induction l; auto.
  intro H.
  apply (urejen_prvi x a (a :: l)) in H.
  - simpl.
    apply Zle_is_le_bool in H.
    now rewrite H.
  - firstorder.
Qed.

Lemma vstavi_glava (x y : Z) (l : list Z) :
  (x < y)%Z -> vstavi y (x :: l) = x :: (vstavi y l).
Proof.
  intros H.
  simpl.
  apply Z.leb_gt in H.
  now rewrite H.
Qed.

Lemma vstavi_mali (x y : Z) (l : list Z) :
  (x <= y)%Z -> vstavi x (y :: l) = x :: y :: l.
Proof.
  intro.
  simpl.
  apply Zle_is_le_bool in H.
  now rewrite H.
Qed.
      
       
Lemma vstavi_mini (x : Z) (l : list Z) :
  urejen l -> (forall y, In y l -> (x <= y)%Z) -> urejen (x :: l).
Proof.
  intro H.
  intro G.
  induction l.
  - auto.
  - firstorder.
Qed.

Lemma el_vstavi (x y : Z) (l : list Z) :
  In y (vstavi x l) -> y = x \/ In y l.
Proof.
  intro.
  induction l.
  - simpl in H.
    firstorder.
  - case_eq (Z.leb x a).
    + intro G.
      apply Zle_is_le_bool in G.
      rewrite vstavi_mali in H.
      firstorder.
      assumption.
    + intro G.
      apply Z.leb_gt in G.
      rewrite vstavi_glava in H.
      firstorder.
      assumption.
Qed.

Lemma vstavi_ohranja (x : Z) (l : list Z) :
   urejen l -> urejen (vstavi x l).
Proof.
  induction l; auto.
  intro H.
  simpl.
  case_eq (Z.leb x a).
  - intro G.
    apply urejen_dodatek.
    apply Zle_bool_imp_le in G.
    firstorder.
  - intro G.
    apply vstavi_mini.
    + apply urejen_pod in H.
      firstorder.
    + intro y.
      intro F.
      apply el_vstavi in F.
      destruct F.
      rewrite H0.
      apply Z.leb_gt in G.
      firstorder.
      now apply (urejen_prvi a y l).
Qed.


Theorem sort_ureja : forall l : list Z, urejen (insertsort l).
Proof.
  intro.
  induction l.
  - now simpl.
  - simpl.
    now apply vstavi_ohranja.
Qed.

Theorem sort_nespreminja : forall l : list Z, enak l (insertsort l).
Admitted.











