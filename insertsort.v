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

Lemma pomo (x y : Z) (l : list Z) :
  (x<=y)%Z /\ urejen (y :: l) -> urejen (x :: l).

Lemma urejenost_podseznama (x : Z) (l : list Z) :
  urejen (x :: l) -> urejen l.
Proof.
  induction l.
  - auto.
  - intro.
    simpl in H.
    simpl.

Lemma vstavi_ohranja (x : Z) (l : list Z) :
   urejen l -> urejen (vstavi x l).
Proof.
  induction l.
  - auto.
  - intro.
    case_eq (Z.leb x a).
    + intro G.
      simpl.
      rewrite G.
      simpl.
      admit.
    + intro G.
      simpl.
      rewrite G.
   
  

Theorem sort_ureja : forall l : list Z, urejen (insertsort l).
Proof.
  intro.
  induction l.
  - now simpl.
  - simpl.
Admitted.

Theorem sort_nespreminja : forall l : list Z, enak l (insertsort l).
Admitted.