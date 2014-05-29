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

Lemma urejen_pod2 (x y : Z) (l : list Z) :
  urejen (x :: y :: l) -> urejen (x :: l).
Proof.
  intros.
  destruct H.
  apply (urejen_menjava x y).
  firstorder.
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
  urejen (x :: l) -> (x < y)%Z -> vstavi y (x :: l) = x :: (vstavi y l).
Proof.
  intros F H.
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
      
Lemma vstavi_pomo (x y : Z) (l : list Z) : 
  urejen (x :: l) -> (x <= y)%Z -> urejen ( x :: (vstavi y l)).
Proof.
  intros H G.
  induction l. 
  - firstorder.
  - case_eq (Z.leb y a).
    + intro F.
      assert (urejen (a :: l)) as E.
      now apply (urejen_pod x (a :: l)).
      rewrite vstavi_mali.
      * apply urejen_dodatek.
        split; auto.
        apply urejen_dodatek.
        split; auto.
        now apply Zle_is_le_bool in F.
      * now apply Zle_is_le_bool in F.
    + intro F.
      SearchAbout ((?x <=? ?y)%Z=false).
      apply Z.leb_gt in F.
      rewrite vstavi_glava.
      * assert (x <= a)%Z as E.
        apply (urejen_prvi x a (a :: l)). 
        assumption. 
        firstorder.
        assert (urejen (x :: l)) as D.
        apply urejen_pod in H.
        assert ((x <= a)%Z /\ urejen (a :: l)) as C.
        split; assumption.
        now apply (urejen_menjava x a l) in C.
        apply IHl in D.
        apply urejen_pod in H.
        assert (forall (t:Z), (In t (vstavi y l)) -> (a <= t)%Z).
        intros.
        (*kako ločiš primere? Tu uporabimo H z urejen prvi in F.*)
        admit.
        apply urejen_dodatek.
        split.
        assumption.
        apply urejen_pod in D.
        (*uporabi H0 na prven iz vstavi y l in nato urejen_dodatek. Prvi vedno obstaja.*)
        assert (exists (h:Z),exists (t:list Z), vstavi y l = h::t).
        admit.
        
        
        admit.
        
        admit.
        
      * apply urejen_pod in H.
        assumption.
      * assumption.
        
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
    apply Z.leb_gt in G.
    assert (a<=x)%Z.
    firstorder.
    apply (vstavi_pomo a x).
    assumption.
    assumption.
Qed.
        
  

Theorem sort_ureja : forall l : list Z, urejen (insertsort l).
Proof.
  intro.
  induction l.
  - unfold insertsort.
    firstorder.
  - simpl.
    apply (vstavi_ohranja a).
    assumption.
Qed.

Theorem sort_nespreminja : forall l : list Z, enak l (insertsort l).
Proof.
  intros.
  admit.
Qed.






