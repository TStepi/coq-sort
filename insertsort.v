Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import pomozne.
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
  - unfold insertsort.
    firstorder.
  - simpl.
    now apply vstavi_ohranja.
Qed.

Lemma pojavi_vstavi (x : Z) ( l : list Z) :
  S(pojavi x l) = pojavi x (vstavi x l).
Proof.
  induction l.
  - simpl.
    now rewrite Z.eqb_refl.
  - case_eq (Z.leb x a).
    + intro.
      simpl.
      rewrite H.
      case_eq (Z.eqb x a).
      * intro G.
        apply Z.eqb_eq in G.
        rewrite <- G.
        simpl.
        now rewrite Z.eqb_refl.
      * intro G.
        simpl.
        now rewrite Z.eqb_refl; rewrite G.
    + intro.
      simpl.
      rewrite H.
      apply Z.leb_gt in H.
      apply Z.lt_neq in H.
      apply not_eq_sym in H.
      apply Z.eqb_neq in H.
      rewrite H.
      simpl.
      now rewrite H.
Qed.

Lemma vstavi_drugacnega (x y : Z) (l : list Z) :
  x <> y -> pojavi x l = pojavi x (vstavi  y l).
Proof.
  intro.
  apply Z.eqb_neq in H.
  induction l.
  -  simpl.
     now rewrite H.
  - simpl.
    case_eq (Z.eqb x a).
    + intro G.
      apply Z.eqb_eq in G.
      case_eq (Z.leb y a).
      * intro F.
        rewrite <- G.
        simpl.
        rewrite H.
        now rewrite Z.eqb_refl.
      * intro F.
        rewrite <- G.
        simpl.
        rewrite IHl.
        now rewrite Z.eqb_refl.
    + intro G.
      case_eq (Z.leb y a).
      * intro.
        simpl.
        now rewrite H; rewrite G.
      * intro F.
        simpl.
        now rewrite G.
Qed.    

Theorem sort_permutira : forall l : list Z, permutiran l (insertsort l).
Proof.
  intro.
  unfold permutiran.
  intro.
  induction l; auto.
  case_eq (Z.eqb x a).
  - intro.
    simpl.
    rewrite H.
    apply Z.eqb_eq in H.
    rewrite <- H.
    rewrite IHl.
    apply pojavi_vstavi.
  - intro.
    simpl.
    rewrite H.
    rewrite IHl.
    apply Z.eqb_neq in H.
    now apply vstavi_drugacnega.
Qed.