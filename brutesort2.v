Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import pomozne.
Require Import Recdef.
Require Import insertsort.

Fixpoint ostanek (l : list Z) : list Z :=
  match l with
    | nil => nil
    | a :: l' => if (a =? najmanjsi a l')%Z then l' else a :: (ostanek l')
  end.

Eval compute in (ostanek (4 :: 2 :: 6 :: 3 :: 1 :: 10 :: nil)%Z).

Lemma trans (x y z : Z) :
  (x <= y)%Z -> (y < z)%Z -> (x < z)%Z.
Proof.
  intros H G.
  firstorder.
Qed.

Lemma najmanjsi_spust (x y : Z) (l : list Z) :
  x = najmanjsi x (y :: l) -> x = najmanjsi x l.
Proof.
  intro.
  assert (x <= y)%Z as G.
  rewrite H.
  apply najmanjsi_tail.
  firstorder.
  unfold najmanjsi in H.
  apply Zle_is_le_bool in G.
  now rewrite G in H.
Qed.

Lemma najmanjsi_dod (x y : Z) (l : list Z) :
  y = najmanjsi y l -> (y < x)%Z -> y = najmanjsi y (x :: l).
Proof.
  intros H G.
  simpl.
  apply Z.lt_le_incl in G.
  apply Zle_is_le_bool in G.
  now rewrite G.
Qed.

Lemma se_manjsi (x y : Z) (l : list Z) :
  x = (najmanjsi x l) -> (y < x)%Z -> y = (najmanjsi y l).
Proof.
  intros H G.
  induction l; auto.
  assert (x <= a)%Z as F.
  rewrite H.
  apply najmanjsi_tail.
  firstorder.
  apply najmanjsi_spust in H.
  apply IHl in H.
  apply najmanjsi_dod.
  assumption.
  firstorder.
Qed. 


Lemma dolzina_ostanka (x : Z) (l : list Z) :
  S( length (ostanek (x :: l) ) )= length (x :: l).
Proof.
  simpl.
  apply eq_S.
  induction l.
  - now rewrite Z.eqb_refl.
  - simpl.
    case_eq (Z.leb x a);
    case_eq (Z.eqb a (najmanjsi a l));
    case_eq (Z.eqb x (najmanjsi x l));
    intros H G F; auto.
    + rewrite H in IHl.
      SearchAbout (length).
      simpl.
      simpl in IHl.
      now rewrite IHl.
    + apply Z.eqb_eq in G.
      rewrite G in F.
      apply Z.leb_gt in F.
      apply Z.lt_neq in F.
      apply Z.neq_sym in F.
      apply Z.eqb_neq in F.
      now rewrite F.
    + apply Z.eqb_eq in G.
      rewrite <- G.
      apply Z.leb_gt in F.
      apply Z.lt_neq in F.
      apply Z.neq_sym in F.
      apply Z.eqb_neq in F.
      now rewrite F.
    + apply Z.eqb_eq in H.
      apply Z.eqb_neq in G.
      apply Z.leb_gt in F.
      assert (a = najmanjsi a l) as E.
      apply (se_manjsi x a);assumption.
      firstorder.
    + rewrite H in IHl.
      simpl in IHl.
      apply Z.leb_gt in F.
      assert (najmanjsi a l < x)%Z as E.
      apply (trans (najmanjsi a l) a x).
      apply najmanjsi_head.
      assumption.
      apply Z.lt_neq in E.
      apply Z.neq_sym in E.
      apply Z.eqb_neq in E.
      rewrite E.
      simpl.
      now apply eq_S.   
Qed.

Function bsort (l : list Z) {measure length l} :=
  match l with
    |nil => nil
    | x :: l' => (najmanjsi x l') :: bsort (ostanek (x :: l'))
  end.
Proof.
  intros l x l' H.
  rewrite <- dolzina_ostanka.
  firstorder.
Defined.

(*bsort_tcc is defined
bsort_terminate is defined
bsort_ind is defined
bsort_rec is defined
bsort_rect is defined
R_bsort_correct is defined
R_bsort_complete is defined
bsort is defined
bsort_equation is defined*)

Lemma o_nil :
  bsort nil = nil.
Proof.
  now rewrite bsort_equation.
Qed.

Lemma en_el (x : Z) :
  bsort (x::nil) = x::nil.
Proof.
  rewrite bsort_equation.
  simpl.
  rewrite Z.eqb_refl.
  now rewrite o_nil.
Qed.

(*Lemma manjsi_urejen (x : Z) (l : list Z) :
  (x <= najmanjsi x l)%Z -> bsort (x::l) = x :: bsort l.
Proof.
  intro.
  induction l.
  rewrite o_nil.
  apply en_el.
  rewrite bsort_equation.
  simpl.
  admit.
  (*case_eq (Z.leb x a);
  case_eq (Z.eqb x (najmanjsi x l)).
   - intros F G.*)
Qed.*)

Lemma prvi_najmanjsi (x : Z) (l : list Z) :
  urejen (x :: l) -> najmanjsi x l = x.
Proof.
  intro.
  induction l; auto.
  simpl.
  case_eq (Z.leb x a).
   - intro G.
     apply urejen_pod2 in H.
     now apply IHl in H.
   - intro G.
     apply Z.leb_gt in G.
     firstorder.
Qed.

Lemma o_ostanku (x : Z) (l : list Z) :
  urejen (x :: l) -> ostanek (x :: l) = l.
Proof.
  intro.
  induction l.
  unfold ostanek.
  simpl.
  assert ((x =? x)%Z = true).
  apply Z.eqb_refl.
  now rewrite H0.
  unfold ostanek.
  assert ((x =? najmanjsi x (a :: l))%Z = true).
   - rewrite (prvi_najmanjsi x (a::l)).
     apply Z.eqb_refl.
     assumption.
   - now rewrite H0.
Qed.

Lemma bsort_urejen (x : Z) (l : list Z) :
  urejen l -> bsort l = l.
Proof.
  intro.
  induction l.
  apply o_nil.
  rewrite bsort_equation.
  rewrite prvi_najmanjsi.
  rewrite o_ostanku.
   - apply urejen_pod in H.
     apply IHl in H.
     now rewrite H.
   - assumption.
   - assumption.
Qed.

Lemma ohranjanje_el (x : Z) (l : list Z) :
  In x l <-> In x (bsort l).
Admitted.

Lemma najmanjsi_head2 (x y : Z) (l : list Z) :
  (najmanjsi x (y :: l) <= y)%Z.
Proof.
  induction l.
  simpl.
  case_eq (Z.leb x y).
   - intro H.
     now apply Zle_is_le_bool in H.
   - intro H.
     apply Z.le_refl.
   - case_eq (a =? najmanjsi x (y :: a :: l))%Z.
      + intro H.
        
Qed.

Lemma najmanjsi_in (x y : Z) (l : list Z) :
  In y l -> (najmanjsi x l <= y)%Z.
Proof.
  intro.
  induction l.
  now simpl in H.
  case_eq (Z.eqb y a).
   - intro G.
     apply Z.eqb_eq in G.
     rewrite G.
     

Theorem bsort_ureja (l : list Z) :
  urejen (bsort l).
Proof.
  induction l.
  rewrite o_nil.
  now unfold urejen.
  rewrite bsort_equation.
  apply (vstavi_mini (najmanjsi a l)) in IHl.
   + admit.
   + firstorder.
     apply <- ohranjanje_el in H.
     now apply najmanjsi_in.
Qed.

Eval compute in  bsort (4 :: 2 :: 3 :: 5 :: 1 :: nil)%Z.
  
