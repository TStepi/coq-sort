Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import pomozne.
Require Import Recdef.

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
  length (ostanek (x :: l) )= length  l.
Proof. 
  induction l.
  - simpl.
    now rewrite Z.eqb_refl.
  - simpl.
    simpl in IHl.
    case_eq (Z.leb x a);
    case_eq (Z.eqb a (najmanjsi a l));
    case_eq (Z.eqb x (najmanjsi x l));
    intros H G F; auto.
    + rewrite H in IHl.
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
    | x :: l' => (najmanjsi x l') :: (bsort (ostanek (x :: l')))
  end.
Proof.
  intros l x l' H.
  rewrite (dolzina_ostanka x l').
  firstorder.
Defined.


Eval compute in (bsort (4 :: 2 :: 3 :: 5 :: 1 :: nil)%Z).


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
  induction l; auto.
  rewrite bsort_equation.
  rewrite prvi_najmanjsi.
  rewrite o_ostanku.
   - apply urejen_pod in H.
     apply IHl in H.
     now rewrite H.
   - assumption.
   - assumption.
Qed.

Lemma ostanek_pod (x : Z) (l : list Z) :
  In x (ostanek l) -> In x l.
Proof.
  intro.
  induction l.
  - simpl in H.
    contradiction.
  - simpl in H.
    case_eq (a =? najmanjsi a l)%Z; intro G.
    + rewrite G in H.
      simpl.
      now right.
    + rewrite G in H.
      simpl in H.
      destruct H.
      * firstorder.
      * apply IHl in H.
        firstorder.
Qed.


Lemma urejen_najmanjsi (x : Z) (l : list Z) :
  urejen l -> (forall y, In y l -> (x <= y)%Z) -> urejen (x :: l).
Proof.
  intros H G.
  destruct l.
  now simpl.
  simpl.
  split.
  - apply G.
    firstorder.
  - destruct l; auto.
Qed.

Lemma en_el (x : Z) :
  bsort (x::nil) = x::nil.
Proof.
  rewrite bsort_equation.
  simpl.
  rewrite Z.eqb_refl.
  firstorder.
Qed.

Lemma pomo1 (x : Z) (l : list Z) :
  In x (bsort (ostanek l)) -> In x (bsort l).
Proof.
  intro.
  induction l.
  firstorder.
  simpl in H.
  case_eq (Z.eqb a (najmanjsi a l)).
   - intro G.
     rewrite G in H.
     rewrite bsort_equation.
     simpl.
     rewrite G.
     now right.
   - intro G.
     rewrite G in H.
     rewrite bsort_equation.
     simpl.
     rewrite G.
     now right.
Qed.

Lemma pomo2 (x : Z) (l : list Z) :
  In x (ostanek l) -> In x l.
Proof.
  intro.
  induction l; firstorder.
  simpl.
  simpl in H.
  case_eq (Z.eqb a (najmanjsi a l)).
   - intro G.
     rewrite G in H.
     now right.
   - intro G.
     rewrite G in H.
     simpl in H.
     destruct H.
      + now left.
      + apply IHl in H.
        now right.
Qed.

Lemma najmanjsi_nekaj (x y : Z) (l : list Z) :
  (y < najmanjsi x l)%Z -> y = najmanjsi y l.
Admitted.
(*Tole sva zih že mela dokazan. Kvečjemu v močnejši obliki.*) 

Lemma pomo3 (x : Z) (l : list Z) :
  length (x :: l) = S (length (ostanek (x :: l))).
Proof.
  induction l.
  simpl.
  rewrite Z.eqb_refl.
  now simpl.
  simpl.
  case_eq (Z.leb x a);
  case_eq (Z.eqb x (najmanjsi a l));
  case_eq (Z.eqb a (najmanjsi a l));
  case_eq (Z.eqb x (najmanjsi x l)); 
  intros H G F U;
  try (simpl in IHl; rewrite H in IHl; firstorder).
  simpl.
  apply Z.eqb_eq in H;
  apply Z.eqb_neq in F;
  apply Z.eqb_neq in G.
  apply Z.leb_gt in U.
  rewrite H in U.
  apply najmanjsi_nekaj in U.
  contradiction.
Qed.  

Lemma ohranjanje_el_n (x : Z) (n : nat) (l : list Z) :
  length l <= n -> In x (bsort l) -> In x l.
Proof.
  generalize l.
  induction n; intros l' G.
   - destruct l'.
     firstorder.
     simpl in G.
     firstorder.
   - destruct l'.
     firstorder.
     rewrite bsort_equation.
     simpl.
     case_eq (Z.eqb z (najmanjsi z l')).
      + intros F U.
        destruct U.
         * apply Z.eqb_eq in F; firstorder.
         * apply IHn in H.
           now right.
           simpl in G.
           omega.
      + intros F U.
        destruct U.
         * assert (In (najmanjsi z l') (z :: l')).
           apply najmanjsi_In.
           rewrite H in H0.
           simpl in H0.
           firstorder.
         * apply IHn in H.
           case_eq (Z.eqb z x).
           intro T; apply Z.eqb_eq in T; firstorder.
           intro T.
           right.
           simpl in H.
           destruct H.
           apply Z.eqb_neq in T.
           contradiction.
           now apply pomo2 in H.
           simpl in G.
           simpl.
           destruct l'.
           apply Z.eqb_neq in F.
           simpl in F.
           firstorder.
           rewrite <- pomo3.
           omega.
Qed.
     

Lemma ohranjanje_el (x : Z) (l : list Z) :
   In x (bsort l) -> In x l.
Proof.
  intro.
  now apply (ohranjanje_el_n x (length l)) in H.
Qed.


Lemma bsort_ureja_n (n : nat) (l : list Z) :
  (length l <= n)%nat -> urejen (bsort l).
Proof.
  generalize l.
  induction n; intros l' H.
  - destruct l'.
    + now simpl.
    + simpl in H.
      assert (S (length l') > 0) as G.
      apply gt_Sn_O.
      apply le_not_gt in H.
      contradiction.
  - apply le_lt_or_eq in H.
    destruct H.
    + apply lt_n_Sm_le in H.
      apply IHn in H.
      assumption.
    + destruct l'.
      * now simpl.
      * simpl in H.
        apply eq_add_S in H.
        rewrite bsort_equation.
        assert (length (ostanek (z :: l')) = n) as G.
        now rewrite dolzina_ostanka.
        apply urejen_najmanjsi.
        apply IHn.
        omega.
        intros y F.
        apply ohranjanje_el in F.
        simpl in F.
        { case_eq (z =? najmanjsi z l')%Z; intro D.
        - rewrite D in F. 
          now apply najmanjsi_tail.
        - rewrite D in F.
          simpl in F.
          destruct F.
          + rewrite H0.
            apply najmanjsi_head.
          + apply ostanek_pod in H0.
            now apply najmanjsi_tail.
        }
Qed.

Theorem bsort_ureja : forall l : list Z, urejen (bsort l).
Proof.
  intro.
  apply (bsort_ureja_n (length l)).
  omega.
Qed.

Lemma pojavi_bsort (x : Z) (l : list Z) :
  pojavi x (bsort (x :: l)) = S (pojavi x (bsort l)).
Proof.
  induction l.
  rewrite en_el.
  simpl.
  now rewrite Z.eqb_refl.
  rewrite bsort_equation.
  simpl.
  case_eq (Z.leb x a);
  case_eq (Z.eqb x a);
  case_eq (Z.eqb x (najmanjsi x l));
  case_eq (Z.eqb a (najmanjsi a l));
  case_eq (Z.eqb x (najmanjsi x (ostanek l)));
  intros;
  try firstorder;
  try (apply Z.eqb_eq in H2;
     rewrite H2 in H1;
     apply Z.eqb_eq in H0;
     apply Z.eqb_neq in H1;
     contradiction);
  admit.
  (* - apply Z.eqb_eq in H2.
     rewrite <- H2.
     rewrite bsort_equation.
     simpl.
     rewrite Z.leb_refl.
     rewrite H.
     admit.*)
Qed.
     
     

Lemma drugacen_bsort (x y : Z) (l : list Z) :
  x <> y -> pojavi x l = pojavi x (bsort  (y :: l)).
Proof.
  intro.
  induction l.
  rewrite en_el.
  apply Z.eqb_neq in H.
  simpl.
  now rewrite H.
  simpl.
  case_eq (Z.eqb y (najmanjsi x l));
  case_eq (Z.eqb x (najmanjsi x l));
  case_eq (Z.eqb y (najmanjsi y l));
  case_eq (Z.eqb x (najmanjsi y l));
  case_eq (Z.eqb x a);
  case_eq (Z.leb y x);
  intros;
  try firstorder;
  try (apply Z.eqb_eq in H1;
     rewrite <- H1;
     rewrite bsort_equation;
     simpl;
     try rewrite H0;
     try rewrite H1;
     try rewrite H2;
     try rewrite H3;
     try rewrite H4;
     try rewrite H5;
     try rewrite H6;
     apply Z.eqb_eq in H2;
     apply Z.eqb_eq in H3;
     assert (x = y);
     firstorder;
     firstorder);
  admit.
Qed.

Theorem bsort_permutira : forall l : list Z, permutiran l (bsort l).
Proof.
  unfold permutiran.
  intros.
  induction l.
  now simpl.
  simpl.
  case_eq (Z.eqb x a).
   - intro.
     apply Z.eqb_eq in H.
     rewrite <- H.
     rewrite IHl.
     now rewrite pojavi_bsort.
   - intro.
     apply Z.eqb_neq in H.
     now apply (drugacen_bsort x a l) in H.
Qed.
     















 

