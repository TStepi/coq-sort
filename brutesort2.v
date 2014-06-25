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
  y = najmanjsi y l -> (y <= x)%Z -> y = najmanjsi y (x :: l).
Proof.
  intros H G.
  simpl.
  apply Zle_is_le_bool in G.
  now rewrite G.
Qed.

Lemma se_manjsi (x y : Z) (l : list Z) :
  x = (najmanjsi x l) -> (y <= x)%Z -> y = (najmanjsi y l).
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
      apply (se_manjsi x a); firstorder.
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

Lemma In_bsort_ostanek (x : Z) (l : list Z) :
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

Lemma In_ostanek (x : Z) (l : list Z) :
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
Proof.
  intro.
  assert (y = najmanjsi y l \/ In (najmanjsi y l) l).
  apply najmanjsi_inv.
  destruct H0.
   - assumption.
   - apply (najmanjsi_tail x (najmanjsi y l) l) in H0.
     assert (y < najmanjsi y l)%Z.
     firstorder.
     assert (najmanjsi y l <= y)%Z.
     apply najmanjsi_head.
     firstorder.
Qed.

Lemma ostanek_dolzina (x : Z) (l : list Z) :
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
           now apply In_ostanek in H.
           simpl in G.
           simpl.
           destruct l'.
           apply Z.eqb_neq in F.
           simpl in F.
           firstorder.
           rewrite <- ostanek_dolzina.
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

Lemma dolzina_nic (l : list Z) :
  length l <= 0 -> l = nil.
Proof.
  intro.
  induction l; auto.
  simpl in H.
  omega.
Qed.

Lemma bsort_ostanek2 (n : nat):
  forall l, length l <= S n -> length (ostanek l) <= n.
Proof.
  induction n.
   - firstorder.
     destruct l.
     firstorder.
     simpl in H.
     apply le_S_n in H.
     apply dolzina_nic in H.
     rewrite H.
     simpl.
     rewrite Z.eqb_refl.
     now simpl.
   - intros.
     destruct l.
     firstorder.
     simpl in H.
     apply le_S_n in H.
     simpl.
     case_eq (Z.eqb z (najmanjsi z l)).
      + now intro.
      + intro.
        apply IHn in H.
        simpl.
        omega.
Qed.

Lemma najmanjsi_dod1 (x y : Z) (l : list Z) :
  (x <= y)%Z -> najmanjsi x l = najmanjsi x (y :: l).
Proof.
  intro.
  simpl.
  apply Zle_is_le_bool in H.
  now rewrite H.
Qed.

Lemma pomo1 (x y : Z) (l : list Z) :
  x <> najmanjsi x (y :: l) -> najmanjsi x (y :: l) = najmanjsi y l.
Proof.
  generalize y.
  generalize x.
  induction l.
   - intros.
     simpl.
     simpl in H.
     case_eq (Z.leb x0 y0).
      + intro.
        rewrite H0 in H.
        firstorder.
      + now intro.
   - intros.
     simpl in H.
     simpl.
     case_eq (Z.leb x0 y0);
     case_eq (Z.leb x0 a);
     case_eq (Z.leb y0 a);
     intros;
     rewrite H0 in H;
     rewrite H1 in H;
     rewrite H2 in H;
     try (apply Zle_is_le_bool in H0);
     try (apply Zle_is_le_bool in H1);
     try (apply Zle_is_le_bool in H2);
     try (apply Z.leb_gt in H0);
     try (apply Z.leb_gt in H1);
     try (apply Z.leb_gt in H2);
     firstorder.
      + rewrite (najmanjsi_dod1 x0 y0 l) in H.
         * apply IHl in H.
           rewrite <- H.
           now apply najmanjsi_dod1.
         * assumption.
      + rewrite (najmanjsi_dod1 x0 a l) in H.
         * apply IHl in H.
           rewrite <- H.
           now apply najmanjsi_dod1.
         * assumption.
Qed.

Lemma pomo_n (n : nat) (x : Z) (l : list Z) :
  length l <= n -> x <> najmanjsi x l -> bsort l = najmanjsi x l :: bsort (ostanek l).
Proof.
  generalize l.
  induction n.
   - intros.
     apply dolzina_nic in H.
     rewrite H in H0.
     simpl in H0.
     firstorder.
   - intros.
     destruct l0.
     firstorder.
     simpl in H.
     apply le_S_n in H.
     assert (najmanjsi x (z :: l0) = najmanjsi z l0).
      + now apply pomo1.    
      + rewrite H1.
        now rewrite bsort_equation.
Qed. 

Lemma pojavi_bsort_n (x : Z) (n : nat) (l : list Z) :
  length l <= n -> pojavi x (bsort (x :: l)) = S (pojavi x (bsort l)).
Proof.
  generalize l.
  generalize x.
  induction n.
   - intros.
     apply dolzina_nic in H.
     rewrite H.
     rewrite en_el.
     simpl.
     now rewrite Z.eqb_refl.
   - intros.
     rewrite bsort_equation.
     simpl.
     case_eq (Z.eqb x0 (najmanjsi x0 l0)).
     now intro.
     intro.
     apply bsort_ostanek2 in H.
     apply (IHn x0 (ostanek l0)) in H.
     rewrite H.
     assert (bsort l0 = najmanjsi x0 l0 :: bsort (ostanek l0)).
      + apply Z.eqb_neq in H0.
        now apply (pomo_n (length l0) x0 l0).
      + rewrite H1.
        simpl.
        now rewrite H0.
Qed.

Lemma pojavi_bsort (x : Z) (l : list Z) :
  pojavi x (bsort (x :: l)) = S (pojavi x (bsort l)).
Proof.
  now apply (pojavi_bsort_n x (length l) l).
Qed.

Lemma pojavi_bsort2 (x y : Z) (l : list Z) :
  pojavi x (bsort (y :: x :: l)) = S (pojavi x (bsort (y :: l))).
Proof.
  admit.
Qed.
     

 
Lemma drugacen_bsort_n (n : nat) (x y : Z) (l : list Z) :
  length l <= n -> x <> y -> pojavi x (bsort l) = pojavi x (bsort  (y :: l)).
Proof.
  (*generalize l.
  generalize x.
  generalize y.
  induction n.
   - intros y' x' l' H G.
     apply dolzina_nic in H.
     rewrite H.
     rewrite en_el.
     apply Z.eqb_neq in G.
     simpl.
     now rewrite G.
   - intros y' x' l' H G.
     destruct l'.
      + rewrite en_el.
        simpl.
        apply Z.eqb_neq in G.
        now rewrite G.
      + simpl in H.
        apply le_S_n in H.
        assert (length l' <= n) as HH. assumption.
        apply (IHn y' x' l') in H.
         * rewrite bsort_equation.
           simpl.
           {
           case_eq (Z.eqb x' (najmanjsi z l'));
           case_eq (Z.eqb z (najmanjsi z l'));
           intros.
            + apply Z.eqb_eq in H0;
              apply Z.eqb_eq in H1;
              rewrite H0;
              rewrite <- H1.
              rewrite H.
              now rewrite pojavi_bsort2.
            + assert (x' <> z).
              apply Z.eqb_eq in H1;
              apply Z.eqb_neq in H0;
              firstorder.
              apply (IHn z x' (ostanek l')) in H2.
               * rewrite <- H2.
               * destruct l'.
                 firstorder.
                 rewrite dolzina_ostanka.
                 simpl in HH.
                 omega.
            + 
           }
         * assumption.*)
   admit.
Qed.
     

Lemma drugacen_bsort (x y : Z) (l : list Z) :
  x <> y -> pojavi x (bsort l) = pojavi x (bsort  (y :: l)).
Proof.
  now apply (drugacen_bsort_n (length l)).
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
     rewrite IHl.
     now apply (drugacen_bsort x a l) in H.
Qed.
     















 

