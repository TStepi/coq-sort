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

Lemma dolzina_nic (l : list Z) :
  length l <= 0 -> l = nil.
Proof.
  intro.
  induction l; auto.
  simpl in H.
  omega.
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

Lemma dolzina_bsort (n : nat) (l : list Z) : 
  length l <= n -> length (bsort l) = length l.
Proof.
  generalize l.
  induction n; intros l' H.
  - apply dolzina_nic in H.
    now rewrite H.
  - apply le_lt_or_eq in H.
    destruct H.
    + apply IHn.
      omega.
    + destruct l'.
      now simpl.
      rewrite H.
      rewrite bsort_equation.
      rewrite <- dolzina.
      apply eq_S.
      simpl in H.
      apply eq_add_S in H.
      rewrite <- H.
      assert (length (bsort (ostanek (z :: l'))) = length (ostanek (z :: l'))) as G.
      apply IHn.
      assert (length (ostanek (z :: l')) = n) as F.
      rewrite <- H.
      apply dolzina_ostanka.
      omega.
      rewrite G.
      now rewrite dolzina_ostanka.
Qed.     



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


Lemma ohranjanje_el (n : nat) (x : Z) (l : list Z) :
  length l <= n -> In x (bsort l) -> In x l.
Proof.
  generalize l.
  induction n; intros l' H G.
  - destruct l'.
    + now simpl in G.
    + simpl in H.
      omega.
  - apply le_lt_or_eq in H.
    destruct H.
    + apply IHn.
      now apply lt_n_Sm_le in H.
      assumption.
    + destruct l'.
      simpl in H.
      omega.
      rewrite bsort_equation in G.
      apply in_inv in G.
      destruct G as [F|F].
      * rewrite <- F.
        apply najmanjsi_In.
      * apply IHn in F.
        now apply ostanek_pod.
        rewrite dolzina_ostanka.
        simpl in H.
        omega.
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
        apply (ohranjanje_el n) in F.
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
        omega.
Qed.

Theorem bsort_ureja : forall l : list Z, urejen (bsort l).
Proof.
  intro.
  apply (bsort_ureja_n (length l)).
  omega.
Qed.

Lemma pojavi_notIn (x : Z) (l : list Z) : 
  ~In x l -> pojavi x l = pojavi x (ostanek l).
Proof.
  intro.
  induction l; auto.
  simpl in H.
  apply Decidable.not_or in H.
  destruct H as [H G].
  apply IHl in G.
  simpl.
  apply Z.neq_sym in H.
  apply Z.eqb_neq in H.
  rewrite H.
  case_eq (Z.eqb a (najmanjsi a l)); intro F; auto.
  simpl.
  now rewrite H.
Qed.

Lemma najmanjsi_ostanek (x : Z) (l : list Z) :
  (x = najmanjsi x l)%Z -> In x l -> S (pojavi x (ostanek l)) = pojavi x l.
Proof.
  intros H G.
  induction l.
  now simpl in G.
  case_eq (Z.eqb a (najmanjsi a l)); intro F.
  + simpl.
    rewrite F.
    simpl in G.
    destruct G as [E|E].
    * rewrite E.
      now rewrite Z.eqb_refl.
    * apply Z.eqb_eq in F.
      assert ((a <= x)%Z /\ (x <= a)%Z) as D.
      split.
      rewrite F.
      now apply najmanjsi_tail.
      rewrite H.
      apply najmanjsi_tail.
      firstorder.
      assert (x = a) as C.
      omega.
      apply Z.eqb_eq in C.
      now rewrite C.
  + simpl.
    rewrite F.
    case_eq (Z.eqb x a); intro E.
    * apply Z.eqb_neq in F.
      apply Z.eqb_eq in E.
      rewrite E in H.
      simpl in H.
      rewrite Z.leb_refl in H.
      firstorder.
    * simpl.
      rewrite E.
      {destruct G as [D|D].
      - apply Z.eqb_neq in E.
        firstorder.
      - apply IHl.
        apply Z.eqb_eq.
        case_eq (Z.leb x a); intro C.
        + simpl in H.
          rewrite C in H.
          now apply Z.eqb_eq.
        + apply Z.leb_gt in C.
          assert (x <= a)%Z as B.
          rewrite H.
          apply najmanjsi_tail.
          firstorder.
          firstorder.
        + assumption. }
Qed.

Lemma nenajmanjsi_ostanek (x : Z) (l : list Z) :
  (x <> najmanjsi x l)%Z -> pojavi x (ostanek l) = pojavi x l.
Proof.
  intro.
  induction l; auto.
  simpl.
  case_eq (Z.eqb a (najmanjsi a l)); case_eq (Z.eqb x a); intros F E.
  + apply Z.eqb_eq in F.
    rewrite F in H.
    apply Z.eqb_eq in E.
    simpl in H.
    rewrite Z.leb_refl in H.
    firstorder.
  + reflexivity.
  + simpl.
    rewrite F.
    apply eq_S.
    apply IHl.
    apply Z.eqb_eq in F.
    apply Z.eqb_neq in E.
    now rewrite F.
  + simpl.
    rewrite F.
    apply IHl.
    apply Z.eqb_neq.
    simpl in H.
    case_eq (Z.leb x a); intro G.
    rewrite G in H.
    now apply Z.eqb_neq.
    rewrite G in H.
    case_eq (Z.eqb x (najmanjsi x l)); intro D; auto.
    apply Z.eqb_eq in D.
    apply Z.eqb_neq in F.
    apply Z.eqb_neq in E.
    apply Z.leb_gt in G.
    assert (a = najmanjsi a l \/ In (najmanjsi a l) l) as C.
    apply najmanjsi_inv.
    destruct C as [C|C];firstorder.
    apply (najmanjsi_tail x (najmanjsi a l) l) in C.
    rewrite <- D in C.
    assert (x <= a)%Z as B.
    transitivity (najmanjsi a l);auto.
    apply najmanjsi_head.
    omega.
Qed.

Lemma pomo_In (x : Z) (l : list Z) :
  In x l -> length l > 0.
Proof.
  intro.
  destruct l.
  now simpl in H.
  simpl.
  omega.
Qed.

Lemma pomo_ostanek (x : Z) (l : list Z) :
  length l > 0 -> length (x :: ostanek l) = length l.
Proof.
  generalize x.
  induction l.
  intros.
  now simpl in H.
  intros.
  simpl.
  case_eq (Z.eqb a (najmanjsi a l)).
   + now intro.
   + intro.
     apply Z.eqb_neq in H0.
     assert (a = najmanjsi a l \/ In (najmanjsi a l) l). apply najmanjsi_inv.
     destruct H1 as [F | F].
      - contradiction.
      - assert (length l > 0).
         * now apply pomo_In in F.
         * apply eq_S.
           now apply (IHl a) in H1.
Qed.

Lemma pojavi_bosrt_n (x : Z) (n : nat) (l : list Z) :
  length l <= n -> pojavi x l = pojavi x (bsort l).
Proof.
  generalize x l.
  induction n; intros y l' H.
  - apply dolzina_nic in H.
    now rewrite H.
  - apply le_lt_or_eq in H.
    destruct H as [H|H].
    + apply lt_n_Sm_le in H.
      now apply (IHn y l') in H.
    + destruct l';auto.
      simpl in H.
      apply eq_add_S in H.
      rewrite bsort_equation.
      simpl.
      case_eq (Z.eqb y z);
      case_eq (Z.eqb z (najmanjsi z l'));
      case_eq (Z.eqb y (najmanjsi z l'));
      intros G F E.
      * apply eq_S.
        apply (IHn y l').
        omega.
      * apply Z.eqb_eq in E.
        apply Z.eqb_eq in F.
        apply Z.eqb_neq in G.
        rewrite E in G.
        firstorder.
      * apply Z.eqb_eq in E.
        apply Z.eqb_neq in F.
        apply Z.eqb_eq in G.
        rewrite E in G.
        firstorder.
      * apply Z.eqb_eq in E.
        rewrite E.
        assert (pojavi z (z :: ostanek l') = S(pojavi z l')) as D.
        simpl.
        rewrite Z.eqb_refl.
        apply eq_S.
        apply (nenajmanjsi_ostanek ).
        now apply Z.eqb_neq in F.
        rewrite  <- D.
        apply IHn.
        simpl.
        destruct l'.
        simpl in F.
        apply Z.eqb_neq in F.
        omega.
        rewrite dolzina_ostanka.
        simpl in H.
        omega.
      * apply Z.eqb_eq in G; apply Z.eqb_eq in F; apply Z.eqb_neq in E.
        firstorder.
      * apply IHn.
        omega.
      * {
        assert (S (pojavi y (z :: ostanek l')) = pojavi y l') as D.
        simpl.
        rewrite E.
        apply najmanjsi_ostanek.
         - apply Z.eqb_eq in G.
           apply Z.eqb_neq in F.
           now apply najmanjsi_manjsi in G.
         - apply Z.eqb_eq in G.
           apply Z.eqb_neq in E.
           now apply (najmanjsi_neq y z l') in E.
         - simpl in D.
           rewrite E in D.
           apply Z.eqb_eq in G.
           assert (y = najmanjsi z l') as GG. assumption.
           apply najmanjsi_inv1 in G.
           destruct G as [G|G].
           apply Z.eqb_neq in E; contradiction.
           assert (y = najmanjsi z l') as GGG. assumption.
           apply najmanjsi_manjsi in GG.
           rewrite <- D.
           apply eq_S.
           assert (length (z :: ostanek (l')) <= n).
            + rewrite <- (pomo_ostanek z l') in H.
              firstorder.
              now apply pomo_In in G.
            + apply (IHn y) in H0.
              rewrite <- H0.
              simpl.
              now rewrite E.
        }
      * {
        assert (y = najmanjsi y l' \/ In (najmanjsi y l') l') as D.
        apply najmanjsi_inv.
        SearchAbout (~ In ?y ?l).
        assert (In y l' \/ (~ In y l')) as C.
        admit.
        (*apply In_dec.*)
        destruct D as [D|D];
        destruct C as [C|C].
        - apply Z.eqb_neq in G.
          (*protislovje*)
          admit.
        - (*0 = 0*)
          admit.
        - (*težji del, je pa res*)
          admit.
        - (*0 = 0*)
          admit.
        }
Qed.
        

Lemma pojavi_bsort_n (x : Z) (n : nat) (l : list Z) :
  length l <= n -> pojavi x (bsort (x :: l)) = S (pojavi x (bsort l)).
Proof.
  generalize x l.
  induction n;
  intros y l' H.
  - apply dolzina_nic in H.
    rewrite H.
    rewrite bsort_equation.
    simpl.
    now rewrite Z.eqb_refl.
  - apply le_lt_or_eq in H.
    destruct H as [H|H].
    + apply lt_n_Sm_le in H.
      now apply (IHn y l') in H.
    + rewrite bsort_equation.
      case_eq (Z.eqb y (najmanjsi y l')); intro G.
      * simpl.
        now rewrite G.
      * simpl.
        rewrite G.
        rewrite bsort_equation.
        
        
