(** Podpora za algoritme za urejanje. *)

(** Delali bomo s seznami celih števil, pri čemer bomo uporabljali
    cela števila iz knjižnice [ZArith]. To so binarna cela števila,
    s katerimi lahko "učinkovito" računamo. *)

Require Import List.
Require Import Bool.
Require Import ZArith.

(** Aktiviramo notacijo za sezname. *)
Local Open Scope list_scope.

(** Najprej je treba definirati pojma "seznam je urejen" in
    "seznam [l1] je permutacija seznama [l2]". 
*)

(** Seznam je urejen, če je prazen, ima en element, ali je
    oblike [x :: y :: _], kjer je [x <= y] in je rep
    [y :: _] urejen. 

    Uporabili bomo vzorec [(y :: _) as l'], ki pomeni "seznam
    [l'] oblike [y :: _]". S tem hkrati dobimo prvi element
    seznama [y] in celoten seznam [l'].
*)
Fixpoint urejen (l : list Z) :=
  match l with
    | nil => True
    | _ :: nil => True
    | x :: ((y :: _) as l') => (x <= y)%Z /\ urejen l'
  end.

(** Za permutacije potrebujemo funkcijo, ki prešteje, kolikokrat
    se dano število [k] pojavi v seznamu [l]. *)
Fixpoint pojavi (x : Z) (l : list Z) :=
  match l with
    | nil => 0
    | y :: l' =>
      if Z.eqb x y then S (pojavi x l') else pojavi x l'
  end.

(** Seznama [l1] in [l2] sta enaka, če imata isto število pojavitev
    za vsak [x]. *)
Definition permutiran (l1 l2 : list Z) :=
  forall x : Z, pojavi x l1 = pojavi x l2.

(** Uvedemo notacijo za [permutiran l1 l2]. *)
Notation "l1 ~~ l2" := (permutiran l1 l2) (at level 70).

(** Relacija [permutiran] je ekvivalenčna relacija. *)
Lemma permutiran_refl (l : list Z) : l ~~ l.
Proof.
  intro ; reflexivity.
Qed.

Lemma permutiran_sym (l1 l2 : list Z) : l1 ~~ l2 -> l2 ~~ l1.
Proof.
  intros E x.
  symmetry.
  apply E.
Qed.

Lemma permutiran_tran (l1 l2 l3 : list Z) : l1 ~~ l2 -> l2 ~~ l3 -> l1 ~~ l3.
Proof.
  intros E1 E2 x.
  transitivity (pojavi x l2) ; auto.
Qed.
  
(** Zveza med [pojavi] in stikanjem seznamov. *)
Lemma pojavi_app (x : Z) (l1 l2 : list Z) : pojavi x (l1 ++ l2) = pojavi x l1 + pojavi x l2.
Proof.
  induction l1 ; simpl ; auto.
  case ((x =? a)%Z) ; omega.
Qed.

(** Potrebovali bomo tudi operacije, ki sezname razdelijo na dva
    podseznama. Na primer, v urejanju z zlivanjem seznam razdelimo
    takole: *)
Fixpoint razpolovi (l : list Z) :=
  match l with
    | nil => (nil, nil)
    | x :: nil => (nil, x :: nil)
    | x :: y :: l' =>
      let (l1, l2) := razpolovi l' in
        (x :: l1, y :: l2)
  end.

Eval compute in (razpolovi (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: nil)%Z).

(** To je pomožna oblika indukcije na seznamih. Pravi, pa tole:
    denimo, da lastnost P in da

    - nil ima lastnost P
    - seznam z enim elementom (x :: nil) ima lastnost P, za vsak x
    - če ima seznam l lastnost P, potem ima tudi x :: y :: l lastnost P,
      za vse x, y, l

    Tedaj ima vsak seznam lasnost P.

    To inačico indukcije najlažje dokažemo tako, da napišemo ustrezno
    rekurzivno funkcijo, ki je po Curry-Howardu njen dokaz.
*)
Fixpoint list_ind_2
         {A : Set}
         (P : list A -> Prop)
         (p0 : P nil)
         (p1 : forall x, P (x :: nil))
         (p2 : forall a b k, P k -> P (a :: b :: k))
         (l : list A) :=
  match l with
    | nil => p0
    | x :: nil => p1 x
    | x :: y :: l' => p2 x y l' (list_ind_2 P p0 p1 p2 l')
  end.

(** Osnovne lastnosti razpolavljanja. *)

Lemma razpolovi_length (l : list Z) :
  match razpolovi l with
    | (l1, l2) => length l = length l1 + length l2
  end.
Proof.
  apply (list_ind_2 (fun l =>
                      let (l1, l2) := razpolovi l in
                        length l = length l1 + length l2)) ;
    simpl ; auto.
  intros x y l' H.
  replace (razpolovi l') with (fst (razpolovi l'), snd (razpolovi l')) in * |- * ;
    [ idtac | symmetry ; apply surjective_pairing ].
  simpl.
  SearchAbout (?x + S ?y).
  rewrite <- plus_n_Sm.
  now repeat f_equal.
Qed.

(** Nekateri algoritmi za urejanje razdelijo seznam na podseznama
    glede na dani kriterij [p]. *)
Fixpoint razdeli (p : Z -> bool) (l : list Z) :=
  match l with
    | nil => (nil, nil)
    | x :: l' =>
      let (l1, l2) := razdeli p l' in
        if p x then (x :: l1, l2) else (l1, x :: l2)
  end.

(** Na primer, takole razdelimo dani seznam glede na to,
    ali so elementi večji od 5. *)
Eval compute in (razdeli (Z.leb 5) (10 :: 1 :: 1 :: 3 :: 8 :: 7 :: 5 :: nil)%Z).
 
Lemma razdeli_length (p : Z -> bool) (l : list Z) :
  let (l1, l2) := razdeli p l in
    length l = length l1 + length l2.
Proof.
  induction l.
  - simpl ; auto.
  - simpl.
    replace (razdeli p l) with (fst (razdeli p l), snd (razdeli p l)) in * |- * ;
      [ idtac | symmetry ; apply surjective_pairing ].
    destruct (p a) ; simpl.
    + now f_equal.
    + rewrite <- plus_n_Sm.
      now f_equal.
Qed.

(** Nekateri algoritmi izračunajo minimalni element seznama. 
    Ker minimalni element praznega seznama ne obstaja, vedno
    računamo minimalni element sestavljenega seznama [x :: l].
*)
Fixpoint najmanjsi (x : Z) (l : list Z) : Z :=
  match l with
    | nil => x
    | y :: l' =>
      match Z.leb x y with
        | true => najmanjsi x l'
        | false => najmanjsi y l'
      end
  end.

Eval compute in (najmanjsi 4 (10 :: 1 :: 1 :: 3 :: 8 :: 7 :: 5 :: nil)%Z).

(** Tako povemo, da želimo pripadajoči program v OCamlu. *)
Recursive Extraction najmanjsi.

(** Osnovne lemen o najmanjsinih elementih. *)

Lemma najmanjsi_inv (x : Z) (l : list Z) :
  x = najmanjsi x l \/ In (najmanjsi x l) l.
Proof.
  generalize x.
  induction l ; auto.
  intro y.
  simpl; destruct (Z.leb y a).
  - destruct (IHl y) ; auto.
  - destruct (IHl a) ; auto.
Qed. 

Lemma najmanjsi_In (x : Z) (l : list Z) : 
  In (najmanjsi x l) (x :: l).
Proof.
  destruct (najmanjsi_inv x l).
  - rewrite <- H ; simpl ; auto.
  - simpl ; auto.
Qed.

Lemma najmanjsi_head (x : Z) (l : list Z) :
  (najmanjsi x l <= x)%Z.
Proof.
  generalize x.
  induction l.
  - intro ; reflexivity.
  - intro y ; simpl.
    case_eq (Z.leb y a) ; intro E.
    + apply IHl.
    + transitivity a ; [apply IHl | idtac].
      apply Z.leb_gt in E.
      firstorder.
Qed.

Lemma manjsi_najmanjsi (x y : Z) (l : list Z) :
  (x < y)%Z -> ((najmanjsi x l) <= (najmanjsi y l))%Z.
Proof.
  intro.
  assert (y = najmanjsi y l \/ In (najmanjsi y l) l) as G.
  apply najmanjsi_inv.
  destruct G.
  - rewrite <- H0.
    assert (najmanjsi x l <= x)%Z as G.
    apply najmanjsi_head.
    firstorder.
  - 
    
  
  
        

Lemma najmanjsi_tail x y l : In y l -> (najmanjsi x l <= y)%Z.
Proof.
  generalize x y ; clear x y.
  induction l ; [intros ? ? H ; destruct H | idtac].
  intros x y H.
  apply in_inv in H ; destruct H as [G|G].
  - rewrite G.
    case_eq (Z.leb x y).
    + intro F.
      simpl.
      rewrite F.
      SearchAbout ((?x <= ?y)%Z -> (?y <= ?z)%Z -> (?x <= ?z)%Z ).
      apply Zle_bool_imp_le in F.
      apply (Z.le_trans (najmanjsi x l) x y); firstorder.
      apply najmanjsi_head.
    + intro F.
      simpl.
      rewrite F.
      apply najmanjsi_head.
  - apply (IHl x y) in G.
    case_eq (Z.leb x a).
    + intro F.
      simpl.
      rewrite F.
      assumption.
    + intro F.
      simpl.
      rewrite F.
      apply Z.leb_gt in F.
    
Qed.

Lemma najmanjsi_spodna_meja (x : Z) (l : list Z) :
  forall y, In y (x :: l) -> (najmanjsi x l <= y)%Z.
Proof.
  intros y [H|H].
  - rewrite H ; apply najmanjsi_head.
  - now apply najmanjsi_tail.
Qed. 
