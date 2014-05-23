Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import sort.
Require Import Recdef.


Local Open Scope list_scope.

Fixpoint najmanjsi (x : Z) (l : list Z) :=
  match l with
    | nil => (x,nil)
    | y :: l' => if (Z.leb x (fst (najmanjsi y l'))) then (x,l) else ((fst (najmanjsi y l')),x::(snd (najmanjsi y l')))
  end.

Eval compute in (najmanjsi 5%Z (7::20::3::nil)%Z).

Lemma dolzina_ostanka (x y : Z) (l : list Z) :
  length ( snd ( najmanjsi x l))=length ( snd ( najmanjsi y l)).
Proof.
  induction l.
  - simpl.
    auto.
  - simpl.
    case_eq (Z.leb x (fst (najmanjsi a l)));
    case_eq (Z.leb y (fst (najmanjsi a l)));
    intros H G; simpl.
    + auto.
    + admit.
    + admit.
    + auto.
Qed.

Lemma ohranjanje_dolzine (x:Z) (l: list Z) :
  length (snd (najmanjsi x l)) = length l.
Proof.
  induction l.
  - auto.
  - simpl.
    case_eq (Z.leb x (fst (najmanjsi a l))).
    + intro.
      simpl.
      auto.
    + intro.
      simpl.
      rewrite <- (enakost_ostanka x a l).
      auto.
Qed.
    

Function brutesort (l : list Z) {measure length l} :=
  match l with 
    | nil => nil
    | x::l' => let (y,l'') := najmanjsi x l' in y::(brutesort l'')
end.
Proof.
  intros.
  simpl.
  rewrite (ohranjanje_dolzine x l').
  rewrite teq0.
  simpl.
  auto.
Qed.

Eval compute in (brutesort (2::5::1::3::nil)%Z).
  
  



