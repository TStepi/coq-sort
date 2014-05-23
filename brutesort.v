Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import sort.
Require Import Recdef.


Local Open Scope list_scope.

Fixpoint najmanjsi (x : Z) (l : list Z) :=
  match l with
    | nil => (x,nil)
    | y :: l' => let (z,l'') := najmanjsi y l' in 
            if (Z.leb x z) then (x,l) else (z,x::l'')
  end.

Eval compute in (najmanjsi 5%Z (7::20::3::nil)%Z).

Lemma pomo (x a : Z) (l : list Z) :
  S (length l) = length ( snd ( najmanjsi x (a::l))).
Proof.
  induction l.
  - simpl.
    case_eq (Z.leb x a) ; tauto.
  - simpl.
    admit.
Qed.

Lemma ohranjanje_dolzine (x:Z) (l: list Z) :
  length (snd (najmanjsi x l)) = length l.
Proof.
  induction l.
  - auto.
  - simpl.
    intros.
    case_eq (Z.leb x (fst (najmanjsi a l))).
    + intro.
      .
      


apply pomo.
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
  
  



