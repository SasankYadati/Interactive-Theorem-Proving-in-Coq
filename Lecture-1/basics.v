Definition nandb (b1:bool) (b2:bool) : bool :=
  if andb b1 b2 then false else true.
Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  if andb b1 b2 then b3 else false.
Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Fixpoint factorial (n:nat) : nat :=
match n with
    | 0 => 1
    | S m => n * factorial m
end. 
Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Require Import Arith.
Require Import Nat.

Definition ltb (n m : nat) : bool :=
if (leb n m) then negb (eqb n m) else false.

Example test_ltb1: (ltb 2 2) = false.
Proof. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros h1.
  intros h2.
  rewrite -> h1.
  rewrite -> h2.
  reflexivity.
Qed.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
    intros b c.
    destruct b eqn:Eb.
    - destruct c eqn:Ec.
        + reflexivity.
        + intros h. rewrite <- h. reflexivity.
    - destruct c eqn:Ec.
        + reflexivity.
        + intros h. rewrite <- h. reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->  forall (b : bool), f (f b) = b.
Proof.
  intros f h b.
  rewrite -> h.
  rewrite -> h.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice:
    forall (f: bool -> bool),
    (forall (x: bool), f x = negb x) -> forall (b: bool), f (f b) = b.
Proof.
    intros f h b.
    destruct b.
    - rewrite -> h. rewrite -> h. simpl. reflexivity.
    - rewrite -> h. rewrite -> h. simpl. reflexivity.
Qed.

Theorem andb_eq_orb: forall (b c: bool),
  (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct b.
  - simpl. intros H. rewrite <- H. reflexivity.
  - simpl. intros H. rewrite <- H. reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m: bin) : bin :=
  match m with
  | Z       => B1 Z
  | B0 (n)  => B1 (n)
  | B1 (n)  => B0 (incr n)
end.

Fixpoint bin_to_nat (m: bin) : nat :=
  match m with
  | Z       => 0
  | B0 (n)  => 2 * (bin_to_nat n)
  | B1 (n)  => 1 + 2 * (bin_to_nat n)
end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.