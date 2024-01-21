Definition nandb (b1:bool) (b2:bool) : bool :=
  if andb b1 b2 then false else true.

Check nandb.
Check nandb true false. (*bool type*)
Check nandb true false = true. (*Prop type*)

Check nat_ind.
Check nat_rec.


Theorem andb3_exchange: forall b c d,
    andb (andb b c) d = andb (andb b d) c.
Proof.
    intros [|] [|] [|]; reflexivity. (*automate using ; which is outside the scope of language but more of a command.*)
Qed.

(* Require Import Arith. *)

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
  | B0 (n)  => (bin_to_nat n) + (bin_to_nat n)
  | B1 (n)  => S ((bin_to_nat n) + (bin_to_nat n))
end.

Theorem plus_n_Sm: forall n m: nat,
    S (n + m) = n + (S m).
Proof.
    induction n as [|n' IH].
    - intros m. simpl. reflexivity.
    - intros m. simpl. rewrite <- IH. reflexivity.
Qed.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
    induction b as [ | | ].
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. rewrite -> IHb. simpl. f_equal. rewrite <- plus_n_Sm. reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
    match n with
    | 0 => Z
    | S n => incr (nat_to_bin n)
    end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
    induction n as [|].
    - simpl. reflexivity.
    - simpl. rewrite bin_to_nat_pres_incr. simpl. rewrite IHn. reflexivity.
Qed.  

Fixpoint double (n:nat) :=
    match n with
    | 0 => 0
    | S n' => S (S (double n'))
    end.

Lemma double_plus: forall n, 
    double n = n + n.
Proof.
    induction n as [|n' IH].
    - simpl. reflexivity.
    - simpl. rewrite -> IH. rewrite -> plus_n_Sm. reflexivity.
Qed.

Lemma double_incr : forall n : nat, 
    double (S n) = S (S (double n)).
Proof.
    simpl. reflexivity.
Qed.

Definition double_bin (b: bin): bin :=
    match b with
    | Z     => Z
    | B0 c  => B0 (B0 c)
    | B1 c  => B0 (B1 c)
    end.

Example double_bin_zero: double_bin Z = Z.
Proof. simpl. reflexivity. Qed.

Example double_bin_two: double_bin (nat_to_bin 2) = nat_to_bin 4.
Proof. simpl. reflexivity. Qed.

Lemma double_incr_bin: forall b: bin,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
    intros b. destruct b.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.

Fixpoint normalize (b: bin): bin :=
    match b with
    | Z     => Z
    | B0 c  => double_bin (normalize c)
    | B1 c  => incr (double_bin (normalize c))
    end.

Example normalize_zeros: normalize (B0 (B0 (B0 Z))) = Z.
Proof. reflexivity. Qed.

Example normalize_zeros2: normalize (B1 (B0 (B0 (B0 Z)))) = B1 Z.
Proof. reflexivity. Qed.

Lemma m2: forall a, 
    nat_to_bin (a + a) = 
    double_bin (nat_to_bin a).
Proof.
    induction a.
    - reflexivity.
    - simpl. rewrite -> double_incr_bin. f_equal. rewrite <- IHa. rewrite <- plus_n_Sm. simpl. reflexivity.
Qed.

Lemma m1: forall b, 
    nat_to_bin ((bin_to_nat b) + (bin_to_nat b)) = 
    double_bin (nat_to_bin (bin_to_nat b)).
Proof.
    destruct b.
    - reflexivity.
    - rewrite m2. reflexivity.
    - rewrite m2. reflexivity.
Qed.

Theorem bin_nat_bin: forall b,
    nat_to_bin (bin_to_nat b) = normalize b.
Proof.
    induction b.
    - reflexivity.
    - simpl. rewrite -> m1. rewrite -> IHb. reflexivity.
    - simpl. f_equal. rewrite -> m1. f_equal. apply IHb.
Qed.

