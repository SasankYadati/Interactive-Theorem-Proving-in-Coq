Theorem add_0_r: forall n:nat, n + 0 = n.
Proof.
    intros n. induction n as [|n' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem minus_n_n: forall n, minus n n = 0.
Proof.
    intros n. induction n as [| n' IH].
    -   simpl. reflexivity.
    -   simpl. apply IH.
Qed.

Theorem mul_0_r: forall n:nat, n * 0 = 0.
Proof.
    induction n as [| n' IH].
    - reflexivity.
    - simpl. apply IH.
Qed.

Theorem plus_n_Sm: forall n m: nat,
    S (n + m) = n + (S m).
Proof.
    induction n as [|n' IH].
    - intros m. simpl. reflexivity.
    - intros m. simpl. rewrite <- IH. reflexivity.
Qed.

Theorem add_comm: forall n m:nat,
    n + m = m + n.
Proof.
    induction n as [|n' IH].
    - intros m. simpl. rewrite -> add_0_r. reflexivity.
    - intros m. simpl. rewrite <- plus_n_Sm. rewrite <- IH. reflexivity.
Qed.

Theorem add_assoc: forall n m p: nat,
    n + (m + p) = (n + m) + p.
Proof.
    induction n as [|n' IH].
    - intros m p. reflexivity.
    - intros m p. simpl. rewrite -> IH. reflexivity.
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

Require Import Arith.

Theorem eqb_refl: forall n: nat,
    (n =? n) = true.
Proof.
    induction n as [|n' IH].
    - simpl. reflexivity.
    - simpl. apply IH.
Qed.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem even_S: forall n: nat,
    even (S n) = negb (even n).
Proof.
    induction n as [|n' IH].
    - simpl. reflexivity.
    - rewrite -> IH. simpl. symmetry. apply negb_involutive.
Qed.

Theorem mult_0_plus': forall n m: nat,
    (n + 0 + 0) * m = n * m.
Proof.
    intros n m.
    assert (H: n + 0 + 0 = n).
        { 
            rewrite add_comm. simpl. rewrite add_comm. reflexivity.
        }
    rewrite -> H.
    reflexivity.
Qed.

Theorem plus_rearrange: forall n m p q: nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
    intros n m p q.
    assert (H: n + m = m + n).
        {
            rewrite add_comm. reflexivity.
        }
    rewrite H. reflexivity.
Qed.

Theorem add_shuffle3: forall n m p: nat,
    n + (m + p) = m + (n + p).
Proof.
    intros n m p.
    assert (H: forall n m p:nat, n + (m + p) = n + m + p).
    {
        intros n1 m1 p1.
        induction n1 as [|n' IH].
        - simpl. rewrite add_comm. reflexivity.
        - simpl. rewrite -> IH. reflexivity.
    }
    rewrite H.
    rewrite (H m n p).
    rewrite (add_comm n).
    reflexivity.
Qed.

    
Theorem mul_comm: forall m n: nat,
    m * n = n * m.
Proof.
    assert (G: forall n: nat, 1 + n = S n).
    {
        simpl. reflexivity.
    }
    induction m as [|m' IH].
    - intros n. rewrite mul_0_r. reflexivity.
    - intros n. 
      rewrite <- mult_n_Sm. rewrite <- G. simpl.
      rewrite <- IH.
      rewrite -> add_comm.
      reflexivity.
Qed.
    
Theorem plus_leb_compat_l: forall n m p: nat,
    n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
    induction p as [|p' IH].
    - intros H. simpl. apply H.
    - simpl. apply IH.
Qed.

Theorem leb_refl: forall n: nat,
    (n <=? n) = true.
Proof.
    induction n.
    - reflexivity.
    - simpl. apply IHn.
Qed.

Theorem zero_neqb_S: forall n:nat,
    0 =? (S n) = false.
Proof.
    intros n. reflexivity.
Qed.

Theorem andb_false_r: forall b: bool,
    andb b false = false.
Proof.
    intros b.
    destruct b.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.