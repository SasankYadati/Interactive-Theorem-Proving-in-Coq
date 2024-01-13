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
