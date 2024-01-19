Lemma triv : forall p: Prop, p -> p.
Proof.
    intros. assumption.
Qed.

Lemma triv2 : forall p q: Prop, p -> (q -> p).
Proof.
    auto.
Qed.

Lemma explode : forall p, 0 = 1 -> p.
Proof.
    discriminate.
Qed.

Lemma explode2 : forall p, 1 = 2 -> p.
Proof.
    intros. discriminate.
Qed.

Require Import List.
Import ListNotations.

Lemma inject1 : forall (A:Type) (a b c d x:A),
    [a;b] = [c;d] -> [a;d;x] = [c;b;x].
Proof.
    intros. f_equal. 
    - injection H as H1 H2. assumption.
    - injection H as H1 H2. subst. reflexivity.
Qed.

