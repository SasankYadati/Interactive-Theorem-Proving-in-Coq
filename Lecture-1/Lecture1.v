Require Import List.
Import ListNotations.

Lemma my_tautology : forall (p: Prop), ~~(p \/ ~p).
Proof.
    intros p H.
    apply H.
    right.
    intros Hp.
    apply H.
    left.
    apply Hp.
Qed.

(* 
Find f such that 
foldl f id l [] = reverse l
f g x = fun l => x :: g l

*)

Fixpoint reverse {A: Type}(l: list A) : list A :=
  match l with 
    | [] => []
    | x :: xs => reverse xs ++ [x]
  end.

Check reverse.

Fixpoint revInto {A: Type}(l acc: list A) : list A := 
    match l with
    | [] => acc
    | x :: xs => revInto xs (x::acc)
    end.

Definition fast_rev {A:Type} (l: list A): list A :=
    revInto l [].

Lemma revInto_correct: forall (A: Type)(l acc: list A),
    revInto l acc = reverse l ++ acc.
Proof.
    induction l as [ | h t IH].
    -   intros l'. reflexivity.
    -   intros l'. simpl. rewrite <- app_assoc. simpl. apply IH.
Qed.

Lemma fastrev_correct: forall (A: Type) (l: list A),
    reverse l = fast_rev l.
Proof.
    intros A l.
    unfold fast_rev. symmetry.
    rewrite <- app_nil_r.
    apply revInto_correct.
Qed.

Fixpoint foldl {A B: Type} (f : B -> A -> B) (val : B) 
    (l : list A) : B := 
    match l with 
    | []    => val 
    | x::xs => foldl f (f val x) xs 
    end.

Definition f {A: Type} (g : list A -> list A) (x: A) (l : list A) : list A := x::g l. 
Definition id {A: Type} := fun (x:A) => x.

Lemma funny_fold_gen_exercise : forall (A: Type) (l l' : list A) (h : list A -> list A), 
    foldl f h l l' = revInto l (h l').
Proof.
    intros A l l'. induction l as [|x xs IH].
    - reflexivity.
    - intros g. simpl. apply IH.
Qed.

Lemma funny_fold_exercise : forall (A: Type) (l : list A), 
    foldl f id l [] = reverse l. 
Proof. Admitted. 

Lemma and_distribute: forall (p q r: Prop),
  (p \/ q) /\ r <-> (p /\ r) \/ (q /\ r).
Proof.
  intros p q r.
  split.
  - intros H. 
    destruct H as [[I | I] J].
    + left.
      split. 
        * apply I.
        * apply J.
    + right.
      split.
        * apply I.
        * apply J.
  - intros H.
    destruct H as [[I J] | [I J]].
    + split. left. apply I. apply J.
    + split. right. apply I. apply J.
Qed.

