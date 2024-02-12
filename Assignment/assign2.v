From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List. Import ListNotations. 
From Coq Require Import Lia.

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).

Lemma or_commut : forall P Q, P \/ Q -> Q \/ P.
Proof. intros P Q [ | ]; constructor; assumption. Qed. 

Theorem main_theorem: 
    (excluded_middle -> peirce) /\ 
    (peirce -> double_negation_elimination) /\ 
    (double_negation_elimination -> de_morgan_not_and_not) /\ 
    (de_morgan_not_and_not -> implies_to_or) /\ 
    (implies_to_or -> excluded_middle).
Proof.
    unfold excluded_middle, peirce, double_negation_elimination, 
        de_morgan_not_and_not, implies_to_or. 
        repeat split.
        -   intros. destruct H with (P:=P). 
            +   apply H1.
            +   apply H0. intros. exfalso. apply H1 in H2. apply H2.
        -   intros H P. unfold "~".
            specialize H with (P:=P) (Q:=False) as H1.
            intros. apply H1.
            intros. apply H0 in H2. exfalso. apply H2.
        -   unfold not. intros DNE P Q H.
            specialize DNE with (P:=P\/Q) as H2.
            apply H2. intros. apply H. split. 
            +   intros. apply H0. left. assumption.
            +   intros. apply H0. right. assumption.
        -   unfold not. intros. 
            specialize H with (P:=P->False) (Q:=Q) as H1.
            apply H1. intros. destruct H2. apply H2. intros. apply H0 in H4. apply H3 in H4. assumption.
        -   unfold not. intros. apply or_commut. apply H with (P:=P) (Q:=P). tauto.
Qed.
            

Inductive pal {X:Type} : list X -> Prop :=
    | pal_nil : pal [] 
    | pal_sing: forall (x: X), pal [x] 
    | pal_more: forall (x: X) (l: list X), pal l -> pal (x::l++[x]).

Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
    intros. induction H.
    -   reflexivity.
    -   reflexivity.
    -   simpl. rewrite rev_app_distr. rewrite <- IHpal. simpl. reflexivity.
Qed.
 
Lemma list_cases: forall (X:Type) (l:list X), l = [] \/ 
    (exists x, l = [x]) \/ (exists x y t, l = x::t ++ [y]).
Proof. 
    intros X. induction l.
    -   left. reflexivity.
    -   simpl. destruct IHl.
        +   right. left. exists a. rewrite H. reflexivity.
        +   destruct H.
            *   right. right. destruct H as [b H]. exists a. exists b. exists []. simpl. rewrite H. reflexivity.
            *   destruct H as [x [y [t H]]]. right. right. exists a. exists y. exists (x::t). simpl. rewrite H. reflexivity.
Qed.

Lemma last_injective : forall (X: Type) (l l' : list X) (x: X),
    l ++ [x] = l' ++ [x] -> l = l'.
Proof. 
    induction l.
    -   intros.  simpl in H. symmetry in H. apply app_eq_unit in H. 
        destruct H as [[H1 H2] | [H1 H2]].
        +   auto.
        +   rewrite H1. auto.
    -   induction l'.
        +   intros. simpl in H. injection H as H1 H2. apply app_eq_nil in H2. destruct H2. rewrite H, H1, H0. reflexivity.
        +   intros. simpl in H. injection H as H1 H2. rewrite H1. rewrite H1 in IHl'. clear a H1. apply IHl in H2. rewrite H2. reflexivity.
Qed.

Lemma length_app: forall {X: Type} (x: X) (n: nat) (l: list X), length (l ++ [x]) < n -> length l < n.
Proof. 
    Search last_length. intros. rewrite last_length in H. 
    Search lt. apply Nat.lt_succ_l. assumption.
Qed.

Theorem rev_pal: forall {X: Type} (l: list X),
    l = rev l -> pal l.
Proof.
    intros X. 
    cut (forall n (l:list X), length l < n -> l = rev l -> pal l).
    -   intros G l H. apply G with (n := S (length l)).
        lia. assumption. 
    -   induction n as [ | n IH]; intros l Hlen Hrev; try lia.
        destruct (list_cases _ l) as [H | [[x H] | [x [y [t H]]]]].
        +   rewrite H. apply pal_nil.
        +   rewrite H. apply pal_sing.
        +   rewrite H. rewrite H in Hrev. simpl in Hrev. rewrite rev_app_distr in Hrev. simpl in Hrev.
            injection Hrev as H1 H2. rewrite H1 in H2. rewrite H1. apply pal_more. rewrite H in Hlen. simpl in Hlen. apply Nat.succ_lt_mono in Hlen.
            apply length_app in Hlen. apply IH. apply Hlen. apply last_injective in H2. assumption.
Qed.

Definition finmap (n m : nat) (f : nat -> nat) : Prop :=
    forall (i: nat), i < n -> f i < m.

Definition inj (n : nat) (f : nat -> nat) : Prop :=
    forall (i j : nat), i < n -> j < n -> f i = f j -> i = j. 

Definition noninj (n : nat) (f : nat -> nat) : Prop := 
    exists (i j : nat), i < n /\ j < n /\ f i = f j /\ i <> j.

Lemma le_cases: forall (n m: nat), n <= m -> n = m \/ n < m.
Proof.
    induction n.
    -   induction m. 
        +   intros. left. reflexivity.
        +   intros. right. apply Nat.lt_0_succ.
    -   induction m.
        +   intros. Search le. apply Le.le_Sn_le_stt in H as H1. apply IHn in H1. destruct H1.
            *   rewrite H0 in H. Search le. specialize Nat.nle_succ_diag_l with (n:=0). intros. unfold not in H1. apply H1 in H. exfalso. auto.
            *   Search lt. specialize Nat.nlt_0_r with(n:=n) as H1. unfold not in H1. apply H1 in H0. exfalso. auto.
        +   intros. Search le. apply le_S_n in H. apply IHn in H. destruct H.
            *   left. f_equal. auto.
            *   right. Search lt. rewrite <- Nat.succ_lt_mono. auto.
Qed.

Lemma image_cases: forall (f: nat -> nat) (n v: nat),
    (forall i, i < n -> f i <> v) \/ (exists i, i < n /\ f i = v).
Proof. 
   intros f n v.
    induction n as [| n' IHn].
    - left. intros i H. inversion H.
    - destruct IHn as [H1 | H2].
        + destruct (Nat.eq_dec (f n') v) as [Heq | Hneq].
        * right. exists n'. split. apply Nat.lt_succ_diag_r. apply Heq.
        * left. intros i Hi. Search lt. rewrite Nat.lt_succ_r in Hi. Search le. apply le_cases in Hi. 
            destruct Hi. rewrite H. auto. apply H1 in H. auto.
        + right. destruct H2 as [i [H3 H4]]. exists i. split. Search lt. apply Nat.lt_lt_succ_r. auto. apply H4.
Qed.

Theorem inj_noninj : forall n f, ~inj n f <-> noninj n f. 
Proof.
    unfold inj, noninj.
    intros n f. split. 
    -   induction n as [ | n IH]; intros A. 
        +   exfalso. apply A. intros. lia.
        +   destruct (image_cases f n (f n)) as [C | [a [C1 C2]]].
            *   destruct IH. unfold not. intros B. apply A. intros. 
                apply PeanoNat.Nat.lt_eq_cases in H,H0. destruct H,H0.
                --  apply Nat.succ_lt_mono in H,H0. apply B;lia.  
                --  injection H0 as H0. apply Nat.succ_lt_mono in H. apply C in H. 
                    rewrite H0 in H1. lia.
                --  injection H as H. apply Nat.succ_lt_mono in H0. apply C in H0. 
                    rewrite H in H1. lia. 
                --  lia.
                --  destruct H as [y H]. exists x. exists y. lia.
            *   exists a. exists n. split. lia. split. lia. split. auto. lia. 
    - intros [a [b [A1 [A2 [A3 A4]]]]] B. apply A4. apply B; auto.
Qed.

Definition erase (f: nat -> nat) (i: nat) : nat -> nat := 
    fun x => if x <? i then f x else f (S x).

Lemma restr_lemma : forall f n m, finmap (S n) m f -> finmap n m f.
Proof. 
    unfold finmap. intros f n m H i Hlt. apply H. lia.
Qed. 

Lemma inj_restr_lemma : forall f n, inj (S n) f -> inj n f. 
Proof. 
    unfold inj. intros f n H a b A B C. apply H; lia.
Qed. 

Lemma range_lemma : forall f n m, finmap (S n) (S m) f -> 
    finmap n m f \/ exists i, i < S n /\ f i = m. 
Proof. 
(** My proof does not use induction, but appeals to image_cases. **)
    intros f n m. destruct (image_cases f (S n) (m)) as [C | [a [C1 C2]]].
    -   intros. unfold finmap in H. destruct (Nat.eq_dec (f n) m) as [Heq | Hneq].
        +   right. exists n. lia.
        +   left. unfold finmap. intros. Search lt. apply Nat.lt_lt_succ_r in H0. apply H in H0 as H1. apply C in H0 as H2. lia.
    -   intros. right. exists a. lia.
Qed.

Lemma n_lt_Sm: forall n m : nat, n < S m -> n = m \/ n < m.
Proof. lia. Qed.

Lemma n_lt_Sm_n_ne_m: forall n m: nat, n < S m /\ n <> m -> n < m.
Proof. lia. Qed.

Lemma erase_restr_lemma : forall f n m i, 
    finmap (S n) (S m) f -> inj (S n) f -> i < S n -> f i = m -> 
    finmap n m (erase f i) /\ inj n (erase f i).
Proof.
(** My proof does not use any induction, but lots of case analysis. **)
    intros. split.
    -   unfold finmap. intros. unfold erase. apply range_lemma in H as G. destruct (i0 <? i) eqn:E.
        +   destruct G as [G | G].
            *   unfold finmap in G. apply G. auto.
            *   unfold finmap in H. destruct G as [x [G1 G2]]. unfold inj in H0. 
                specialize H with (i:=i0) as HH. specialize H0 with (i:=i0) (j:=i) as H00.
                apply n_lt_Sm_n_ne_m. split. 
                --  apply HH. lia.
                --  rewrite Nat.ltb_lt in E. lia.
        +   unfold finmap in H, G. destruct G as [G | [x [G1 G2]]].
            *   Search ltb. rewrite Nat.ltb_ge in E.  apply G. unfold inj in H0. 
                apply n_lt_Sm_n_ne_m. split.
                --  lia.
                --  unfold not. intros. specialize G with (i:=i) as GG. apply n_lt_Sm in H1.
                    destruct H1 as [H1 | H1]. 
                    ++  lia.
                    ++  lia.
            *   rewrite Nat.ltb_ge in E. unfold inj in H0. apply n_lt_Sm in H1.
                destruct H1 as [H1 | H1].
                --  lia.
                --  clear G1 G2. apply n_lt_Sm_n_ne_m. split.
                    ++  specialize H with (i:=S i0). apply H. lia.
                    ++  unfold not. intros. 
                        specialize H with (i:=i0).
                        specialize H0 with (i:=i) (j:=S i0). lia.
    -   unfold inj, erase. unfold finmap in H. unfold inj in H0. intros. destruct (i0 <? i) eqn:E.
        +   destruct (j <? i) eqn:E1.
            *   rewrite Nat.ltb_lt in E, E1. 
                specialize H0 with (i:=i0) (j:=j). lia.
            *   rewrite Nat.ltb_lt in E. rewrite Nat.ltb_ge in E1. 
                specialize H0 with (i:=i0) (j:=S j). lia.
        +   destruct (j <? i) eqn:E1.
            *   rewrite Nat.ltb_lt in E1. rewrite Nat.ltb_ge in E.
                specialize H0 with (i:=S i0) (j:=j). lia.
            *   rewrite Nat.ltb_ge in E, E1.
                specialize H0 with (i:=S i0) (j:=S j). lia.
Qed.

Theorem php: forall n m f, finmap n m f -> m < n -> noninj n f.
Proof.
    intros n m f. rewrite <- inj_noninj. 
    generalize m f. clear f m. 
    induction n as [ | n IH]. 
    -   intros. inversion H0. 
    -   intros [ | m] f A Hlt Hinj. 
        apply A in Hlt. inversion Hlt.
        remember (range_lemma _ _ _ A) as B. clear HeqB. 
        destruct B as [B | [i [B C]]].
        *   apply inj_restr_lemma in Hinj. 
            apply IH in B. auto. lia.
        *   remember (erase_restr_lemma _ _ _ i A Hinj B C) as D.
            clear HeqD.
            destruct D as [D1 D2].
            apply IH in D1; auto. lia.
Qed. 

