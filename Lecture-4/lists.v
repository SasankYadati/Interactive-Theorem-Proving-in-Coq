Inductive natprod: Type :=
    | pair (n1 n2 : nat).

Check (pair 3 5): natprod.

Definition fst (p: natprod) : nat :=
    match p with
    | pair x y => x
    end.

Definition snd (p: natprod) : nat :=
    match p with
    | pair x y => y
    end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing: forall (p: natprod),
    p = (fst p, snd p).
Proof.
    intros p. destruct p as [n m]. simpl. reflexivity. 
Qed.

Theorem snd_fst_is_swap: forall p,
    (snd p, fst p) = swap_pair p.
Proof.
    intros p. destruct p. simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd: forall p,
    fst (swap_pair p) = snd p.
Proof.
    intros p. destruct p. reflexivity.
Qed.

Inductive natlist: Type :=
    | nil
    | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | 0 => nil
    | S count' => n :: (repeat n count')
    end.

Fixpoint length (l:natlist) : nat :=
    match l with
    | [] => 0
    | h :: t => S (length t)
    end.

Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | []        => l2
    | h :: t    => h :: (app t l2)
    end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default: nat) (l: natlist) : nat :=
    match l with
    | nil       => default
    | h :: t    => h
    end.

Definition tl (l: natlist) : natlist :=
    match l with
    | nil       => nil
    | h :: t    => t
    end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
    | nil => []
    | 0 :: t => nonzeros t
    | h :: t => h :: (nonzeros t)
    end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).

Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
    | nil       => []
    | h :: t    => if odd h then (h::(oddmembers t)) else (oddmembers t)
    end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
    length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | h::t, H::T => h :: H :: (alternate t T)
    end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag :=  natlist.

Require Import Arith.

Fixpoint eqb (n m : nat) : bool :=
  match n,m with
    | 0,0 => true
    | 0,_ => false
    | _,0 => false
    | S n', S m' => eqb n' m' 
  end.

Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
    | nil => 0
    | h :: t => if eqb h v then S (count v t) else count v t
    end. 

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
    v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool :=
    match s with
    | nil => false
    | h :: t => if eqb v h then true else member v t
    end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
    match s with
    | []        => []
    | h :: t    => if eqb v h then t else h :: (remove_one v t)
    end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
    | []        => []
    | h :: t    => if eqb v h then remove_all v t else h :: (remove_all v t)
    end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint included (s1:bag) (s2:bag) : bool :=
    match s1 with
    | [] => true
    | h :: t => if member h s2 then included t (remove_one h s2) else false
    end.

Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Theorem add_inc_count: forall (v:nat) (b:bag),
    count v (add v b) = S (count v b).
Proof.
    intros v b.
    simpl.
    assert (H: forall n, eqb n n = true).
    {
        induction n.
        - simpl. reflexivity.
        - simpl. apply IHn.
    } 
    rewrite -> H. reflexivity.
Qed.

Theorem nil_app: forall l: natlist,
    [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred: forall l: natlist,
    pred (length l) = length (tl l).
Proof.
    intros l. destruct l as [|n l'].
    - reflexivity.
    - reflexivity.
Qed.

Theorem app_assoc: forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
    intros l1 l2 l3. induction l1 as [| n l1' IH].
    - simpl. reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
    match l with
    | nil       => nil
    | h :: t    => rev t ++ [h]
    end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length: forall l1 l2:natlist,
    length (l1 ++ l2) = length l1 + length l2.
Proof.
    induction l1 as [| n l1' IH].
    - simpl. reflexivity.
    - simpl. intros l2. rewrite -> IH. reflexivity.
Qed.

Require Import Nat.

Theorem rev_length: forall l: natlist,
    length (rev l) = length l.
Proof.
    induction l as [|n l' IH].
    - reflexivity.
    - simpl. rewrite -> app_length.
      simpl. rewrite -> IH. rewrite Nat.add_comm. 
      reflexivity.
Qed.

Theorem app_nil_r: forall l : natlist,
    l ++ [] = l.
Proof.
    induction l as [|n l' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1 as [|n l1' IH].
  - intros l2. simpl. rewrite -> app_nil_r. reflexivity.
  - intros l2. simpl. rewrite -> IH. rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive: forall l: natlist,
    rev (rev l) = l.
Proof.
    induction l as [|h t IH].
    - reflexivity.
    - simpl. rewrite -> rev_app_distr. simpl. rewrite -> IH. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
    intros.
    rewrite -> app_assoc. 
    rewrite -> app_assoc.
    reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
    induction l1 as [|h t IH].
    - simpl. reflexivity.
    - intros. destruct h.
        + simpl. apply IH.
        + simpl. rewrite -> IH. reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
    match l1, l2 with
    | nil, nil => true
    | _, nil => false
    | nil, _ => false
    | h1::t1, h2::t2 => if h1=?h2 then eqblist t1 t2 else false
    end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
    intros. induction l as [|h t IH].
    - reflexivity.
    - simpl. Search eqb. rewrite -> Nat.eqb_refl. apply IH.
Qed.

Theorem count_memeber_nonzero : forall (s: bag),
    1 <=? (count 1 (1::s)) = true.
Proof.
    intros. simpl. reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
    n <=? (S n) = true.
Proof.
    intros n. induction n as [|n' IH].
    - reflexivity.
    - simpl. apply IH.
Qed.

Theorem remove_does_not_increase_count : forall (s:bag),
    (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
    induction s as [|h t IH].
    - reflexivity.
    - destruct h.
        + simpl. apply leb_n_Sn.
        + simpl. apply IH.
Qed.

Theorem bag_count_sum : forall (s1 s2: bag) (n:nat),
    count n (sum s1 s2) = count n s1 + count n s2.
Proof.
    intros. induction s1.
    - intros. simpl. reflexivity.
    - simpl. destruct (lists.eqb n0 n).
        + rewrite -> IHs1. simpl. reflexivity.
        + apply IHs1.
Qed.

Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
    intros f H1 n1 n2 H2. 
    rewrite -> H1. 
    rewrite <- H2.
    rewrite <- H1.
    reflexivity.
Qed.

Theorem rev_injective : forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
Proof.
    intros.
    rewrite <- rev_involutive.
    rewrite <- H.
    symmetry. apply rev_involutive.
Qed.

Inductive natoption : Type :=
    | Some (n : nat)
    | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
    match l with
    | nil   => None
    | h::t  => match n with
                | 0     => Some h
                | S n'  => nth_error t n'
                end
    end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Definition option_elim (d:nat) (o:natoption) : nat :=
    match o with
    | Some n'   => n'
    | None      => d
    end.

Definition hd_error (l : natlist) : natoption :=
    match l with
    | []    => None
    | h::t  => Some h
    end.
Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
    hd default l = option_elim default (hd_error l).
Proof.
    destruct l.
    - simpl. reflexivity.
    - intros. simpl. reflexivity.
Qed.

Inductive id : Type :=
    | Id (n :nat).

Definition eqb_id (x1 x2 : id) :=
    match x1, x2 with
    | Id n1, Id n2 => n1 =? n2
    end.

Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
    intros. destruct x. simpl. 
    rewrite -> Nat.eqb_refl. reflexivity.
Qed.

Inductive partial_map : Type :=
    | empty
    | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map) (x : id) (value : nat) : partial_map :=
    record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
    match d with
    | empty         => None
    | record y v d' => if eqb_id x y then Some v else find x d'
    end.

Theorem update_eq : forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
    intros. simpl. rewrite -> eqb_id_refl. reflexivity.
Qed.

Theorem update_neq : forall (d: partial_map) (x y : id) (o : nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
    intros.
    simpl.
    rewrite -> H.
    reflexivity.
Qed.


