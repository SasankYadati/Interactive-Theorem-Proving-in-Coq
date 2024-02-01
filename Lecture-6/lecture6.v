Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
    intros X P Q. split.
    -   intros [w [G | H]]. 
        +   left. exists w. assumption.
        +   right. exists w. assumption.
    -   intros [[w G] | [w H]].
        +   exists w. left. assumption.
        +   exists w. right. assumption.
Qed.
