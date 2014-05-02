Parameter A B C : Prop.

Theorem vaja2: A /\ B -> B /\ A.
Proof.
  intro.
  split.
  - destruct H.
    assumption.
  - destruct H.
    assumption.
Qed.

Theorem vaja2_drugic: A /\ B -> B /\ A.
Proof.
  tauto.
Qed.

Theorem vaja1: A -> (B -> A).
Proof.
  intro.
  intro.
  assumption.
Qed.

Theorem vaja3: A \/ A -> A.
Proof.
  intros G.
  destruct G.
  - assumption.
  - assumption.
Qed.

Theorem vaja3': A \/ A -> A.
Proof.
  intros [G1|G2]. (*Kombiniran intro-destruct, kjer poves kako naj destructa - na G1 in G2.*)
  - assumption.
  - assumption.
Qed.

Theorem vaja3'': A \/ A -> A.
Proof.
  intros [?|?]. (*Sam poimenuje hipoteze. Ce das not _, pa dano hipotezo ignorira.*)
  - assumption.
  - assumption.
Qed.

Theorem vaja4: (A \/ B -> C) -> (A -> C) /\ (B -> C).
Proof.
  intro.
  split.
  - intro.
    apply H.
    left.
    assumption.
  - intro.
    apply H.
    right.
    assumption.
Qed.

Theorem vaja5: (A -> C) /\ (B -> C) -> (A \/ B -> C).
Proof.
  intros [H1 H2] [G1|G2]. (* intros. destruct H. destruct G. *)
  - apply H1.
    assumption.
  - apply H2.
    assumption.
Qed.

Theorem vaja8: ~ (A \/ B) -> ~ A /\ ~ B.
Proof.
  intro.
  split.
  - intro.
    absurd (A \/ B). (* ktera izjava je taka, da bomo dokazal izj in ne izj. rabmo jo pa zto, kr hocmo F dokazat. *)
    + assumption.
    + left.
      assumption.
  - intro.
    absurd (A \/ B).
    + assumption.
    + right.
      assumption.
Qed.


Theorem vaja7: A -> ~ ~ A.
Proof.
  intros H G. (* s tem ga prsilis da bo dva introja nardu. Sicer jih neb, k sam od sebe ne uposteva def. negacije. *)
  apply G.
  assumption.
Qed.


Print vaja7.

Theorem vaja6: ~ (A /\ ~A).
Proof.
  intro.
  absurd A.
  - apply H.
  - apply H.
Qed.







  
