Require Import List.
Require Import Bool.
Require Import ZArith.

Local Open Scope list_scope.
Local Open Scope Z_scope.


(* Lets get this partey started! *)
Fixpoint urejen (l : list Z) :=
  match l with
    | nil => True
    | _ :: nil => True
    | x :: ((y :: _) as l') => x <= y /\ urejen l'
  end.

Lemma urejen_tail (x : Z) (l : list Z) :
  urejen (x :: l) -> urejen l.
Proof.
  induction l ; firstorder.
Qed.

Lemma urejen_head (x : Z) (l : list Z) :
  urejen (x :: l) -> forall y, In y l -> x <= y.
Proof.
  generalize x ; clear x.
  induction l.
  - simpl ; tauto.
  - intros x [H G] z [K|K].
    + now destruct K.
    + transitivity a ; auto.
Qed.

Lemma urejen_lt_cons (x : Z) (l : list Z) :
  (forall y : Z, In y l -> x <= y) -> urejen l -> urejen (x :: l).
Proof.
  intros H G.
  induction l ; [ simpl ; auto | idtac ].
  split.
  - apply H ; simpl ; auto.
  - destruct l ; simpl ; auto.
Qed.

Fixpoint vstavi (x: Z) (l: list Z) :=
  match l with
    | nil => x::nil
    | a::l' => match (Z.leb x a) with
                 | true => (x::a::l')
                 | false => (a::(vstavi x l'))
               end
(*    | a::l' => (Zmin x a)::(vstavi (Zmax x a) l')  *)
  end.

Eval compute in (vstavi 5 (1::2::4::7::8::9::nil)).
Eval compute in (vstavi 3 nil).

(*Fixpoint urejen2 (l: list Z) :=
  match l with
    | nil => True
    | x::l' => match l' with 
                 | nil => True
                 | y::t => match (Z.leb x y) with
                             | true => (urejen2 l')
                             | false => False
                           end
               end    
  end.
Eval compute in urejen2 nil.
Eval compute in urejen2 (1::nil).
Eval compute in urejen2 (1::2::3::4::6::8::nil).
Eval compute in urejen2 (1::2::3::24::6::18::nil).
Eval compute in urejen2 (1::2::nil).
Eval compute in urejen2 (3::2::nil). *)

(*Fixpoint urejen3 (l : list Z) :=
  match l with
    | nil => True
    | _ :: nil => True
    | x :: ((y :: _) as l') => x <= y /\ urejen3 l'
  end.*)

(*Lemma urejen_urejenega (x: Z) (lis: list Z): 
  (urejen lis) /\ (forall y: Z, (In y lis) -> x<y) -> urejen (x::lis).
Proof.
  intro.
  destruct H. destruct H0.
Qed.*)

Lemma pomozna1 (x: Z) (sez: list Z): 
  forall y: Z, In y (x::sez) -> y=x \/ (In y sez).
Proof.
  intros. induction (sez).
  - destruct H. 
    + left. symmetry. apply H.
    + right; assumption.
  - destruct H.
    + left; symmetry; assumption.
    + right; assumption.
Qed.

Lemma pomozna2 (x: Z) (sez: list Z): 
  forall y: Z, In y (vstavi x sez) -> y=x \/ (In y sez).
Proof.
  intros.
  induction sez.
  - simpl in H. left. destruct H; auto. destruct H.
  - unfold vstavi in H. case_eq (x <=? a).
    + intro. rewrite H0 in H.
      destruct H.
      * left; symmetry; apply H.
      * right; apply H.
    + intro. rewrite H0 in H. fold vstavi in H. destruct H.
      * right. simpl. left; apply H.
      * simpl. destruct IHsez. apply H. left. apply H1. 
        right; right; apply H1.
Qed.


Lemma vstavi_urejen (x:Z) (l:list Z):
  (urejen l) -> urejen (vstavi x l).
Proof.
  induction l.
  - simpl ; auto.
  - intro H.
    case_eq (x <=? a).
    + intro.
      apply Zle_bool_imp_le (*Z.ltb_lt*) in H0.
      replace (vstavi x (a::l)) with (x::a::l).
      * simpl. split. apply H0. apply H.
      * simpl. replace (x <=? a) with true.
        (*elim H0. SearchAbout ((?x ?= ?a) = Gt). 
        apply Z.compare_gt_iff.*)
        auto. symmetry; generalize H0; apply Zle_imp_le_bool.
    + intro. (* SearchAbout ((?x <=? ?a) = false). apply Z.leb_gt in H0.*)
      simpl; rewrite H0.
      generalize H. apply urejen_tail in H. intro H2.
      apply urejen_lt_cons.
      * intro. intro. apply pomozna2 in H1. destruct H1.
          rewrite H1. apply Z.lt_eq_cases.
          apply Z.leb_gt in H0. left; apply H0.
          generalize H1. apply urejen_head. apply H2.
      * apply IHl. apply H.
Qed.


Fixpoint insertion (l:list Z) :=
  match l with 
    | nil => nil
    | x::l' => vstavi x (insertion l')
  end.

Theorem insertion_uredi(l:list Z):
  urejen(insertion(l)).
Proof.
  induction l; simpl in * |- *; auto.
  apply vstavi_urejen. apply IHl.
Qed.

