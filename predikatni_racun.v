(* Osnovne vaje iz logike 1. reda. *)

(* Uporabimo knjižnico, ki ima taktiko omega. Ta zna delati z naravnimi števili,
   če nastopajo samo linearne funkcije. *)
Require Import Omega.

(* Tip naravnih števil je nat. Ima element 0, operacijo naslednik S in običajne
   aritmetične operacije. *)

Theorem vaja_1:
  forall n : nat, exists m : nat, n < m.
Proof.
  intro.
  exists (S n). (* (S n) - naslednik od n. *)
  omega.
  (* admit - ce se bos na ta del se kasneje vrnil, za zdaj pa ga naj smatra kot 
     dokazanega. *)
Qed.

Theorem vaja_2 (n : nat): exists m : nat, n < m.
Proof.
  exists (1 + n).
  omega.  (* Tle bi delal tudi auto. Ne bi pa delal, ce bi pisali exists (n + 1),
             saj je sestevanje definirano s pomocjo rekurzije na prvem clenu. *)
Qed.

Theorem vaja_4 (n m : nat): 2 * n + m + 1 = m + n + 1 + n.
Proof.
  omega.
Qed.

Theorem vaja_5 (n : nat): (exists m : nat, n = 2 * m) \/ (exists m : nat, n = 1 + 2 * m).
Proof.
  induction n.
  - left.
    exists 0.
    auto.
  - destruct IHn.
    + right.
      destruct H.
      exists x.
      auto.
    + left.
      destruct H.
      exists (S x).
      omega.
Qed.

Theorem vaja_6: forall n, exists m, n = 3 * m \/ n = 3 * m + 1 \/ n = 3 * m + 2.
Proof.
  intro.
  induction n.
  - exists 0.
    left.
    auto.
  - destruct IHn as [m [Babitty|[Rabitty|Blop]]].
    + exists m.
      right; left.
      omega.
    + exists m; right; right; omega.
    + exists (S m); left; omega.
Qed.

(* Predpostavimo, da imamo množici A in B. *)
Parameter A B : Set. 

(* Predpostavimo, da imamo predikat P na A in  Q na B. *)
Parameter P : A -> Prop.
Parameter Q : B -> Prop.

Theorem vaja_7:
  forall y : B, (forall x : A , P x /\ Q y) -> (forall z : A, P z).
Proof.
  intro.
  intro.
  intro x.
  apply H.
Qed.

(* Predpostavimo relacijo R med A in B. *)
Parameter R : A -> B -> Prop.

Theorem vaja_8:
  (exists x : A, forall y : B, R x y) -> (forall y : B, exists x : A, R x y).
Proof.
  intro.
  intro.
  destruct H.
  exists x.
  apply H.
Qed.

Theorem vaja_9:
  ~ (exists x : A, P x) <-> forall x : A, ~ P x.
Proof.
  split.
  - intros.
    intro.
    absurd (exists x : A, P x).
    + assumption.
    + exists x; apply H0.
  - intros.
    intro.
    destruct H0 as [x0 G].
    absurd  (P x0).
    + apply H.
    + assumption.
Qed.

(* Zakon o izključeni tretji možnosti. 
   Tu smo ga samo definirali, nismo ga predpostavili! *)
Definition lem := forall P : Prop, P \/ ~ P.

(* Zakon o dvojni negaciji. *)
Definition dn := forall P : Prop, ~ ~ P -> P.

Lemma vaja_10: lem -> dn.
Proof.
  unfold lem, dn.
  intro.
  intros P.
  intro.
  
  apply H.
  intro.
  absurd 
Qed.

Lemma vaja_11: dn -> lem.
Proof.
  (* naredimo na predavanjih *)
  admit.
Qed.
  
Theorem vaja_12:
  (exists x : A, P x) -> ~ forall x : A, ~ P x.
Proof.
  (* naredimo na vajah *)
  admit.
Qed.

Theorem vaja_13:
  dn -> (~ forall x : A, ~ P x) -> exists x : A, P x.
Proof.
  (* naredimo na vajah *)
  admit.
Qed.
