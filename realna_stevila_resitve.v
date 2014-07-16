(** V teh vajah se bomo učili uporabljati standardno knjižnico
v Coqu (http://www.lix.polytechnique.fr/coq/stdlib/).
Knjižnica ima veliko koristnih izrekov in definicij. Ponavadi
je glavna težava v tem, da je težko najti izrek, ki ga v
danem trenutku potrebujemo. Coq ima nekaj ukazov, s katerim
lahko prgledujemo knjižnico in iščemo potencialno koristne
izreke.

Najprej bomo vadili uporabo knjižnice za realna števila, zato jo
najprej zahtevamo z ukazom [Require Import].
*)

Require Import Reals.

(** Večinoma bomo uporabljali notacijo za realna števila. Na primer,
želimo, da bi "x + y" pomenilo seštevanje realnih števil, ne naravnih.
Lahko bi vsakič pisali "(x + y)%R", a je bolj praktično, da vključimo
notacijo za realna števila z ukazom [Local Open Scope]. *)

Local Open Scope R_scope.

(* Če bomo potrebovali operacije na naravnih številih, lahko še vedno
pišemo "(x + y)%nat". *)

(** Dokažimo preprosto neenačbo. *)
Theorem vaja_1 (x y : R) : x^2 + y^2 >= 2 * x * y.
Proof.
  (* Postopek dokaza je naslednji:

- prenesemo vse na eno stran: x^2 - 2 * x * y + y^2 >= 0
- faktoriziramo: (x - y)^2 >= 0
- opazimo, da je kvadrat števila nenegativen

Prva težava: kako prenesemo [2 * y * x] na drugo stran neenačbe?
Verjetno obstaja ustrezna lema v knjižnici. Treba je malo brskati.
Poskusite in če ne najdete odgovora v 5 minutah, poglejte rešitev
v tej datoteki. Iščite v knižnici [RIneq],
http://www.lix.polytechnique.fr/coq/stdlib/Coq.Reals.RIneq.html

Rešitev je nižje spodaj.

|
|
V
































Lenoba lena, malo bolj se potrudi!








































Lema, ki jo iščemo je [Rminus_ge]. O njej izvemo več z ukazom
[Check Rminus_ge.], ki pove:

Rminus_ge : forall r1 r2 : R, r1 - r2 >= 0 -> r1 >= r2
*)
 apply Rminus_ge.
 (** Sedaj bi radi faktorizirali. To je najlažje narediti tako,
da Coq-u povemo, naj zamenja [x^2 + y^2 - 2 * x * y] s
kvadratom [(x - y)^2]. Če bi to naredili, bi se nam kasneje
zataknilo: v knjižnici je kvadrat realnega števila definiran
kot [Rsqr x]. Zato je bolje, da [Rsqr] uporabimo tudi mi.

Lahko pa bi tudi v knjižnici poiskali lemo [Rsqr_plus],
vendar tega zdaj ne bomo naredili, da vidimo, kako se dela
na roke.
*)
  replace (x^2 + y^2 - 2 * x * y) with (Rsqr (x - y)).
  - (* Spet iščemo lemo, tokrat, da je kvadrat nenegativen.
Hitro najdemo

Lemma Rle_0_sqr : forall r, 0 <= Rsqr r.

Na žalost gre v napačno smer, mi potrebujemo Rsqr r >= 0.
Najprej moramo svojo neenačbo obrniti. Torej potrebujemo
lemo, ki pravi [x <= y -> y >= x]. Spet malo pogledamo in
najdemo [Rle_ge]. *)
    apply Rle_ge.
    apply Rle_0_sqr.
    (* Kot vidimo, je vse skupaj ena nočna mora. Hej, bomo vsaj imeli dokaz z vsemi
podrobnostmi. *)
    - (* Tu bi bilo najbolj logično, če bi uporabili poenostavljanje
izrazov. To se lahko v splošnem naredi s [simpl] in s [compute]. Za delo s
kolobarji (realna števila tvorijo kolobar, saj tvorijo obseg) imamo taktiki
[ring_simpify] in [ring]. Z nekaj poskušanja ugotovimo, da je pravo
zaporedje [compute] in [ring]. *)
       compute.
       ring.
Qed.

(** Naslednjo vajo naredite sami. Ideja: x^4 je treba napisati kot Rsqr (x^2). *)
Theorem vaja_2 : forall x : R, 0 <= x^4.
Proof.
  intro.
  replace (x^4) with (Rsqr(x^2)).
  - apply Rle_0_sqr.
  - compute.
    ring.
Qed.

(* GLEJ LINK http://www.lix.polytechnique.fr/coq/stdlib/Coq.Reals.RIneq.html#Rsqr !!! *)


(** Iskanje po spletnih straneh je lahko precej zamudno. V Coq-u lahko
iščemo tudi z ukazi:

- [SearchAbout Rsqr] poišče vse izreke, ki omenjajo [Rsqr].
- [SearchAbout "+"] poišče vse izreke, ki omenjajo "+" (tu podamo kar notacijo,
lahko bi tudi rekli [SearchAbout Rplus]).
- [SearchAbout (Rsqr (?x - ?y))] poišče vse izreke, v katerih se pojavi izraz
oblike "Rsqr (?x - ?y)", kjer sta ?x in ?y poljubna. V splošnem lahko
napišemo poljuben vzorec, kjer z ?x, ?y, ... označimo tiste dele vzorca,
ki so poljubni.

Polna dokumentacija za [SearchAbout] in [SearchPattern] je na
http://coq.inria.fr/V8.2pl1/refman/Reference-Manual009.html#@command105

Ukaz [SearchPattern vzorec] sprejme vzorec in vrne vse izreke, katerih
*sklep* ustreza danemu vzorcu.
*)
(** Naslednje vaje reši s pomočjo ukaza [SearchAbout]. Vsaka od vaj je rešljiva
s preprosto uporabo [apply] izreka iz knjižnice. *)

Theorem vaja_3 (x : R) : 0 < Rsqr x -> x <> 0.
Proof.
  (* Uporabi: SearchAbout Rsqr. *)
  SearchAbout Rsqr.
  apply Rsqr_gt_0_0.
Qed.

Theorem vaja_4 (x : R) : x < x + 1.
Proof.
  (* Uporabi: SearchPattern (?x < ?x + 1). *)
  SearchPattern (?x < ?x + 1).
  apply Rlt_plus_1.
Qed.

Theorem vaja_5 (x : R) : sin (2 * x) = 2 * sin x * cos x.
Proof.
  (* SearchAbout (sin (2 * ?x)). *)
  SearchAbout (sin (2 * ?x)).
  apply sin_2a.
Qed.

(** Tu je še nekaj bolj zanimivih vaj. Pomagajte si s [SearchAbout]
in [SearchPattern]. *)

Theorem vaja_6 : forall x : R, 0 < x -> 0 < x * x * x.
Proof.
  intro.
  intro.
  replace (x*x) with (Rsqr(x)).
  SearchAbout Rsqr.
  SearchPattern (0 < ?a * ?b).
  - apply Rmult_lt_0_compat.
    + apply Rsqr_pos_lt.
      firstorder.
   (* intro.
      absurd (0 < x).
      * subst.
        firstorder.
      * apply H. *)
    + apply H.
  - compute.
    ring.
Qed.

Theorem vaja_7 (x : R) : sin (3 * x) = 3 * (cos x)^2 * sin x - (sin x)^3.
Proof.
  SearchAbout (sin (3 * ?x)).
  SearchAbout (sin (?a + ?b)).
  replace (3 * x) with (x + 2 * x).
  - rewrite sin_plus.
    rewrite cos_2a.
    rewrite sin_2a.
    rewrite Rmult_minus_distr_l.
    ring.
  - symmetry. rewrite Rmult_plus_distr_r.
    ring.
Qed.

Theorem vaja_8 (x y : R) :
  0 <= x -> 0 <= y -> Rabs (x + y) = Rabs x + Rabs y.
Proof.
  intros.
  SearchAbout (Rabs (?x)).
  rewrite Rabs_pos_eq. rewrite Rabs_pos_eq. rewrite Rabs_pos_eq.
  - ring.
  - apply H0.
  - apply H.
  - SearchAbout (0 <= ?x + ?y).
    apply Rplus_le_le_0_compat.
    assumption. assumption.
Qed.

Theorem vaja_9 : forall x : R, x <= 0 -> x * x * x <= 0.
Proof.
  intros.
  replace (x*x*x) with (x*Rsqr(x)).
  (*SearchAbout (Rsqr(?x)).
  SearchAbout (?a*?b).
  SearchAbout (?a <= ?b).*)

(*  replace (0) with (0*Rsqr(x)).
   - SearchPattern ( ?x * ?y <= ?z).
     apply Rmult_le_compat_r.
      + apply Rle_0_sqr.
      + assumption.
   - ring.
   - compute. ring.*)

  (*BLIŽJE KOT SPODAJ, AMPAK ŠE ZMERI OMGGGG...*)
  destruct H.
  - left.
    (*SearchAbout (?x*?y = ?y*?x).*)
    (*rewrite Rmult_comm. *)
   SearchAbout (?a * ?b > 0).
    replace (x) with (--x).
    (*Samo en minus daš ven: *)
    + rewrite Ropp_mult_distr_l_reverse.
      apply Ropp_lt_gt_0_contravar.
      apply Rmult_gt_0_compat.
      * apply Ropp_gt_lt_0_contravar. assumption.
      * rewrite  Ropp_involutive. SearchAbout (Rsqr (?x)).
        apply Rsqr_pos_lt.
        SearchAbout (?x<>0). intro.  destruct H0.
        SearchAbout (?x < ?x). apply (Rlt_irrefl x). assumption.
    + apply Ropp_involutive.
  - rewrite H. compute. firstorder.
  - unfold Rsqr. firstorder.
Qed.
        
          

(*OMG KLOBASA IN VRTENJE V KROGU.
    rewrite tech_pow_Rmult.
    replace (x) with (--x).
    + replace (--x) with ((-1)*(-x)).
      * rewrite Rpow_mult_distr.
        replace ((-1)^3) with (-1).
        compute.
        rewrite Ropp_mult_distr_l_reverse. rewrite Ropp_mult_distr_l_reverse.
        rewrite Ropp_mult_distr_l_reverse. rewrite Ropp_mult_distr_l_reverse.
        rewrite Rmult_1_r. rewrite Rmult_comm. rewrite Rmult_1_r.
        rewrite  Ropp_involutive. 
        admit. (*????????*)
        symmetry.
        compute. 
        rewrite Ropp_mult_distr_l_reverse.
        rewrite Rmult_1_r. 
        rewrite Ropp_mult_distr_l_reverse.
        rewrite Rmult_comm.
        rewrite Rmult_1_r. rewrite Rmult_comm. rewrite Rmult_1_r. 
        apply Ropp_involutive.
      * rewrite Rmult_opp_opp. rewrite Ropp_involutive. firstorder.
    + apply Ropp_involutive.
  - right. rewrite H. firstorder.
  - ring. *)

Theorem vaja_10 : forall x : R, 0 < x * x * x -> 0 < x.
Proof.
  intros.
  replace (x*x) with (Rsqr(x)) in H.
  replace 0 with (0*(Rsqr x)) in H. 
  rewrite Rmult_comm in H.
  SearchAbout (?a*?b < ?a*?c). 
  apply Rmult_gt_reg_l in H.
  - assumption.
  - SearchAbout (Rsqr ?x).
    assert (~ x=0). intro. absurd ((Rsqr x)*x = 0). 
    + replace ((Rsqr x)*0) with (0) in H.
      * intro. rewrite H1 in H.
        SearchAbout (?a < ?a).
        apply (Rlt_irrefl 0). apply H.
      * SearchAbout (?x * 0). symmetry. apply (Rmult_0_r (Rsqr x)).
    + rewrite H0. unfold Rsqr. ring.
    + apply Rsqr_pos_lt. apply H0.
 - rewrite Rmult_comm. apply (Rmult_0_r (Rsqr x)).
 - unfold Rsqr. ring.
Qed.






