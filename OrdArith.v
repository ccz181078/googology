Require Import Ordinal.
Require Import Coq.Arith.PeanoNat.

Section WithFuncExt.
(* 为了方便，引入函数外延公理 *)
Hypothesis func_ext : forall {A B: Type} {f g : A->B},
  (forall x, f x = g x) -> f = g.

(* (x+y)+z = x+(y+z) *)
Lemma oadd_assoc: forall x y z, oadd (oadd x y) z = oadd x (oadd y z).
intros.
induction z; cbn; auto.
- apply inv,IHz.
- apply inv,func_ext,H.
Qed.

(* x*(y+z) = x*y+x*z *)
Lemma omult_add_distr_r: forall x y z, omult x (oadd y z) = oadd (omult x y) (omult x z).
intros.
induction z; cbn; auto.
- rewrite IHz.
  apply oadd_assoc.
- apply inv,func_ext,H.
Qed.

(* (x*y)*z = x*(y*z) *)
Lemma omult_assoc: forall x y z, omult (omult x y) z = omult x (omult y z).
intros.
induction z; cbn; auto.
- rewrite IHz.
  apply eq_sym.
  apply omult_add_distr_r.
- apply inv,func_ext,H.
Qed.

(* 0+x = x *)
Lemma oadd_0_x: forall x, oadd Zero x = x.
intros.
induction x; cbn; auto. 
- apply inv,IHx.
- apply inv,func_ext,H.
Qed.

(* x*n+x = x+x*n *)
Lemma omult_n_add_comm: forall (x:On)(n:nat), oadd (omult x n) x = oadd x (omult x n).
intros.
induction n; cbn.
- apply oadd_0_x.
- rewrite IHn.
  rewrite oadd_assoc.
  apply inv,IHn.
Qed.

(* 1*x = x *)
Lemma omult_1_x: forall x, omult 1 x = x.
intros.
induction x; cbn; auto. 
- apply inv,IHx.
- apply inv,func_ext,H.
Qed.

(* x^1 = x *)
Lemma opower_x_1: forall x, opower x 1 = x.
intros.
cbn.
apply omult_1_x.
Qed.

(* a^(b+c) = (a^b)*(a^c) *)
Lemma opower_add_distr_r: forall x y z, opower x (oadd y z) = omult (opower x y) (opower x z).
intros.
induction z; cbn.
- rewrite oadd_0_x.
  apply eq_refl.
- rewrite IHz.
  apply omult_assoc.
- apply inv,func_ext,H.
Qed.

(* a^(b*c) = (a^b)^c *)
Lemma opower_mult_assoc: forall x y z, opower x (omult y z) = (opower (opower x y) z).
intros.
induction z; cbn; auto.
- rewrite <-IHz.
  rewrite opower_add_distr_r.
  apply eq_refl.
- apply inv,func_ext,H.
Qed.

End WithFuncExt.


(* 序数运算是自然数运算的推广 *)
Lemma oSuc_on_nat: forall a:nat, (ω_ (S a)) = Suc a.
intro.
induction a; cbn; auto.
Qed.

Lemma oadd_on_nat: forall a b:nat, (ω_ (plus a b)) = oadd a b.
intros.
induction b; cbn; auto.
rewrite <-IHb.
rewrite <-oSuc_on_nat.
auto.
Qed.

Lemma omult_on_nat: forall a b:nat, (ω_ (mult a b)) = omult a b.
intros.
induction b; cbn.
- rewrite <-mult_n_O; auto.
- rewrite <-IHb.
  rewrite Nat.mul_comm.
  cbn.
  rewrite Nat.mul_comm,Nat.add_comm.
  apply oadd_on_nat.
Qed.

Lemma opower_on_nat: forall a b:nat, (ω_ (Nat.pow a b)) = opower a b.
intros.
induction b; cbn; auto.
rewrite <-IHb,Nat.mul_comm.
apply omult_on_nat.
Qed.


(* SGH保持序数运算 *)
Lemma g_nat: forall a n:nat, g a n = a.
intros a n.
induction a; cbn; auto.
Qed.

Lemma g_oadd: forall a b n, g (oadd a b) n = (g a n)+(g b n).
intros a b.
induction b; cbn; auto.
intro n.
rewrite IHb.
auto.
Qed.

Lemma g_omult: forall a b n, g (omult a b) n = (g a n)*(g b n).
intros a b.
induction b; cbn; auto.
intro n.
rewrite g_oadd,IHb.
auto.
Qed.

Lemma g_opower: forall a b n, g (opower a b) n = (g a n)^(g b n).
intros.
induction b; cbn; auto.
rewrite g_omult,IHb.
apply Nat.mul_comm.
Qed.

Lemma g_ωpow: forall a n, g (ωpow a) n = n^(g a n).
intros.
induction a; cbn; auto.
rewrite <-IHa.
rewrite g_omult,g_nat.
apply Nat.mul_comm.
Qed.


