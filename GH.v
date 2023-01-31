Require Import Ordinal.
Require Import OrdArith.
Require Import Coq.Arith.PeanoNat.

(*
这里讨论FGH、HH等增长层级的一些性质
*)

Lemma mult_n_2 n: n*2 = n+n.
rewrite Nat.mul_comm.
apply (inv (plus n)). auto.
Qed.

Module FGH.

Lemma iter_S n c: iter (fun n0 : nat => S n0) n c = n + c.
induction n; cbn; auto.
Qed.

Lemma FGH_0 n: f 0 n = S n.
auto.
Qed.

Lemma FGH_1 n: f 1 n = n*2.
rewrite mult_n_2.
apply iter_S.
Qed.

Lemma FGH_2 n: f 2 n = n*(2^n).
rewrite Nat.mul_comm.
cbn.
assert (forall c, iter (fun n0 : nat => iter (fun n1 : nat => S n1) n0 n0) n c = 2 ^ n * c). {
intro c.
induction n; cbn; auto.
rewrite IHn,iter_S.
rewrite <-Nat.mul_add_distr_l,<-mult_n_2,(Nat.mul_comm c 2),Nat.mul_assoc,(Nat.mul_comm _ 2).
auto.
}
apply H.
Qed.

End FGH.

Module HH.

Section WithFuncExt.
(* 为了方便，引入函数外延公理 *)
Hypothesis func_ext : forall {A B: Type} {f g : A->B},
  (forall x, f x = g x) -> f = g.

(*
h_0(n) = n
h_{x+1}(n) = h_x(n+1)
h_x(n) = h_{x[n]}(n), x is Lim
HH的定义和FGH、SGH等的递归方式不同
但接下来可以证明，HH和FGH非常相似
*)

(* h_{a+ω^b}(n)=h_a(f_b(n)) *)
Theorem h_add_ωpow(a b:On): forall n, h (oadd a (ωpow b)) n = h a (f b n).
generalize dependent a.
induction b; cbn; auto.
intros a n.
generalize dependent a.
assert (forall a c, h (oadd a (omult (ωpow b) n)) c = h a (iter (f b) n c)). {
  induction n; cbn; auto.
  intros a c.
  rewrite <-IHb.
  rewrite <-IHn.
  apply (inv (fun x=>h x c)).
  rewrite oadd_assoc; auto.
  apply inv.
  rewrite omult_n_add_comm; auto.
}
intro a.
apply H.
Qed.

(* h_{ω^b}(n)=f_b(n) 给出了FGH和HH间精确的换算 *)
Theorem h_ωpow(a:On): forall n, h (ωpow a) n = f a n.
intro n.
pose proof (h_add_ωpow Zero a n).
rewrite oadd_0_x in H; auto.
Qed.


(* h_{a+m}(n)=h_a(n+m) *)
Lemma h_add_n (a:On)(m:nat): forall n, h (oadd a m) n = h a (n+m).
induction m; cbn; auto.
intro n.
rewrite (IHm (S n)).
apply inv.
rewrite (Nat.add_comm n (S m)).
cbn.
apply inv,Nat.add_comm.
Qed.

(* h_m(n)=m+n *)
Lemma h_nat (m:nat): forall n, h m n = m + n.
intro n.
assert (h m n = h (oadd 0 m) n). {
  apply (inv (fun x=>h x _)),eq_sym,oadd_0_x.
  auto.
}
rewrite H,h_add_n.
cbn.
apply Nat.add_comm.
Qed.

(* h_ω(n)=n*2 *)
Lemma h_ω n: h ω n = n*2.
rewrite mult_n_2.
unfold h,ω.
apply h_nat.
Qed.

(* h_{ω*m}(n)=n*2^m *)
Lemma h_ωn (m n:nat): h (omult ω m) n = n*2^m.
generalize dependent n.
induction m; intro n; cbn.
- rewrite Nat.mul_comm. cbn. auto.
- rewrite h_add_n,IHm.
  rewrite (Nat.add_comm _ 0). cbn.
  rewrite <-mult_n_2,<-mult_n_2,(Nat.mul_comm (2^m) 2),Nat.mul_assoc.
  apply eq_refl.
Qed.


End WithFuncExt.
End HH.
