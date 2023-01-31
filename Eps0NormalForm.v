Require Import Ordinal.
Require Import OrdArith.
Require Import OrdIterFixpoint.
Require Import Coq.Strings.String.


Module Eps0NF.

(*
前面给出的On的元素是基于基本列递归定义的序数记号，这使得我们能统一讨论每种序数记号的基本列并混用各种记号，但也导致不方便讨论序数记号本身的结构
这里给出用统一格式的表达式表示的一定范围内的序数的一种方式；这样的表示方式更接近大数学中常用的表示方式
*)


(* 将类型T的序数记号展开一层 *)
Inductive ExprFS{T:Set}:Set :=
| ZeroE
| SucE(n:T)
| LimE(f:nat->T).

(* 命题：T到On的映射保持基本列的定义 *)
Definition toOn_FS{T:Set}(toOn:T->On)(toFS:T->ExprFS) :=
forall x:T, (toOn x) = 
match (toFS x) with
| ZeroE => Zero
| SucE n0 => Suc (toOn n0)
| LimE f0 => Lim (fun n=>toOn (f0 n))
end.




(* 形如0或ω^a+b的表达式，用于表示ε0以内的序数 *)
Inductive Expr: Set :=
| expr0
| ωpowadd(a b:Expr).

(* 表达式对应的序数 *)
Fixpoint toOn(x:Expr) :=
match x with
| expr0 => Zero
| ωpowadd a b => oadd (ωpow (toOn a)) (toOn b)
end.

(* ω^表达式 *)
Definition ωpowE(x:Expr):Expr := 
ωpowadd x expr0.

(* ω^表达式*n *)
Fixpoint ωpowmulE(x:Expr)(n:nat):=
match n with
| O => expr0
| S n' => ωpowadd x (ωpowmulE x n')
end.




(*
w^0+0 = 0+1
w^(a+1)+0[n] = w^a*n
w^a+0[n] = w^(a[n]), a is Lim
w^a+(b+1) = (w^a+b)+1
(w^a+b)[n] = w^a+(b[n]), b is Lim
*)

(* 表达式的基本列 *)
Fixpoint toFS(x:Expr):ExprFS :=
match x with
| expr0 => ZeroE
| ωpowadd a b =>
  match (toFS b) with
  | ZeroE =>
    match (toFS a) with
    | ZeroE => SucE expr0
    | SucE n0 => LimE (fun n=>ωpowmulE n0 n)
    | LimE f0 => LimE (fun n=>ωpowE (f0 n))
    end
  | SucE n0 => SucE (ωpowadd a n0)
  | LimE f0 => LimE (fun n=>ωpowadd a (f0 n))
  end
end.



Section WithFuncExt.
(* 为了方便，引入函数外延公理 *)
Hypothesis func_ext : forall {A B: Type} {f g : A->B},
  (forall x, f x = g x) -> f = g.

(* 证明ω^x*n的定义和对应的序数兼容 *)
Lemma toOn_ωpowmulE: forall x n, toOn (ωpowmulE x n) = omult (opower ω (toOn x)) n.
intros x n.
induction n; auto.
simpl.
rewrite IHn.
generalize (toOn x). intro o.
rewrite omult_n_add_comm; auto.
Qed.

(* 证明ω^x的定义和对应的序数兼容 *)
Lemma toOn_ωpowE: forall x, toOn (ωpowE x) = ωpow (toOn x).
auto.
Qed.

(* 证明基本列的定义和对应的序数兼容 *)
Lemma Expr_toOn_FS: toOn_FS toOn toFS.
unfold toOn_FS.
intro x.
induction x; auto.
simpl.
induction (toFS x2); rewrite IHx2; auto.
simpl.
rewrite IHx1.
destruct (toFS x1); auto.
cbn.
apply inv.
unfold ωpow.
apply func_ext.
intro x.
rewrite <-(toOn_ωpowmulE n x).
apply eq_refl.
Qed.

(* repr(w)表示这种表达式能表示w和w的基本列递归展开出的所有序数 *)
Definition repr(w:On):= forall ls, exists e, toOn e = FSs w ls.

(* 证明如果x能表示，那么x的基本列递归展开的序数都能表示 *)
Lemma repr_trans e ls : exists e', (toOn e') = FSs (toOn e) ls.
intros.
induction ls; cbn.
- exists e; auto.
- destruct IHls as [x H].
  rewrite <-H.
  rewrite Expr_toOn_FS.
  unfold FS.
  destruct (toFS x).
  1: exists expr0.
  2: exists n.
  3: exists (f a).
  all: auto.
Qed.

(* 证明如果x能表示，则ω^x也能表示 *)
Lemma repr_ωpow: (forall x, repr x -> repr (ωpow x)).
unfold repr.
intros.
destruct (H nil).
cbn in H0.
rewrite <-H0.
rewrite <-toOn_ωpowE.
apply repr_trans.
Qed.

(* 证明ε0展开出的序数都能用这种表达式表示 *)
Theorem repr_ε0: forall n, repr (FS ε_0 n).
unfold repr.
intro n.
induction n; cbn.
- intros.
  apply (repr_trans expr0 ls).
- intros.
  cbn in IHn.
  apply repr_ωpow.
  unfold repr.
  apply IHn.
Qed.

End WithFuncExt.


(* 有了序数表达式，我们可以定义把自然数代入表达式中每个ω处求值 *)
Definition subst_nat(x0:Expr)(n:nat):nat :=
(fix FIX x :=
match x with
| expr0 => O
| ωpowadd a b => plus (Nat.pow n (FIX a)) (FIX b)
end) x0.

(* 接下来证明这种求值方式恰好和SGH的行为对应 *)
Theorem subst_nat_eq_g: forall x n, subst_nat x n = g (toOn x) n.
intro x.
induction x; auto.
intro n.
cbn.
rewrite g_oadd,g_ωpow.
rewrite <-IHx1,<-IHx2.
auto.
Qed.


Module Str.

Local Open Scope string_scope.

(* 用括号序列可以简洁地展示ω^a+b形式的表达式 *)
Fixpoint to_string(x:Expr): string :=
match x with
| expr0 => ""
| ωpowadd a b => "(" ++ (to_string a) ++ ")" ++ (to_string b)
end.

Goal
(to_string expr0)="" /\
(to_string (ωpowadd expr0 expr0))="()" /\
(to_string (ωpowadd expr0 (ωpowadd expr0 expr0)))="()()" /\
(to_string (ωpowadd (ωpowadd expr0 expr0) expr0))="(())"
.
repeat split.
Qed.

Definition FS' (x:Expr) (n:nat) :=
match (toFS x) with
| ZeroE => expr0
| SucE n0 => n0
| LimE f0 => f0 n
end.

Goal
(to_string (expr0))="" /\
(to_string (ωpowE expr0))="()" /\
(to_string (iter ωpowE 2 expr0))="(())" /\
(to_string (iter ωpowE 3 expr0))="((()))" /\
(to_string (iter ωpowE 4 expr0))="(((())))" /\
(to_string (FS' (iter ωpowE 4 expr0) 0))="(())" /\
(to_string (FS' (iter ωpowE 4 expr0) 1))="((()))" /\
(to_string (FS' (iter ωpowE 4 expr0) 2))="((()()))" /\
(to_string (FS' (iter ωpowE 4 expr0) 3))="((()()()))" /\
(to_string (FS' (FS' (iter ωpowE 4 expr0) 3) 1))="((()()))" /\
(to_string (FS' (FS' (iter ωpowE 4 expr0) 3) 2))="((()())(()()))" /\
(to_string (FS' (FS' (iter ωpowE 4 expr0) 3) 3))="((()())(()())(()()))" /\
(to_string (iter (fun x=>FS' x 3) 3 (iter ωpowE 4 expr0)))="((()())(()())(())(())(()))" /\
(to_string (iter (fun x=>FS' x 3) 4 (iter ωpowE 4 expr0)))="((()())(()())(())(())()()())" /\
True.
repeat split.
Qed.

End Str.


End Eps0NF.
