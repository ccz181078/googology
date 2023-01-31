
(* 序数的简化定义 *)
Inductive On := 
| Zero (* 零序数 *)
| Suc(n:On) (* 后继序数 *)
| Lim(f:nat->On) (* 极限序数 *)
.

(* 定义序数的基本列 *)
Definition FS(a:On)(n:nat):On :=
match a with
| Zero => Zero
| Suc a0 => a0
| Lim f => (f n)
end.

(* f迭代n次，以m为输入 *)
Definition iter{T} :=
fix FIX(f:T->T)(n:nat)(m:T) :=
match n with
| O => m
| S x => f (FIX f x m)
end.


(* FGH *)
Fixpoint f(x:On)(n:nat) :=
match x with
| Zero => S n
| Suc x0 => iter (f x0) n n
| Lim f0 => f (f0 n) n
end.

(* SGH *)
Fixpoint g(x:On)(n:nat) :=
match x with
| Zero => O
| Suc x0 => S (g x0 n)
| Lim f0 => g (f0 n) n
end.

(* HH *)
Fixpoint h(x:On)(n:nat) :=
match x with
| Zero => n
| Suc x0 => h x0 (S n)
| Lim f0 => h (f0 n) n
end.

(* MGH *)
Fixpoint m(x:On)(n:nat) :=
match x with
| Zero => S n
| Suc x0 => m x0 (m x0 n)
| Lim f0 => m (f0 n) n
end.

(* 每个自然数都对应一个序数 *)
Fixpoint ω_(n:nat):On :=
match n with
| O => Zero
| S n0 => Suc (ω_ n0)
end.

(* 为了方便，将自然数视为序数 *)
Coercion ω_ : nat >-> On.

(* 第一个极限序数 *)
Definition ω := Lim ω_.

(* 序数加法 *)
Fixpoint oadd(a b:On) :=
match b with
| Zero => a
| Suc b0 => Suc (oadd a b0)
| Lim f => Lim (fun n=>oadd a (f n))
end.

(* 序数乘法 *)
Fixpoint omult(a b:On) :=
match b with
| Zero => Zero
| Suc b0 => oadd (omult a b0) a
| Lim f => Lim (fun n=>omult a (f n))
end.

(* 序数乘方 *)
Fixpoint opower(a b:On) :=
match b with
| Zero => Suc Zero
| Suc b0 => omult (opower a b0) a
| Lim f => Lim (fun n=>opower a (f n))
end.

(* 用于输出函数值的前几项 *)
Fixpoint List(f:nat->nat)(n:nat):(list nat) :=
match n with
| O => (f O) :: nil
| S x => (List f x) ++ ((f n) :: nil)
end.

(* f,g,h的求值的例子 *)
Compute (List (g 0) 4). (* 0 *)
Compute (List (g 1) 4). (* 1 *)
Compute (List (g 2) 4). (* 2 *)
Compute (List (g 3) 4). (* 3 *)
Compute (List (g ω) 4). (* n *)
Compute (List (g (oadd ω 1)) 4). (* n+1 *)
Compute (List (g (oadd ω 5)) 4). (* n+5 *)
Compute (List (g (oadd ω ω)) 4). (* n+n *)
Compute (List (g (omult ω 2)) 4). (* n*2 *)
Compute (List (g (opower ω 2)) 4). (* n^2 *)
Compute (List (g (opower ω ω)) 4). (* n^n *)
Compute (List (g (opower ω (opower ω ω))) 2). (* n^n^n *)

Compute (List (f 0) 4).
Compute (List (f 1) 4).
Compute (List (f 2) 4).
Compute (List (f 3) 2).
Compute (List (f ω) 2).

Compute (List (h 0) 4). 
Compute (List (h 1) 4).
Compute (List (h 2) 4).
Compute (List (h 3) 4).
Compute (List (h ω) 4).
Compute (List (h (oadd ω 1)) 4).
Compute (List (h (oadd ω 5)) 4).
Compute (List (h (omult ω 2)) 4).
Compute (List (h (omult ω 3)) 4).
Compute (List (h (omult ω ω)) 4).

(* 按照序数x的结构进行递归，使用给定的初值O'和后继运算S'，构造新序数 *)
Fixpoint oiter(O':On)(S':On->On)(x:On):On :=
match x with
| Zero => O'
| Suc x0 => S' (oiter O' S' x0)
| Lim f => Lim (fun n=>oiter O' S' (f n))
end.

Section CheckEq.

(* 为了方便，引入函数外延公理 *)
Hypothesis func_ext : forall {A B: Type} {f g : A->B},
  (forall x, f x = g x) -> f = g.

(* 容易验证，序数加法可以用oiter定义，后继操作是取后继序数 *)
Goal forall a b, (oadd a b) = (oiter a Suc b).
intros a b.
induction b.
- simpl. apply eq_refl.
- simpl. rewrite IHb. apply eq_refl.
- simpl. rewrite (func_ext H). apply eq_refl.
Qed.

(* 容易验证，序数乘法可以用oiter定义，后继操作是加a *)
Goal forall a b, (omult a b) = (oiter Zero (fun t=>oadd t a) b).
intros a b.
induction b.
- simpl. apply eq_refl.
- simpl. rewrite IHb. apply eq_refl.
- simpl. rewrite (func_ext H). apply eq_refl.
Qed.

(* 容易验证，序数乘方可以用G定义，后继操作是乘a *)
Goal forall a b, (opower a b) = (oiter (Suc Zero) (fun t=>omult t a) b).
intros a b.
induction b.
- simpl. apply eq_refl.
- simpl. rewrite IHb. apply eq_refl.
- simpl. rewrite (func_ext H). apply eq_refl.
Qed.

End CheckEq.


Definition ωpow := opower ω.


(* 定义序数连续取基本列 *)
Fixpoint FSs(a:On)(n:list nat):On :=
match n with
| nil => a
| cons h t => FS (FSs a t) h
end.


(* 辅助化简 *)
Lemma inv{A B:Type} : forall (f:A->B) x1 x2, x1=x2 -> f x1 = f x2.
intros.
rewrite H.
apply eq_refl.
Qed.



