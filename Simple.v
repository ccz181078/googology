Require Import Ordinal.

(* 一些比较弱的著名记号，主要从大数入门.pdf中选取 *)

(* 阶乘 *)
Fixpoint fac(n:nat) :=
match n with
| O => 1
| S n' => n*(fac n')
end.

Compute (List fac 5).


(* 乘方 *)
Fixpoint pow(a b:nat) :=
match b with
| O => 1
| S b' => a*(pow a b')
end.

Compute (List (pow 2) 5).
Compute (List (pow 3) 5).


(* 阿克曼函数 *)
Fixpoint Ack(m:nat):nat->nat :=
match m with
| O => S
| S m' => fun n=>iter (Ack m') n (Ack m' 1)
end.

Compute (List (Ack 0) 4).
Compute (List (Ack 1) 4).
Compute (List (Ack 2) 4).
Compute (List (Ack 3) 4).
Compute (List (Ack 4) 0).


(* 高德纳箭头 *)
Fixpoint arrow(a n b:nat) :=
match n with
| O => O
| S O => pow a b
| S n' => iter (arrow a n') (b-1) a
end.

Compute (List (arrow 2 1) 4).
Compute (List (arrow 2 2) 4).


(* 葛立恒数 *)
Fixpoint G(n:nat) :=
match n with
| O => 4
| S n' => arrow (G n') 3 3
end.

Definition G64 := G 64.


(* 康威链 *)
(**
  a,b = a^b
  X,1,Y = X
  X,a+1,b+1 = X,(X,a,b+1),b
  大写字母表示自然数构成的序列，小写字母表示自然数
**)

(* 可以从 F0=X 和 F1(a)=X,a 构造 chain_suc(F0,F1,a,b)=X,a,b *)
Fixpoint chain_suc(F0:nat)(F1:nat->nat)(a b:nat):nat :=
match a,b with
| 1,_ => F0
| _,1 => F1 a
| (S a'),(S b') => iter (fun x=>chain_suc F0 F1 x b') a' F0
| _,_ => O
end.

(* 根据 F0=X、F1(a)=X,a、ls=Y 递归计算 X,a,Y *)
Fixpoint chain' (F0:nat)(F1:nat->nat)(ls:list nat):nat :=
match ls with
| nil => F0
| cons a b =>
  match b with
  | nil => F1 a
  | _ => chain' (F1 a) (chain_suc F0 F1 a) b
  end
end.

(* 计算康威链 *)
Definition chain(ls:list nat) :=
match ls with
| nil => 1
| cons a bs => chain' a (pow a) bs
end.

Compute (chain (17::nil)).
Compute (chain (2::3::nil)).
Compute (chain (3::2::nil)).
Compute (chain (2::3::2::nil)).
Compute (arrow 2 2 3).

(* 将a重复b次的列表 *)
Fixpoint repeat_list(a b:nat): list nat :=
match b with
| O => nil
| S b' => cons a (repeat_list a b')
end.

(* 康威链的下标扩展 *)
Fixpoint chain_ex(n:nat)(ls:list nat):nat :=
match ls with
| nil => 1
| cons a bs =>
  match n with
  | 0 => O
  | 1 => chain' a (pow a) bs
  | S n' => chain' a (fun b=>chain_ex n' (repeat_list a (S b))) bs
  end
end.

Goal chain_ex 1 = chain.
split.
Qed.
