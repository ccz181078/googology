Require Import Ordinal.

(*
Madore's OCF引入了序数加乘幂和一个Ω，可以继续引入更多的Ω和相应的ψ来提升强度
Weak Buchholz's OCF 是最简单的引入了ω个Ω的OCF之一，不需要支持额外的序数运算，可以作为例子说明如何引入多个Ω和相应的ψ
Buchholz's OCF和Weak版本类似，但引入了序数加法来提升强度
这里给出的定义和原始定义不完全等价，但整体是类似的，极限也相同
这里的定义同构于BMS在1行和2行时的特例
Buchholz's OCF的基本列定义可以参考https://googology.fandom.com/wiki/List_of_systems_of_fundamental_sequences
BMS的定义可以参考https://googology.fandom.com/wiki/Bashicu_matrix_system
证明3行和以上的BMS的停机性比较困难
*)

Module Example1.

(* 引入Ω得到多个序数类型 *)

Inductive On1 : Set :=
| Zero_1
| Suc_1(a:On1)
| Limω_1(g:nat->On1)
| LimΩ1_1(g:On->On1).

Inductive On2 : Set :=
| Zero_2
| Suc_2(a:On2)
| Limω_2(g:nat->On2)
| LimΩ1_2(g:On->On2)
| LimΩ2_2(g:On1->On2).

Inductive On3 : Set :=
| Zero_3
| Suc_3(a:On3)
| Limω_3(g:nat->On3)
| LimΩ1_3(g:On->On3)
| LimΩ2_3(g:On1->On3)
| LimΩ3_3(g:On2->On3).

(* Ω的基本列是恒等映射，顺便给出了将小的序数类型嵌入大的序数类型的方式 *)

Fixpoint Up1 x :=
match x with
| Zero => Zero_1
| Suc x0 => Suc_1 (Up1 x0)
| Lim f0 => Limω_1 (fun n=>Up1 (f0 n))
end.

Fixpoint Up2 x :=
match x with
| Zero_1 => Zero_2
| Suc_1 x0 => Suc_2 (Up2 x0)
| Limω_1 f0 => Limω_2 (fun n=>Up2 (f0 n))
| LimΩ1_1 f0 => LimΩ1_2 (fun n=>Up2 (f0 n))
end.

Fixpoint Up3 x :=
match x with
| Zero_2 => Zero_3
| Suc_2 x0 => Suc_3 (Up3 x0)
| Limω_2 f0 => Limω_3 (fun n=>Up3 (f0 n))
| LimΩ1_2 f0 => LimΩ1_3 (fun n=>Up3 (f0 n))
| LimΩ2_2 f0 => LimΩ2_3 (fun n=>Up3 (f0 n))
end.

Definition Ω1 : On1 := LimΩ1_1 Up1.
Definition Ω2 : On2 := LimΩ2_2 Up2.
Definition Ω3 : On3 := LimΩ3_3 Up3.


Module Weak.
(* Weak Buchholz's OCF 的一部分 *)
Fixpoint ψ0(x:On1):On :=
match x with
| Zero_1 => 1
| Suc_1 x0 => Suc (ψ0 x0)
| Limω_1 f0 => Lim (fun n=>ψ0 (f0 n))
| LimΩ1_1 f0 => Lim (fun m=>(iter (fun n=>ψ0 (f0 n)) m Zero))
end.

Fixpoint ψ1(x:On2):On1 :=
match x with
| Zero_2 => Ω1
| Suc_2 x0 => Suc_1 (ψ1 x0)
| Limω_2 f0 => Limω_1 (fun n=>ψ1 (f0 n))
| LimΩ1_2 f0 => LimΩ1_1 (fun n=>ψ1 (f0 n))
| LimΩ2_2 f0 => Limω_1 (fun m=>(iter (fun n=>ψ1 (f0 n)) m Zero_1))
end.

Fixpoint ψ2(x:On3):On2 :=
match x with
| Zero_3 => Ω2
| Suc_3 x0 => Suc_2 (ψ2 x0)
| Limω_3 f0 => Limω_2 (fun n=>ψ2 (f0 n))
| LimΩ1_3 f0 => LimΩ1_2 (fun n=>ψ2 (f0 n))
| LimΩ2_3 f0 => LimΩ2_2 (fun n=>ψ2 (f0 n))
| LimΩ3_3 f0 => Limω_2 (fun m=>(iter (fun n=>ψ2 (f0 n)) m Zero_2))
end.

Compute (List (g (ψ0 (Ω1))) 4). (* n *)
Compute (List (g (ψ0 (ψ1 Ω2))) 4). (* n^n *)
Compute (List (g (ψ0 (ψ1 (ψ2 Ω3)))) 2). (* n^n^n *)
(* Weak BOCF 的极限是ε_0 *)
End Weak.

Module Normal.

(* 序数加法 *)
Fixpoint oadd_1(a b:On1):On1 :=
match b with
| Zero_1 => a
| Suc_1 b0 => Suc_1 (oadd_1 a b0)
| Limω_1 f0 => Limω_1 (fun n=>oadd_1 a (f0 n))
| LimΩ1_1 f0 => LimΩ1_1 (fun n=>oadd_1 a (f0 n))
end.

Fixpoint oadd_2(a b:On2):On2 :=
match b with
| Zero_2 => a
| Suc_2 b0 => Suc_2 (oadd_2 a b0)
| Limω_2 f0 => Limω_2 (fun n=>oadd_2 a (f0 n))
| LimΩ1_2 f0 => LimΩ1_2 (fun n=>oadd_2 a (f0 n))
| LimΩ2_2 f0 => LimΩ2_2 (fun n=>oadd_2 a (f0 n))
end.

(* 序数乘自然数 *)
Definition omult_1(a:On1)(n:nat):On1 := iter (oadd_1 a) n Zero_1.
Definition omult_2(a:On2)(n:nat):On2 := iter (oadd_2 a) n Zero_2.

(* Buchholz's OCF 的一部分 *)
Fixpoint ψ0(x:On1):On :=
match x with
| Zero_1 => 1
| Suc_1 x0 => Lim (fun n=>omult (ψ0 x0) n)
| Limω_1 f0 => Lim (fun n=>ψ0 (f0 n))
| LimΩ1_1 f0 => Lim (fun m=>(iter (fun n=>ψ0 (f0 n)) m Zero))
end.

Fixpoint ψ1(x:On2):On1 :=
match x with
| Zero_2 => Ω1
| Suc_2 x0 => Limω_1 (fun n=>omult_1 (ψ1 x0) n)
| Limω_2 f0 => Limω_1 (fun n=>ψ1 (f0 n))
| LimΩ1_2 f0 => LimΩ1_1 (fun n=>ψ1 (f0 n))
| LimΩ2_2 f0 => Limω_1 (fun m=>(iter (fun n=>ψ1 (f0 n)) m Zero_1))
end.

Fixpoint ψ2(x:On3):On2 :=
match x with
| Zero_3 => Ω2
| Suc_3 x0 => Limω_2 (fun n=>(omult_2 (ψ2 x0) n))
| Limω_3 f0 => Limω_2 (fun n=>ψ2 (f0 n))
| LimΩ1_3 f0 => LimΩ1_2 (fun n=>ψ2 (f0 n))
| LimΩ2_3 f0 => LimΩ2_2 (fun n=>ψ2 (f0 n))
| LimΩ3_3 f0 => Limω_2 (fun m=>(iter (fun n=>ψ2 (f0 n)) m Zero_2))
end.


(* 验证一些简单性质 *)
Compute (List (g (ψ0 (Up1 (ψ0 Zero_1)))) 4). (* n *)
Compute (List (g (ψ0 (Up1 2))) 4). (* n^2 *)
Compute (List (g (ψ0 (Up1 3))) 4). (* n^3 *)
Compute (List (g (ψ0 (Up1 ω))) 4). (* n^n *)

Goal
(FS (ψ0 (ψ1 Zero_2)) 0) = Zero /\
(FS (ψ0 (ψ1 Zero_2)) 1) = (ψ0 Zero_1) /\
(FS (ψ0 (ψ1 Zero_2)) 2) = (ψ0 (Up1 (ψ0 Zero_1))) /\
(FS (ψ0 (ψ1 Zero_2)) 3) = (ψ0 (Up1 (ψ0 (Up1 (ψ0 Zero_1))))) /\

(FS (ψ0 (ψ1 (Up2 (ψ1 Zero_2)))) 0) = Zero /\
(FS (ψ0 (ψ1 (Up2 (ψ1 Zero_2)))) 1) = (ψ0 (ψ1 Zero_2)) /\
(FS (ψ0 (ψ1 (Up2 (ψ1 Zero_2)))) 2) = (ψ0 (ψ1 (Up2 (Up1 (ψ0 (ψ1 Zero_2)))))) /\

(FS (ψ0 (ψ1 (ψ2 Zero_3))) 1)=(ψ0 (ψ1 Zero_2)) /\
(FS (ψ0 (ψ1 (ψ2 Zero_3))) 2)=(ψ0 (ψ1 (Up2 (ψ1 Zero_2)))) /\
(FS (ψ0 (ψ1 (ψ2 Zero_3))) 3)=(ψ0 (ψ1 (Up2 (ψ1 (Up2 (ψ1 Zero_2)))))).
repeat split.
Qed.


End Normal.

End Example1.

(*
在序数类型X引入Ω得到On'
分类为0,a+1,cf=ω,ω<cf<Ω,cf=Ω
*)
Inductive On'{X:Set}{cf:X->Set} : Set :=
| Zero'
| Suc'(a:On')
| Limω(g:nat->On')
| LimX(x:X)(g:cf x->On')
| LimΩ (g:X->On').

(* 递推地给出cf(x)>ω时的cf(x) *)
Definition cf0(x:On):Set := unit.
Definition cf'{X:Set}{cf:X->Set}(x:@On' X cf): Set :=
match x with
| LimX x f0 => cf x
| LimΩ f0 => X
| _ => unit
end.

(* 将小的序数类型嵌入大的序数类型 *)
Definition Up1: On->@On' On cf0.
intro x.
induction x.
- apply Zero'.
- apply (Suc' IHx).
- apply (Limω H).
Defined.

Definition Up'{X:Set}{cf:X->Set}:
  (@On' X cf)->(@On' (@On' X cf) (@cf' X cf)).
intro x.
induction x.
- apply Zero'.
- apply (Suc' IHx).
- apply (Limω H).
- apply (LimX (LimX x g) H).
- apply (LimX (LimΩ g) H).
Defined.

(* 序数加法 *)
Definition oadd'{X:Set}{cf:X->Set}(a b:@On' X cf): @On' X cf.
induction b.
- apply a.
- apply (Suc' IHb).
- apply (Limω H).
- apply (LimX x H).
- apply (LimΩ H).
Defined.


Definition omult'{X:Set}{cf:X->Set}(a:@On' X cf)(n:nat):@On' X cf := iter (oadd' a) n Zero'.

(*
ψ(0)=Ω
ψ(a+1)[n]=ψ(a)*n
ψ(a)[n]=ψ(a[n]), ω≤cf(a)<Ω
ψ(a)[n+1]=ψ(a[ψ(a)[n]]), cf(a)=Ω, ψ(a)[0]=0
*)
Definition ψ'{X:Set}{cf:X->Set}{Ω:@On' X cf}: (@On' (@On' X cf) (@cf' X cf))->(@On' X cf).
intro x.
induction x.
- apply Ω.
- apply (Limω (omult' IHx)).
- apply (Limω H).
- destruct x eqn:E.
  + apply (H tt). (* 不可达 *)
  + apply (H tt). (* 不可达 *)
  + apply (H tt). (* 不可达 *)
  + apply (@LimX X cf x0 H).
  + apply (@LimΩ X cf H).
- apply (Limω (fun m=>(iter H m Zero'))).
Defined.

Definition ψ0 : (@On' On cf0)->On.
intro x.
induction x.
- apply (Suc Zero).
- apply (Lim (omult IHx)).
- apply (Lim H).
- apply Zero. (* 不可达 *)
- apply (Lim (fun m=>(iter H m Zero))).
Defined.

Structure Layer := {
  X: Set;
  cf: X->Set;
  Ω: @On' X cf;
  ψn: @On' X cf -> X;
  Up: X->@On' X cf;
  limit_n: On;
  limit_n_f: @On' X cf->On
}.


(* 递推出每层的序数类型、基本列类型、Ω,ψ,Up等 *)
Fixpoint Layer_at(n:nat) := match n with
| O => Build_Layer On cf0 (LimΩ Up1) ψ0 Up1 (ψ0 Zero') ψ0
| S n' => let a:=(Layer_at n') in
  let ψ:=(@ψ' (X a) (cf a) (Ω a)) in
  let l:=fun x=>(limit_n_f a (ψ x)) in
  Build_Layer (@On' (X a) (cf a)) (@cf' (X a) (cf a)) (LimΩ Up') ψ (Up') (l Zero') l
end.


(* Buchholz's OCF的极限 *)
Definition BO : On := Lim (fun n=>limit_n (Layer_at n)).


(* 定义一些特例方便测试 *)
Definition ψ1 := ψn (Layer_at 1).
Definition ψ2 := ψn (Layer_at 2).
Definition ψ3 := ψn (Layer_at 3).

Definition Up2 := Up (Layer_at 1).
Definition Up3 := Up (Layer_at 2).
Definition Up4 := Up (Layer_at 3).

(* 验证一些简单性质 *)
Compute (List (g (ψ0 (Up1 (ψ0 Zero')))) 4). (* n *)
Compute (List (g (ψ0 (Up1 2))) 4). (* n^2 *)
Compute (List (g (ψ0 (Up1 3))) 4). (* n^3 *)
Compute (List (g (ψ0 (Up1 ω))) 4). (* n^n *)

Goal
(FS (ψ0 (ψ1 Zero')) 0) = Zero /\
(FS (ψ0 (ψ1 Zero')) 1) = (ψ0 Zero') /\
(FS (ψ0 (ψ1 Zero')) 2) = (ψ0 (Up1 (ψ0 Zero'))) /\
(FS (ψ0 (ψ1 Zero')) 3) = (ψ0 (Up1 (ψ0 (Up1 (ψ0 Zero'))))) /\

(FS (ψ0 (ψ1 (Up2 (ψ1 Zero')))) 0) = Zero /\
(FS (ψ0 (ψ1 (Up2 (ψ1 Zero')))) 1) = (ψ0 (ψ1 Zero')) /\
(FS (ψ0 (ψ1 (Up2 (ψ1 Zero')))) 2) = (ψ0 (ψ1 (Up2 (Up1 (ψ0 (ψ1 Zero')))))) /\

(FS (ψ0 (ψ1 (ψ2 Zero'))) 1)=(ψ0 (ψ1 Zero')) /\
(FS (ψ0 (ψ1 (ψ2 Zero'))) 2)=(ψ0 (ψ1 (Up2 (ψ1 Zero')))) /\
(FS (ψ0 (ψ1 (ψ2 Zero'))) 3)=(ψ0 (ψ1 (Up2 (ψ1 (Up2 (ψ1 Zero')))))) /\

(FS (ψ0 (ψ1 (ψ2 (ψ3 (Up4 (Up3 (ψ2 (Up3 (ψ2 Zero'))))))))) 1)=(ψ0 (ψ1 (ψ2 (ψ3 (Up4 (Up3 (ψ2 Zero'))))))) /\
(FS (ψ0 (ψ1 (ψ2 (ψ3 (Up4 (Up3 (ψ2 (Up3 (ψ2 Zero'))))))))) 2)=(ψ0 (ψ1 (ψ2 (ψ3 (Up4 (Up3 (ψ2 (Up3 (Up2 (ψ1 (ψ2 (ψ3 (Up4 (Up3 (ψ2 Zero'))))))))))))))).
repeat split.
Qed.

