Require Import Ordinal.
Require Import OrdIterFixpoint.

(* 
ε_0内的序数都可以递归写成0或ω^a+b
Madore's OCF引入一个充分大的序数Ω满足Ω[n]=n，将大的序数写为Ω^a*b+c，其中b是普通序数，a,c是大的序数，再用函数ψ将大的序数映射为普通序数
类似于ω^(a+1)[n]=ω^a*n，Ω^(a+1)[η]=Ω^a*η，这允许我们进行更强的迭代
Madore's OCF的集合定义和这里用到的基本列构造可以参考https://googology.fandom.com/wiki/Madore's_function
 *)

(* 引入Ω后的序数类型，基本列可以更复杂 *)
Inductive On' : Set :=
| Zero'
| Suc'(a:On')
| LimΩ(g:On->On')
| Limω(g:nat->On').

(* 引入Ω后的序数加法 *)
Fixpoint oadd' (a b:On'):On' :=
match b with
| Zero' => a
| Suc' b0 => Suc' (oadd' a b0)
| LimΩ g => LimΩ (fun η=>oadd' a (g η))
| Limω g => Limω (fun n=>oadd' a (g n))
end.

(* 接下来讨论Ω^a*b，其中a:On', b:On *)
(* Ω^(a+1)*(b+1) [n] = Ω^(a+1)*b + Ω^a*n *)
Fixpoint Ωpm_suc(F:On->On')(b:On):On' :=
match b with
| Zero => Zero'
| Suc b0 => LimΩ (fun η=>oadd' (Ωpm_suc F b0) (F η))
| Lim f0 => Limω (fun n=>Ωpm_suc F (f0 n))
end.

(* Ω^a*(b+1) [n] = Ω^a*b + Ω^(a[n]), cf(a)≥ω *)
Fixpoint Ωpm_limΩ(F:On->On->On')(b:On):On' :=
match b with
| Zero => Zero'
| Suc b0 => LimΩ (fun η=>oadd' (Ωpm_limΩ F b0) (F η 1))
| Lim f0 => Limω (fun n=>Ωpm_limΩ F (f0 n))
end.

Fixpoint Ωpm_limω(F:nat->On->On')(b:On):On' :=
match b with
| Zero => Zero'
| Suc b0 => Limω (fun n=>oadd' (Ωpm_limω F b0) (F n 1))
| Lim f0 => Limω (fun n=>Ωpm_limω F (f0 n))
end.

(* Ω^0*(b+1) = (Ω^0*b) + 1 *)
Fixpoint Ωpm_0(b:On):On' :=
match b with
| Zero => Zero'
| Suc b0 => Suc' (Ωpm_0 b0)
| Lim f0 => Limω (fun n=>Ωpm_0 (f0 n))
end.

(* Ωpm(a,b) = Ω^a*b *)
Fixpoint Ωpm (a:On'):On->On' :=
match a with
| Zero' => Ωpm_0
| Suc' a' => Ωpm_suc (Ωpm a')
| LimΩ g => Ωpm_limΩ (fun η=>Ωpm (g η))
| Limω g => Ωpm_limω (fun n=>Ωpm (g n))
end.

(* Madore's OCF *)
Fixpoint ψ(x:On'):On :=
match x with
| Zero' => ε_0
| Suc' x0 => ε_suc (ψ x0)
| LimΩ g => iter_lim (fun a=>ψ (g a)) 1
| Limω g => Lim (fun n=>ψ (g n))
end.

Definition Ωpow := fun x=>Ωpm x 1.

Definition BHO := ψ (Limω (fun n=>iter Ωpow n Zero')).
