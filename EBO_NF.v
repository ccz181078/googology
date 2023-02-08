Require Import Ordinal.

Module EBO_NF.

(* 表达式，E0表示0，P a b 表示 ψ_a(b) *)
Inductive Expr: Set :=
| E0
| P(a b:Expr).

Scheme Equality for Expr.

(* 小于 *)
Fixpoint lt(a b:Expr):bool :=
match a,b with
| E0,E0 => false
| E0,P _ _ => true
| P _ _,E0 => false
| P a1 a2,P b1 b2 =>
  (lt a1 b1) || (Expr_beq a1 b1) && (lt a2 b2)
end.

(* 基本列的分类 *)
Inductive FSType :=
| Zero'
| Suc'(x:Expr)
| Limω(f:nat->Expr)
| LimΩ(cf:Expr)(f:Expr->Expr).

(*
Extended Weak Buchholz's OCF的一种基本列
参考：https://googology.fandom.com/wiki/Extended_Weak_Buchholz%27s_function
*)
Fixpoint ExprFS(x:Expr):FSType :=
match x with
| E0 => Zero'
| P a b =>
  match (ExprFS b) with
  | Zero' =>
    match (ExprFS a) with
    | Zero' => Suc' E0                     (* ψ_0(0)=0+1 *)
    | Suc' x => (LimΩ x (fun n=>n))        (* ψ_{x+1}(0)[n] = n, cf=ψ_{x+1}(0) *)
    | Limω f => (Limω (fun n=>P (f n) E0)) (* ψ_a(0)[n] = ψ_{a[n]}(0), cf(a)≥ω *)
    | LimΩ cf f => (LimΩ cf (fun n=>P (f n) E0))
    end
  | Suc' x => Suc' (P a x) (* ψ_a(b)[n]=ψ_a(b[n]), 1≤cf(b)<ψ_{a+1}(0) *)
  | Limω f => Limω (fun n=>P a (f n))
  | LimΩ cf f =>
    if (lt cf a)
      then LimΩ cf (fun n=>P a (f n))
      else Limω (fun n=>P a (iter (fun w=>f (P cf w)) n E0))
      (* ψ_a(b)[n]=ψ_a(x=>b[ψ_c(x)]迭代n次), cf(b)=ψ_{c+1}(0)≥ψ_{a+1}(0) *)
  end
end.


Definition E1 := (P E0 E0).
Definition E2 := (P E0 E1).
Definition E3 := (P E0 E2).
Definition Eω := (P E0 (P E1 E0)).
Goal (ExprFS (P E0 E3)) = Suc' (P E0 E2).
split.
Qed.

Definition ExprFSω x n y :=
match (ExprFS x) with
| Limω f => (f n)=y
| _ => False
end.

Goal 
(ExprFS (P E0 E0)) = Suc' E0 /\
(ExprFS (P E0 (P E2 (P E0 (P E0 E0))))) = Suc' (P E0 (P E2 (P E0 E0))) /\
(ExprFSω Eω 0 E1) /\
(ExprFSω Eω 1 E2) /\
(ExprFSω Eω 2 E3) /\
(ExprFSω (P E0 (P E3 E0)) 0 (P E0 E0)) /\
(ExprFSω (P E0 (P E3 E0)) 1 (P E0 (P E2 E0))) /\
(ExprFSω (P E0 (P E3 E0)) 2 (P E0 (P E2 (P E2 E0)))) /\
(ExprFSω (P E0 (P E3 (P E2 E0))) 0 (P E0 E0)) /\
(ExprFSω (P E0 (P E3 (P E2 E0))) 1 (P E0 (P E3 (P E1 E0)))) /\
(ExprFSω (P E0 (P E3 (P E2 E0))) 2 (P E0 (P E3 (P E1 (P E3 (P E1 E0)))))) /\
(ExprFSω (P E0 (P E3 (P E3 E0))) 0 (P E0 E0)) /\
(ExprFSω (P E0 (P E3 (P E3 E0))) 1 (P E0 (P E3 (P E2 E0)))) /\
(ExprFSω (P E0 (P E3 (P E3 E0))) 2 (P E0 (P E3 (P E2 (P E3 (P E2 E0)))))) /\
(ExprFSω (P E0 (P E3 (P E2 (P E1 E0)))) 2 (P E0 (P E3 (P E2 (P E0 (P E3 (P E2 (P E0 E0)))))))) /\
(ExprFSω (P E0 (P Eω E0)) 0 (P E0 (P E1 E0))) /\
(ExprFSω (P E0 (P Eω E0)) 1 (P E0 (P E2 E0))) /\
(ExprFSω (P E0 (P Eω E0)) 2 (P E0 (P E3 E0))) /\
(ExprFSω (P E0 (P (P Eω E0) E0)) 2 (P E0 (P (P E3 E0) E0))) /\
(ExprFSω (P E0 (P (P E2 E0) E0)) 2 (P E0 (P (P E1 (P (P E1 E0) E0)) E0))) /\
True
.
repeat split.
Qed.



Definition LT a b := (lt a b)=true.

(* C(a,b,x) 表示若a,b是标准项则x是标准项且x∈C_a(b), NF(a)表示a是标准项 *)
Inductive C: Expr->Expr->Expr->Prop :=
| C_0: forall a b, C a b E0
| C_P: forall a b x y,
  NF (P x y) ->
  (LT (P x y) (P a E0) \/ (C a b x /\ C a b y /\ LT y b)) ->
  C a b (P x y)

with NF: Expr->Prop :=
| NF_0: NF E0
| NF_P: forall x y, NF x -> NF y -> C x y y -> NF (P x y).

Scheme C_mind := Induction for C Sort Prop
  with NF_mind := Induction for NF Sort Prop.

(* 判断标准项的程序 *)
Fixpoint Cb(a b w:Expr):bool :=
match w with
| E0 => true
| P x y =>
  (NFb x) && (NFb y) && (Cb x y y) &&
  ((lt (P x y) (P a E0)) ||
   (Cb a b x) && (Cb a b y) && (lt y b))
end

with NFb(w:Expr):bool :=
match w with
| E0 => true
| P a b => (NFb a) && (NFb b) && (Cb a b b)
end.

(* 标准项的例子 *)
Goal
(NFb E0)=true /\
(NFb (P E0 E0))=true /\
(NFb (P (P (P E0 E0) E0) (P E0 E0)))=true /\
(NFb (P E0 (P E2 E0)))=true /\
(NFb (P E0 (P E3 E0)))=true /\
(NFb (P E0 (P E3 (P E3 E0))))=true /\
(NFb (P E0 (P E3 (P E2 E0))))=true /\
(NFb (P E0 (P E2 (P E1 (P E2 E0)))))=true /\
(NFb (P E0 (P (P E1 E0) (P E1 (P E3 E0)))))=true /\
(NFb (P E0 (P E1 (P E2 E0))))=false /\
(NFb (P E0 (P E2 (P E1 (P E3 E0)))))=false /\
True.
unfold E3,E2,E1.
repeat split.
Qed.


End EBO_NF.
