Require Import Ordinal.

(* 接下来给出与序数函数的不动点相关的构造：ε,ζ,η,二元φ,Γ,序数元φ *)


(* iter_lim(f,x) 表示 x, f(x), f(f(x)), ... 的极限 *)
Definition iter_lim(f:On->On)(x:On):On := Lim (fun n=>iter f n x).

(* f(0,x), f(1,x), ... 的极限 *)
Definition seq_lim(f:nat->On->On)(x:On):On := Lim (fun n=>f n x).

(* oiter_Suc(f,0), oiter_Suc(f,1), oiter_Suc(f,2), ... 可以用于枚举f(0), f(f(0)+1), f(f(f(0)+1)+1)... *)
Definition oiter_Suc(f:On->On)(x:On):On := oiter (f 0) (fun a=>(f (Suc a))) x.



(* 用序数乘方的迭代作为后继操作 *)
Definition ε_suc := iter_lim ωpow.

(* 序数乘方的不动点 *)
Definition ε_0 := ε_suc Zero.
Definition ε_1 := ε_suc (Suc ε_0).
Definition ε_2 := ε_suc (Suc ε_1).

(* 每个序数都对应序数乘方的不动点 *)
Definition ε:On->On := oiter_Suc ε_suc.


(* 用ε的迭代作为后继操作 *)
Definition ζ_suc := iter_lim ε.

(* ε的不动点 *)
Definition ζ_0 := ζ_suc Zero.
Definition ζ_1 := ζ_suc (Suc ζ_0).
Definition ζ_2 := ζ_suc (Suc ζ_1).

(* 每个序数都对应ε的不动点 *)
Definition ζ:On->On := oiter_Suc ζ_suc.


(* 用ζ的迭代作为后继操作 *)
Definition η_suc := iter_lim ζ.

(* ζ的不动点 *)
Definition η_0 := η_suc Zero.
Definition η_1 := η_suc (Suc η_0).
Definition η_2 := η_suc (Suc η_1).

(* 每个序数都对应ζ的不动点 *)
Definition η:On->On := oiter_Suc η_suc.


(* 重复上面的过程 *)
(* 用f的迭代作为后继操作 *)

(* f的前几个不动点 *)
Definition fixpoint_0(f:On->On):On := iter_lim f Zero.
Definition fixpoint_1(f:On->On):On := iter_lim f (Suc (fixpoint_0 f)).
Definition fixpoint_2(f:On->On):On := iter_lim f (Suc (fixpoint_1 f)).


(* 希望第一个f是ωpow，然后是ε,ζ,η,... *)
(* 二元φ函数 *)
Fixpoint φ(a:On):On->On :=
match a with
| Zero => ωpow
| Suc a0 => oiter_Suc (iter_lim (φ a0))
| Lim f => oiter_Suc (seq_lim (fun n=>(φ (f n))))
end.

(* 验证 φ(1,_)=ε(_) *)
Goal ωpow=(φ 0) /\ ε=(φ 1) /\ ζ=(φ 2) /\ η=(φ 3).
repeat split.
Qed.

(* Γ(x)=φ(1,0,x) *)
Definition Γ := oiter_Suc (iter_lim (fun x=>φ x 0)).



(* 以F为起点的二元φ函数 *)
Definition φ2(F:On->On):On->On->On :=
fix FIX(a:On):On->On :=
match a with
| Zero => F
| Suc a0 => oiter_Suc (iter_lim (FIX a0))
| Lim f => oiter_Suc (seq_lim (fun n=>(FIX (f n))))
end.

(* 以F为起点的三元φ函数 φ(x,y,z) *)
Definition φ3(F:On->On):On->On->On->On :=
fix FIX(a:On):On->On->On :=
match a with
| Zero => φ2 F
| Suc a0 => φ2 (oiter_Suc (iter_lim (fun x=>FIX a0 x 0)))
| Lim f => φ2 (oiter_Suc (seq_lim (fun n x=>FIX (f n) x 0)))
end.

(* 以F为起点的四元φ函数 φ(a,b,c,d) *)
Definition φ4(F:On->On):On->On->On->On->On :=
fix FIX(a:On):On->On->On->On :=
match a with
| Zero => φ3 F
| Suc a0 => φ3 (oiter_Suc (iter_lim (fun x=>FIX a0 x 0 0)))
| Lim f => φ3 (oiter_Suc (seq_lim (fun n x=>FIX (f n) x 0 0)))
end.

(* 验证和前面的定义的相容性 *)
Goal (φ2 ωpow)=φ /\ (φ3 ωpow 0)=φ /\ (φ4 ωpow 0 0)=φ /\ (φ3 ωpow 1 0)=Γ.
repeat split.
Qed.


(* φn_suc用于将n元φ函数变为n+1元 *)
(* φ(xxx, 0, 0...0, y) 由递归时传入的表示起点的F决定 *)
(* φ(xxx, a+1, 0...0, y) = x→φ(xxx, a, x, 0...0) 的第y个不动点 *)
(* φ(xxx, a, 0...0, y) = x→sup φ(xxx, a[n], x, 0...0) 迭代1+y次 *)
Definition φn_suc{T}(prev:((On->On)->On->T->On)*T):((On->On)->On->(On*T)->On)*(On*T) :=
let (φn,T0):=prev in
let f0 :=
  fun (F:On->On) =>
  fix FIX(a:On):On->T->On :=
  match a with
  | Zero => φn F
  | Suc a0 => φn (oiter_Suc (iter_lim (fun x=>FIX a0 x T0)))
  | Lim f => φn (oiter_Suc (seq_lim (fun n x=>FIX (f n) x T0)))
  end
in (
  (fun (F:On->On) (a:On) (b:On*T) => let (b1,b2):=b in f0 F a b1 b2),
  (Zero,T0)
).

Definition φ1' := (fun (f:On->On)(x:On)(y:True) => f x, I).
Definition φ2' := (φn_suc φ1').
Definition φ3' := (φn_suc φ2').
Definition φ4' := (φn_suc φ3').

Inductive ex_Set (A : Set) (P : A -> Set) : Set :=
| existSet(x:A)(y:P x) : ex_Set A P.

(* φn_lim用于对一列参数列表长度不同的φ函数进行对角化操作 *)
(* φ(xxx, (a+1)@b, y@0) = x→sup φ(xxx, a@b, x@b[n]) 迭代1+y次，b为极限序数 *)
(* φ(xxx, a@b, y@0) = x→sup φ(xxx, a[n]@b, x@b[n]) 迭代1+y次，a,b为极限序数 *)
Definition φn_lim{T:nat->Set} (prev:forall n:nat, let Tn := T n in ((On->On)->On->Tn->On)*Tn)
  :let Tn := (ex_Set nat T) in ((On->On)->On->(On*Tn)->On)*(On*Tn)
 :=
let f0 :=
  fun (F:On->On) =>
  fix FIX(a:On)(b:On)(e:ex_Set nat T):On :=
  match e with (existSet _ _ n0 Tn) =>
    let F' :=
      match a with
      | Zero => F
      | Suc a0 => (oiter_Suc (seq_lim (fun n x => let (_,T0):=(prev n) in (FIX a0 x (existSet _ _ n T0)))))
      | Lim f => (oiter_Suc (seq_lim (fun n x => let (_,T0):=(prev n) in (FIX (f n) x (existSet _ _ n T0)))))
      end
    in let (φn,_):=(prev n0) in
    φn F' b Tn
  end
in (
  fun (F:On->On)(a:On)(bc:On*(ex_Set nat T)) => let (b,c):=bc in f0 F a b c,
  (Zero, existSet _ _ 0 (let (_,T0):=(prev 0) in T0))
).

(* Ta(a)辅助计算1+a元φ函数的参数列表的类型 *)
Fixpoint Ta(a:On):Set :=
match a with
| Zero => True (* 零个参数，占位 *)
| Suc a0 => On*(Ta a0) (* 对每个后继序数，在左边增加一个参数 *)
| Lim f => On*(ex_Set nat (fun n=>(Ta (f n)))) (* 对极限序数a，有最左参数，以及对应Ta(a[n])的右侧参数 *)
end.

(* φa(a)构造 1+a元φ函数 以及 表示a个0的参数列表 *)
Fixpoint φa(a:On):(((On->On)->On->(Ta a)->On)*(Ta a)) :=
match a with
| Zero => φ1'
| Suc a0 => φn_suc (φa a0)
| Lim f => φn_lim (fun n => φa (f n))
end.

(* φ_at(a,b) 表示 φ(a @ b) *)
Definition φ_at(a b:On):On :=
let (f,z):=(φa b) in 
f ωpow a z.

Definition SVO : On := (φ_at 1 ω).
Definition LVO : On := iter_lim (φ_at 1) 0.

Goal φ1'=(φa 0) /\ φ2'=(φa 1) /\ φ3'=(φa 2) /\ φ4'=(φa 3).
repeat split.
Qed.

Definition φ2'' := let (f,_):=φ2' in f.
Definition φ3'' := let (f,_):=φ3' in f.
Definition φ4'' := let (f,_):=φ4' in f.

Section CheckEq.
(* 为了方便，引入函数外延公理 *)
Hypothesis func_ext : forall {A B: Type} {f g : A->B},
  (forall x, f x = g x) -> f = g.

(* 验证和前面的定义是相容的 *)
Lemma φ2''_eq_φ2 : forall F x y, φ2'' F x (y,I) = φ2 F x y.
intros F x.
unfold φ2'',φ2',φ1',φn_suc,φ2.
induction x; auto.
all: intro y.
all: apply (inv (fun x=>oiter_Suc x y)),inv,func_ext.
- intro x0.
  apply IHx.
- intro x.
  apply func_ext.
  intro x0.
  apply H.
Qed.

(* 验证和前面的定义是相容的 *)
Lemma φ3''_eq_φ3 : forall F x y z, φ3'' F x (y,(z,I)) = φ3 F x y z.
intros F x.
unfold φ3'',φ3',φ3,φn_suc,φ2',φ2,φn_suc,φ1'.
induction x.
- apply φ2''_eq_φ2.
- intro y.
  induction y.
  all: intros.
  all: apply (inv (fun x=>oiter_Suc x z)),inv,func_ext.
  all: intro.
  + apply IHx.
  + apply IHy.
  + intros.
    apply func_ext. intros.
    apply H.
- intro y.
  induction y.
  all: intros.
  all: apply (inv (fun x=>oiter_Suc x z)),inv,func_ext.
  all: intro.
  + apply func_ext. intros.
    apply H.
  + apply IHy.
  + apply func_ext. intros.
    apply H0.
Qed.

(* 验证SVO的基本列的前几项 *)
Goal (φ_at 1 0) = (FS SVO 0) /\ (φ_at 1 1) = (FS SVO 1) /\ (φ_at 1 2) = (FS SVO 2).
auto.
Qed.

(* 验证φ(x@0)=ω^x *)
Goal (fun x=>φ_at x 0)=ωpow.
auto.
Qed.

End CheckEq.
