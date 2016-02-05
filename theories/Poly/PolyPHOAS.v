(** * The proposed meta-theory **)

(*
(kinds)        k := k -> k | *
(large types)  l := forall x : k , l | [s]
(small types)  s := s -> s | s s | x | [b]
(expr)         e := \ x : s. e | e e | x | e s | [b]
*)

Set Printing Universes.

Universes U2 U1 U0.
Constraint U1 < U2.
Constraint U0 < U1.

(** * Kinds **)

(* kinds of small types *)
Inductive kind : Set :=
| kStar 
| kArr (_ _ : kind).


Fixpoint kindD (k : kind) : Type@{U1} :=
  match k with
  | kStar => Type@{U0}
  | kArr a b => kindD a -> kindD b
  end.

(* kinds of large types *)
Inductive lkind : Set :=
| lkStar
| lkArr (_ : kind) (_ : lkind)            
| lkArrl (_ _ : lkind)
.

Fixpoint lkLift (k : kind) : lkind :=
  match k with
    | kStar => lkStar
    | kArr a b => lkArr a (lkLift b)
  end.

Fixpoint lkindD (k : lkind) : Type@{U2} :=
  match k with
  | lkStar => Type@{U1}
  | lkArr a b => kindD a -> lkindD b
  | lkArrl a b => lkindD a -> lkindD b
  end.

(** * Types **)
(* Small Types *)
Inductive type (F : kind -> Type) : kind -> Type :=
| smVar : forall k, F k -> type F k
| smArr : type F kStar -> type F kStar -> type F kStar
| smAbs : forall k1 k2, (F k1 -> type F k2) -> type F (kArr k1 k2)
| smApp : forall k1 k2, type F (kArr k1 k2) -> type F k1 -> type F k2
.

Arguments smVar {_ _} _.
Arguments smArr {_} _ _.
Arguments smAbs {_ _ _} _.
Arguments smApp {_ _ _} _ _.


(* Large Types *)
Inductive ltype (lF : lkind -> Type) (F : kind -> Type) : lkind -> Type :=
| tsmVar  : forall k, F k -> ltype lF F (lkLift k)
| tVar  : forall k, lF k -> ltype lF F k
| tArr : ltype lF F lkStar -> ltype lF F lkStar -> ltype lF F lkStar
| tPi : forall k, (F k -> ltype lF F lkStar) -> ltype lF F lkStar

(* small type abstraction/application *)
| tAbs : forall k1 k2, (type F k1 -> ltype lF F k2) -> ltype lF F (lkArr k1 k2)
| tApp : forall k1 k2, ltype lF F (lkArr k1 k2) -> type F k1 -> ltype lF F k2

(* large type abstraction/application *)
| tAbsl : forall k1 k2, (lF k1 -> ltype lF F k2) -> ltype lF F (lkArrl k1 k2)
| tAppl : forall k1 k2, ltype lF F (lkArrl k1 k2) -> ltype lF F k1 -> ltype lF F k2
.

Arguments tsmVar {_ _ _} _.
Arguments tVar {_ _ _} _.
Arguments tArr {_ _} _ _.
Arguments tPi {_ _ _} _.
Arguments tAbs {_ _ _ _} _.
Arguments tApp {_ _ _ _} _ _.
Arguments tAbsl {_ _ _ _} _.
Arguments tAppl {_ _ _ _} _ _.

Example idType : (forall lF F , ltype lF F lkStar).
refine (
  fun lF F =>
    tPi (fun (t : F kStar) =>
           let t := tsmVar t in
           _))
.
simpl in t.
exact (tArr t t).
Defined.

Fixpoint typeD {k} (t : type kindD k) : kindD k :=
  match t with
    | smVar x     => x
    | smArr t1 t2 => typeD t1 -> typeD t2                                           
    | smAbs f     => fun x => typeD (f x)
    | smApp f x   => typeD f (typeD x)
  end.

Definition liftType : Type@{U0} -> Type@{U1} := fun x => x.

Fixpoint lkLiftD (k : kind) : kindD k -> lkindD (lkLift k) :=
  match k with
      kStar => liftType
    | kArr a b => fun f x => lkLiftD b (f x)
  end.

Fixpoint ltypeD {k} (t : ltype lkindD kindD k) : lkindD k :=
  match t in ltype _ _ k return lkindD k with
    | tsmVar x => lkLiftD _ x
    | tVar x => x
    | tPi f => forall a, ltypeD (f a)
    | tArr t1 t2 => ltypeD t1 -> ltypeD t2                                           
    | tAbs f => fun x => ltypeD (f (smVar x))
    | tApp f x => ltypeD f (typeD x)
    | tAbsl f => fun x => ltypeD (f x)
    | tAppl f x => ltypeD f (ltypeD x)
  end.

(** * Expressions **)

(* Expressions with small types *)
Inductive expr (F : kind -> Type) (Fe : type F kStar -> Type) : type F kStar -> Type :=
| eVar  : forall t, Fe t -> expr F Fe t
| eAbs  : forall (t1 t2 : type F kStar), (Fe t1 -> expr F Fe t2) -> expr F Fe (smArr t1 t2)
| eApp  : forall (t1 t2 : type F kStar), expr F Fe (smArr t1 t2) -> expr F Fe t1 -> expr F Fe t2
.

Arguments eVar  {_ _ _} _.
Arguments eAbs  {_ _ _ _} _.
Arguments eApp  {_ _ _ _} _ _.

(* Expressions with large types *)
Inductive lexpr
          (lF : lkind -> Type)
          (F : kind -> Type)
          (lFe : ltype lF F lkStar -> Type) 
          (Fe : type F kStar -> Type) :
  ltype lF F lkStar -> Type :=
| small  : forall t, expr F Fe (smVar t) -> lexpr lF F lFe Fe (tsmVar t)
| leVar  : forall t, lFe t -> lexpr lF F lFe Fe t
| leAbs  : forall (t1 t2 : ltype lF F lkStar), (lFe t1 -> lexpr lF F lFe Fe t2) -> lexpr lF F lFe Fe (tArr t1 t2)
| leApp  : forall (t1 t2 : ltype lF F lkStar), lexpr lF F lFe Fe (tArr t1 t2) -> lexpr lF F lFe Fe t1 -> lexpr lF F lFe Fe t2
| leTAbs : forall k (tf : F k -> ltype lF F lkStar), (forall t, lexpr lF F lFe Fe (tf t)) -> lexpr lF F lFe Fe (tPi tf)
| leTApp : forall k (tf : F k -> ltype lF F lkStar), lexpr lF F lFe Fe (tPi tf) -> forall t, lexpr lF F lFe Fe (tf t)
.

Arguments small {_ _ _ _ _} _.
Arguments leVar  {_ _ _ _ _} _.
Arguments leAbs  {_ _ _ _ _ _} _.
Arguments leApp  {_ _ _ _ _ _} _ _.
Arguments leTAbs {_ _ _ _ _ _} _.
Arguments leTApp {_ _ _ _ _ _} _ _.

Fixpoint exprD {t : type kindD kStar} (e : expr kindD typeD t) : typeD t :=
  match e with
      eVar x => x 
    | eAbs f => fun x => exprD (f x)
    | eApp f x => exprD f (exprD x)
  end.

Fixpoint lexprD {t : ltype lkindD kindD lkStar} (e : lexpr lkindD kindD ltypeD typeD t) : ltypeD t :=
  match e in lexpr _ _ _ _ t return ltypeD t with
    | small x => exprD x
    | leVar x => x 
    | leAbs f => fun x => lexprD (f x)
    | leApp f x => lexprD f (lexprD x)
    | leTAbs f => fun x => lexprD (f x)
    | leTApp f x => lexprD f x
  end
  .

(* Local Variables: *)
(* coq-prog-name: "/Users/matt/.opam/system/bin/coqtop" *)
(* coq-load-path: nil *)
(* End: *)

