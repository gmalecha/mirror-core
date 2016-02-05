Require Import ExtLib.Data.HList.
(** * The proposed meta-theory **)

(*
(kinds)        k := k -> k | *
(large types)  l := forall x : k , l | [s]
(small types)  s := s -> s | s s | x | [b]
(expr)         e := \ x : s. e | e e | x | e s | ?u | [b]
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
Inductive type (Fu : list kind -> kind -> Type@{U1}) (F : kind -> Type@{U1}) : kind -> Type :=
| smVar : forall k, F k -> type Fu F k
| smUVar : forall ks k, Fu ks k -> hlist (type Fu F) ks -> type Fu F k
| smArr : type Fu F kStar -> type Fu F kStar -> type Fu F kStar
| smAbs : forall k1 k2, (F k1 -> type Fu F k2) -> type Fu F (kArr k1 k2)
| smApp : forall k1 k2, type Fu F (kArr k1 k2) -> type Fu F k1 -> type Fu F k2
.

Arguments smVar {_ _ _} _.
Arguments smUVar {_ _ _ _} _ _.
Arguments smArr {_ _} _ _.
Arguments smAbs {_ _ _ _} _.
Arguments smApp {_ _ _ _} _ _.


(* Large Types *)
Inductive ltype (lF : lkind -> Type@{U2}) (Fu : list kind -> kind -> Type@{U1}) (F : kind -> Type@{U1}) : lkind -> Type :=
| tsmVar  : forall k, F k -> ltype lF Fu F (lkLift k)
| tsmUVar  : forall ks k, Fu ks k -> hlist (fun x => type Fu F x) ks -> ltype lF Fu F (lkLift k)
| tVar  : forall k, lF k -> ltype lF Fu F k
| tArr : ltype lF Fu F lkStar -> ltype lF Fu F lkStar -> ltype lF Fu F lkStar
| tPi : forall k, (type Fu F k -> ltype lF Fu F lkStar) -> ltype lF Fu F lkStar

(* small type abstraction/application *)
| tAbs : forall k1 k2, (F k1 -> ltype lF Fu F k2) -> ltype lF Fu F (lkArr k1 k2)
| tApp : forall k1 k2, ltype lF Fu F (lkArr k1 k2) -> type Fu F k1 -> ltype lF Fu F k2

(* large type abstraction/application *)
| tAbsl : forall k1 k2, (lF k1 -> ltype lF Fu F k2) -> ltype lF Fu F (lkArrl k1 k2)
| tAppl : forall k1 k2, ltype lF Fu F (lkArrl k1 k2) -> ltype lF Fu F k1 -> ltype lF Fu F k2
.

Arguments tsmVar {_ _ _ _} _.
Arguments tsmUVar {_ _ _ _ _} _ _.
Arguments tVar {_ _ _ _} _.
Arguments tArr {_ _ _} _ _.
Arguments tPi {_ _ _ _} _.
Arguments tAbs {_ _ _ _ _} _.
Arguments tApp {_ _ _ _ _} _ _.
Arguments tAbsl {_ _ _ _ _} _.
Arguments tAppl {_ _ _ _ _} _ _.

Fixpoint liftT {lF Fu F k} (t : type Fu F k) : ltype lF Fu F (lkLift k) :=
  match t in type _ _ k return ltype lF Fu F (lkLift k) with
    smVar x => tsmVar x
  | smUVar u xs => tsmUVar u xs
  | smArr t1 t2 => tArr (liftT t1) (liftT t2)
  | smAbs f => tAbs (fun x => liftT (f x))
  | smApp f x => tApp (liftT f) x
  end.

Example idType {lF Fu F} : ltype lF Fu F lkStar :=
  tPi (fun t => liftT (smArr t t)).

Fixpoint build_Karrow (ls : list kind) (k : kind) : kind :=
  match ls with
  | nil => k
  | cons l ls => kArr l (build_Karrow ls k)
  end.

Definition kindDu (ls : list kind) (k : kind) : Type :=
  kindD (build_Karrow ls k).

Fixpoint typeD {k} (t : type kindDu kindD k) : kindD k :=
  match t with
  | smVar x     => x
  | @smUVar _ _ ks k u xs =>
    (fix rec ls xs : (kindDu ls k) -> kindD k :=
       match xs in hlist _ ls return kindDu ls k -> kindD k with
       | Hnil => fun x => x
       | Hcons x xs => fun u => rec _ xs (u (typeD x))
       end) ks xs u
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

Fixpoint ltypeD {k} (t : ltype lkindD kindDu kindD k) : lkindD k :=
  match t in ltype _ _ _ k return lkindD k with
    | tsmVar x => lkLiftD _ x
    | @tsmUVar _ _ _ ks k u xs =>
      lkLiftD _ ((fix rec ls (xs : hlist (fun x => type kindDu kindD x) ls) :=
                    match xs in hlist _ ls
                          return kindDu ls k -> kindD k
                    with
                    | Hnil => fun x => x
                    | Hcons x xs => fun f => rec _ xs (f (typeD x))
                    end) ks xs u)
    | tVar x => x
    | tPi f => forall a, ltypeD (f a)
    | tArr t1 t2 => ltypeD t1 -> ltypeD t2
    | tAbs f => fun x => ltypeD (f x)
    | tApp f x => ltypeD f (typeD x)
    | tAbsl f => fun x => ltypeD (f x)
    | tAppl f x => ltypeD f (ltypeD x)
  end.


(** * Expressions **)

(* Expressions have large types *)
Inductive expr
          (lF : lkind -> Type@{U2})
          (Ku : list kind -> kind -> Type@{U1})
          (F : kind -> Type@{U1})
          (Fu : list (ltype lF Ku F lkStar) -> ltype lF Ku F lkStar -> Type)
          (Fe : ltype lF Ku F lkStar -> Type) :
  ltype lF Ku F lkStar -> Type :=
| eVar  : forall t, Fe t -> expr lF Ku F Fu Fe t
| eUVar : forall ts t, Fu ts t -> hlist (expr lF Ku F Fu Fe) ts -> expr lF Ku F Fu Fe t

| eAbs  : forall (t1 t2 : ltype lF Ku F lkStar),
    (Fe t1 -> expr lF Ku F Fu Fe t2) -> expr lF Ku F Fu Fe (tArr t1 t2)
| eApp  : forall (t1 t2 : ltype lF Ku F lkStar), expr lF Ku F Fu Fe (tArr t1 t2) -> expr lF Ku F Fu Fe t1 -> expr lF Ku F Fu Fe t2
| eTAbs : forall k (tf : type Ku F k -> ltype lF Ku F lkStar), (forall t, expr lF Ku F Fu Fe (tf t)) -> expr lF Ku F Fu Fe (tPi tf)
| eTApp : forall k (tf : type Ku F k -> ltype lF Ku F lkStar), expr lF Ku F Fu Fe (tPi tf) -> forall t, expr lF Ku F Fu Fe (tf t)
.

Arguments eVar  {_ _ _ _ _ _} _.
Arguments eUVar  {_ _ _ _ _ _ _} _ _.
Arguments eAbs  {_ _ _ _ _ _ _} _.
Arguments eApp  {_ _ _ _ _ _ _} _ _.
Arguments eTAbs {_ _ _ _ _ _ _} _.
Arguments eTApp {_ _ _ _ _ _ _} _ _.

Section here.
  Context {lF : lkind -> Type} {Ku : list kind -> kind -> Type} {F : kind -> Type}.
  Fixpoint build_arrow (ls : list (ltype lF Ku F lkStar)) (rt : ltype lF Ku F lkStar)
  : ltype lF Ku F lkStar :=
    match ls with
    | nil => rt
    | cons l ls => tArr l (build_arrow ls rt)
    end.
End here.

Definition uvarD a b := ltypeD (build_arrow a b).


Fixpoint exprD {t : ltype lkindD kindDu kindD lkStar}
         (e : expr lkindD kindDu kindD uvarD ltypeD t)
: ltypeD t :=
  match e in expr _ _ _ _ _ t return ltypeD t with
    | eVar x => x
    | @eUVar _ _ _ _ _ ts t u xs =>
      (fix rec ts
          (es : hlist (fun t => expr lkindD kindDu kindD uvarD ltypeD t) ts) :
         (ltypeD (build_arrow ts t)) -> ltypeD t :=
         match es in hlist _ ts
               return (ltypeD (build_arrow ts t)) -> ltypeD t
         with
         | Hnil => fun x => x
         | Hcons e es => fun f => rec _ es (f (exprD e))
         end) ts xs u
    | eAbs f => fun x => exprD (f x)
    | eApp f x => exprD f (exprD x)
    | eTAbs f => fun x => exprD (f x)
    | eTApp f x => exprD f x
  end.

Example polyId {lF F Ku Fe Fu} : expr lF F Ku Fu Fe idType :=
  eTAbs (fun t : type F Ku kStar => eAbs (fun x : Fe (liftT t) => eVar x))
.

Example inst1 {lF F Ku Fe Fu} (t : type F Ku kStar) : expr lF F Ku Fe Fu (liftT (smArr t t)) :=
  eAbs (fun x => eApp (eTApp polyId t) (eVar x))
.

Example inst2 {lF F Ku Fu Fe} (t : type F Ku kStar) : expr lF F Ku Fu Fe (liftT (smArr t t)) :=
  eApp (eTApp polyId (smArr t t)) (eAbs (fun x => eVar x))
.


