Require Import List.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Vector.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import SepLog.

Set Implicit Arguments.
Set Strict Implicit.

Section heap.
  Variable L S : Type.
  Variable SL : SeparationLogic L S.

  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Variable RType_typD : RType typD.

  Variable TI_Sep : TypInstance0 typD S.
  Variable TI_Prop : TypInstance0 typD L.
  Variable TI_Arr : TypInstance2 typD Fun.

  Let tySep := @typ0 _ typD _ TI_Sep.
  Let tyProp := @typ0 _ typD _ TI_Prop.
  Let tyArr := @typ2 _ typD _ TI_Arr.

  Variable expr : Type.
  Variable Expr_expr : Expr typD expr.

  Variable FI_Emp : FuncInstance0 typD expr emp.

  Variable SA_Star : SymAppN (n := 0) ((fun _ => tySep) :: (fun _ => tySep) :: nil)
                                      tySep.
  Variable SA_Inj : SymAppN (n := 0) ((fun _ => tyProp) :: nil)
                                      tySep.
  Variable SA_Ex : SymAppN (n := 1) ((fun _ => tySep) :: nil) (fun _ => tySep).

  Variable AI_app : forall d r, AppInstance (tyArr d r) d r.

  Parameter lift : nat -> nat -> expr -> expr.

  Record SepHeap : Type :=
  { Pures : list expr
  ; Impures : list (expr * list expr)
  }.

  Definition SepHeap_lift (s l : nat) (h : SepHeap) : SepHeap :=
    match l with
      | 0 => h
      | _ =>
        let lift := lift s l in
        {| Pures := map lift h.(Pures)
         ; Impures := map (fun ees =>
                             let '(e,es) := ees in
                             (lift e, map lift es)) h.(Impures)
        |}
    end.

  Definition ExSepHeap : Type :=
    (list typ * SepHeap)%type.

  Definition SepHeap_pure (e : expr) : SepHeap :=
    {| Pures := e :: nil
     ; Impures := nil
    |}.

  Definition ExSepHeap_pure (e : expr) : ExSepHeap :=
    (nil, SepHeap_pure e).

  Definition SepHeap_star (l r : SepHeap) : SepHeap :=
    {| Pures := l.(Pures) ++ r.(Pures)
     ; Impures := l.(Impures) ++ r.(Impures)
    |}.

  Definition ExSepHeap_star (l r : ExSepHeap) : ExSepHeap :=
    match l , r with
      | (lt, lh) , (rt, rh) =>
        let ll := length lt in
        let lr := length rt in
        (lt ++ rt,
         SepHeap_star (SepHeap_lift 0 lr lh)
                      (SepHeap_lift lr ll rh))
    end.

  Definition SepHeap_func (e : expr) : SepHeap :=
    {| Pures := nil
     ; Impures := (e, nil) :: nil
    |}.

  Definition ExSepHeap_func (e : expr) : ExSepHeap :=
    (nil, SepHeap_func e).

  Fixpoint stars' (ls : list S) : S :=
    match ls with
      | nil => @emp _ _ _
      | l :: ls =>
        star l (stars' ls)
    end.

  Fixpoint stars (ls : list S) : S :=
    match ls with
      | nil => @emp _ _ _
      | l :: nil => l
      | l :: ls => star l (stars ls)
    end.

  Let Emp := @ctor0 _ typD expr _ emp _.
  Let Star x y := sappn SA_Star (Vnil _) (Vcons x (Vcons y (Vnil _))).
  Let Inj x := sappn SA_Inj (Vnil _) (Vcons x (Vnil _)).
  Parameter App : expr -> expr -> expr.

  Fixpoint Apps (f : expr) (es : list expr) : expr :=
    match es with
      | nil => f
      | e :: es => Apps (App f e) es
    end.

  Fixpoint estars (ls : list expr) : expr :=
    match ls with
      | nil => Emp
      | l :: ls => Star l (estars ls)
    end.

  Definition SepHeapD (sh : SepHeap) : expr :=
    Star (estars (map Inj sh.(Pures)))
         (estars (map (fun xy => let '(x,y) := xy in Apps x y) sh.(Impures))).

  Require Import Coq.Init.Wf.

  (** Given the above definitions, this is a trivial catamorphism **)
  Section liftEx.
    Variable R : Type.
    Variable R_lift : nat -> nat -> R -> R.
    Variable R_star : R -> R -> R.
    Variable R_pure : expr -> R.
    Variable R_func : expr -> R.
    Variable R_emp : R.

    (** So now we want to write [liftEx]
     **   liftEx : expr -> (list typ * expr)
     ** we only know how to do it for [star] and [and]
     **)
  Definition liftEx (e : expr) : list typ * R.
  refine (
    @Fix_F expr (@acc _ _ _ Expr_expr) (fun _ => list typ * R)%type
           (fun e recur =>
              matchSepLog _ _ FI_Emp SA_Star SA_Inj SA_Ex e
                (fun _ => (nil, R_emp))
                (fun P _ => (nil, R_pure P))
                (fun l r lacc racc =>
                   let '(lt,le) := recur l lacc in
                   let '(rt,re) := recur r racc in
                   (lt ++ rt,
                    R_star (R_lift 0 (length rt) le)
                           (R_lift (length rt) (length lt) re)))
                (fun t b bacc =>
                   let '(lt,le) := recur b bacc in
                   (t :: lt, le))
                (fun _ => (nil, R_func e)))
           e (wf_acc e)).
  Defined.
  End liftEx.

End heap.