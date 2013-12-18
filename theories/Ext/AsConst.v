Require Import ExtLib.Data.HList.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

Section as_const.
  Variable ts : types.
  Variable func : Type.
  Variable RSym_func : RSym (typD ts) func.

  Section as_const.
    Variable as_const_func : func -> option (sigT (typD ts nil)).

    Fixpoint as_const (e : expr func) (vs : list typ) (t : typ)
    : option (hlist (typD ts nil) vs -> typD ts nil t) :=
        match e with
          | UVar _ => None
          | Var v =>
            (** TODO: multiple lookups **)
            match nth_error vs v as z
                  return option (hlist (typD ts nil) vs -> match z with
                                                      | None => Empty_set
                                                      | Some x => typD ts nil x
                                                    end)
                      -> option (hlist (typD ts nil) vs -> typD ts nil t)
            with
              | Some t' => fun get =>
                             match get with
                               | Some get =>
                                 match typ_cast_typ ts nil t' t with
                                   | Some cast =>
                                     Some (fun g => cast (fun x => x) (get g))
                                   | None => None
                                 end
                               | None => None (** unreachable **)
                             end
              | None => fun _ => None
            end (@nth_error_hlist_nth _ _ vs v)
          | Abs t' e =>
            match t as t
                  return option (hlist (typD ts nil) vs -> typD ts nil t)
            with
              | tyArr d r =>
                match as_const e (d :: vs) r with
                  | Some body =>
                    Some (fun g => fun x => (body (Hcons x g)))
                  | None => None
                end
              | _ => None
            end
          | Inj f =>
            match as_const_func f with
              | Some (existT t' f) =>
                match typ_cast_typ ts nil t' t with
                  | None => None
                  | Some cast => Some (fun _ => cast (fun x => x) f)
                end
              | None => None
            end
          | App f e =>
            match as_const_simul f vs with
              | Some (existT (tyArr dt rt) f) =>
                match as_const e vs dt with
                  | Some e =>
                    match typ_cast_typ ts nil rt t with
                      | Some cast => Some (fun g => cast (fun x => x) ((f g) (e g)))
                      | None => None
                    end
                  | None => None
                end
              | _ => None
            end
        end
    with as_const_simul (e : expr func) (vs : list typ)
         : option { t : typ & hlist (typD ts nil) vs -> typD ts nil t } :=
           match e with
             | UVar _ => None
             | Var v =>
               (** TODO: multiple lookups **)
               match nth_error vs v as z
                     return option (hlist (typD ts nil) vs -> match z with
                                                                | None => Empty_set
                                                                | Some x => typD ts nil x
                                                              end)
                            -> option { t : typ & hlist (typD ts nil) vs -> typD ts nil t}
               with
                 | Some t' => fun get =>
                                match get with
                                  | Some get =>
                                    Some (existT (fun t => hlist (typD ts nil) vs -> typD ts nil t) t' (fun g => get g))
                                  | None => None (** unreachable **)
                                end
                 | None => fun _ => None
               end (@nth_error_hlist_nth _ _ vs v)

             | Abs t e =>
               match as_const_simul e (t :: vs) with
                 | Some (existT t' f) =>
                   Some (existT (fun t => hlist (typD ts nil) vs -> typD ts nil t) (tyArr t t') (fun g x => f (Hcons x g)))
                 | _ => None
               end
             | Inj f =>
               match as_const_func f with
                 | Some (existT t f) => Some (existT (fun t => hlist (typD ts nil) vs -> typD ts nil t) _ (fun _ => f))
                 | _ => None
               end
             | App f e =>
               match as_const_simul f vs with
                 | Some (existT (tyArr d r) f) =>
                   match as_const e vs d with
                     | Some x =>
                       Some (existT (fun t => hlist (typD ts nil) vs -> typD ts nil t) r (fun g => (f g) (x g)))
                     | _ => None
                   end
                 | _ => None
               end
           end.
  End as_const.

  (** TODO: These will be used to build the [as_const_func] above **)
  Record Delta : Type :=
  { type : typ
  ; repr : func
  ; defn : typD ts nil type }.

End as_const.
