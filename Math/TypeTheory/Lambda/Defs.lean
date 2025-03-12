import Math.Data.Map.Basic

structure Name where
  ofNat :: toNat : Nat
deriving DecidableEq

inductive LamType where
| Empty
| Func (arg ret: LamType)

inductive Term where
| Lambda (arg_ty: LamType) (arg_name: Name) (body: Term)
| App (func arg: Term)
| Var (name: Name)
| Panic (body: Term) (ret_ty: LamTerm)

namespace Term

def subst (term subst: Term) (name: Name) : Term :=
  match term with
  | .App func arg => .App (func.subst subst name) (arg.subst subst name)
  | .Panic body ty => .Panic (body.subst subst name) ty
  | .Lambda n ty body => .Lambda n ty (body.subst subst name)
  | .Var n => if n = name then subst else term

-- does this term have the given type
inductive IsWellTyped : Map Name LamType -> Term -> LamType -> Prop where
| Lambda (arg_ty arg_name body) (h: arg_name ∉ ctx) :
  IsWellTyped (ctx.insert_no_dup arg_name arg_ty h) body ret_ty ->
  IsWellTyped ctx (.Lambda arg_ty arg_name body) (.Func arg_ty ret_ty)
| App (func arg: Term) :
  IsWellTyped ctx func (.Func arg_ty ret_ty) ->
  IsWellTyped ctx arg arg_ty ->
  IsWellTyped ctx (.App func arg) ret_ty
| Var name (h: name ∈ ctx) :
  ty = ctx[name] -> IsWellTyped ctx (.Var name) ty
| Panic (body ret_ty) :
  IsWellTyped ctx body .Empty ->
  IsWellTyped ctx (.Panic body ret_ty) ret_ty

-- is there a lambda which introduces this name?
inductive Introduces : Term -> Name -> Prop where
| LambdaIntro (arg_ty arg_name body) : Introduces (.Lambda arg_ty arg_name body) arg_name
| LambdaBody (arg_ty arg_name body) :
  Introduces body name ->
  Introduces (.Lambda arg_ty arg_name body) name
| PanicBody (body ret_ty) :
  Introduces body name ->
  Introduces (.Panic body ret_ty) name
| AppFunc (func arg) :
  Introduces func name ->
  Introduces (.App func arg) name
| AppArg (func arg) :
  Introduces arg name ->
  Introduces (.App func arg) name

inductive IsValue : Term -> Prop where
| Lambda (arg_ty arg_name body) : IsValue (.Lambda arg_ty arg_name body)

def IsWellTyped.NoContextIntroductions {term: Term} : term.IsWellTyped ctx ty -> ∀x ∈ ctx, ¬term.Introduces x := by
  intro wt x hx
  induction wt with
  | Var => exact nofun
  | Lambda _ _ _ _  _ ih =>
    intro g
    cases g
    contradiction
    apply ih
    rw [Map.mem_insert_no_dup]; left; assumption
    assumption
  | App _ _ _ _ ih₀ ih₁ =>
    intro g
    cases g
    apply ih₀ <;> assumption
    apply ih₁ <;> assumption
  | Panic _ _ _ ih =>
    intro b
    apply ih
    assumption
    cases b
    assumption

-- NOTE: insert here means, insert if the key is not in the map
-- and if the key is in the map, then this is a no-op
def IsWellTyped.weaken {term: Term} : term.IsWellTyped ctx ty -> ¬term.Introduces x.fst -> term.IsWellTyped (insert x ctx) ty := by
  intro wt int
  induction wt with
  | Var =>
    apply IsWellTyped.Var
    rw [Map.insert_get_elem_tail]
    assumption
  | Lambda arg_ty arg_name body h wt ih =>
    refine IsWellTyped.Lambda arg_ty arg_name body ?_ ?_
    intro g
    apply int
    rw [Map.mem_insert] at g
    rcases g with g | g
    contradiction
    subst arg_name
    apply Introduces.LambdaIntro
    rw [Map.insert_no_dup_eq_insert,
      Map.insert_comm]
    rename_i ctx _
    rw [←Map.insert_no_dup_eq_insert (ctx := ctx)]
    apply ih
    intro h; apply int
    apply Introduces.LambdaBody
    assumption
    intro h; dsimp at h
    cases h
    apply int
    apply Introduces.LambdaIntro
  | App func arg funcwt argwt ih₀ ih₁ =>
    apply IsWellTyped.App
    apply ih₀
    intro h; apply int
    apply Introduces.AppFunc; assumption
    apply ih₁
    intro h; apply int
    apply Introduces.AppArg; assumption
  | Panic _ _ _ ih =>
    apply IsWellTyped.Panic
    apply ih
    intro h; apply int
    apply Introduces.PanicBody
    assumption

def IsWellTyped.weaken_nodup {term: Term} {name: Name} (h: name ∉ ctx) : term.IsWellTyped ctx ty -> ¬term.Introduces name -> term.IsWellTyped (ctx.insert_no_dup name newty h) ty := by
  rw [Map.insert_no_dup_eq_insert]
  apply IsWellTyped.weaken (x := (_, _))

def IsWellTyped.subst
  {term subst : Term}
  (name_in_ctx: name ∈ ctx) :
  term.IsWellTyped ctx ty ->
  subst.IsWellTyped (ctx.erase name) ctx[name] ->
  (∀n, term.Introduces n -> subst.Introduces n -> False) ->
  (term.subst subst name).IsWellTyped (ctx.erase name) ty := by
  intro wt substwt nocomm
  induction wt with
  | Var var var_mem h =>
    unfold Term.subst
    split; subst var
    subst h; assumption
    apply IsWellTyped.Var
    rw [Map.erase_get_elem]
    assumption
    rw [Map.mem_erase]
    apply And.intro <;> assumption
  | Lambda arg_ty arg_name body arg_name_not_mem wt ih =>
    apply IsWellTyped.Lambda
    rw [←Map.erase_insert_no_dup_comm_of_ne]
    apply ih
    rw [Map.insert_nodup_get_elem, dif_neg]
    rw [Map.erase_insert_no_dup_comm_of_ne]
    apply IsWellTyped.weaken_nodup
    assumption
    apply nocomm
    apply Introduces.LambdaIntro
    rintro rfl
    contradiction
    rintro rfl
    contradiction
    left; assumption
    · intro n h
      apply nocomm
      apply Introduces.LambdaBody
      assumption
    rintro rfl; contradiction
  | App _ _ _ _ ih₀ ih₁ =>
    apply IsWellTyped.App
    apply ih₀
    assumption
    · intro n b
      apply nocomm
      apply Introduces.AppFunc
      assumption
    apply ih₁
    assumption
    · intro n b
      apply nocomm
      apply Introduces.AppArg
      assumption
  | Panic _ _ _ ih =>
    apply IsWellTyped.Panic
    apply ih
    assumption
    · intro n b
      apply nocomm
      apply Introduces.PanicBody
      assumption

-- there every well typed term has exactly one valid type
def unique_typing {term: Term}:
  term.IsWellTyped ctx ty₀ ->
  term.IsWellTyped ctx ty₁ ->
  ty₀ = ty₁ := by
  intro wt₀ wt₁
  induction wt₀ generalizing ty₁ with
  | Var _ _ h =>
    cases wt₁ with
    | Var _ _ g =>
    subst h; subst g; rfl
  | Lambda _ _ _ _ _ ih  =>
    cases wt₁ with
    | Lambda =>
    congr
    apply ih
    assumption
  | App _ _ _ _ ih =>
    cases wt₁ with
    | App _ _  wt₁ =>
    cases ih wt₁
    rfl
  | Panic =>
    cases wt₁
    rfl

def LamTerm.IsWellTyped.NotEmptyValue {term: Term} :
  term.IsWellTyped ctx .Empty -> ¬term.IsValue := by
  intro wt val
  cases wt <;> contradiction

end Term
