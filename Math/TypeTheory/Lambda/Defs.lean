import Math.Data.Map.Basic
import Math.Logic.Equiv.Defs

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
| Panic (body: Term) (ret_ty: LamType)

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

def IsWellTyped.NotEmptyValue {term: Term} :
  term.IsWellTyped ctx .Empty -> ¬term.IsValue := by
  intro wt val
  cases wt <;> contradiction

def relabel (f: Name ↪ Name) : Term -> Term
| .Var x => .Var (f x)
| .Lambda arg_ty n body => .Lambda arg_ty (f n) (body.relabel f)
| .App func arg => .App (func.relabel f) (arg.relabel f)
| .Panic body ret_ty => .Panic (body.relabel f) ret_ty

def IsWellTyped.relabel' (term: Term) (f: Name ↪ Name) :
  term.IsWellTyped ctx ty -> (term.relabel f).IsWellTyped (ctx.map_keys f) ty := by
  intro wt
  induction wt with
  | Var =>
    apply IsWellTyped.Var
    rw [Map.map_keys_get_elem]
    assumption
  | Lambda arg_ty arg_name body h wt ih =>
    apply IsWellTyped.Lambda
    rw [←Map.map_keys_insert_no_dup]
    assumption
  | App =>
    apply IsWellTyped.App
    assumption
    assumption
  | Panic =>
    apply IsWellTyped.Panic
    assumption

def IsWellTyped.relabel (term: Term) (f: Name ↪ Name) : term.IsWellTyped ctx ty -> (∀x ∈ ctx, f x = x) -> (term.relabel f).IsWellTyped ctx ty := by
  intro wt h
  have := relabel' term f wt
  rw [Map.map_keys_id_on] at this
  assumption
  assumption

def relabel_comp (f g: Name ↪ Name) (term: Term) :
  (term.relabel f).relabel g = term.relabel (f.trans g) := by
  induction term with
  | Var => rfl
  | Lambda arg_ty name body ih =>
    dsimp [relabel]
    congr
  | App =>
    dsimp [relabel]
    congr
  | Panic =>
    dsimp [relabel]
    congr

def relabel_id (term: Term) : term.relabel .rfl = term := by
  induction term with
  | Var => rfl
  | Lambda arg_ty arg_name body ih =>
    simp [relabel, ih]; rfl
  | App _ _ ih₀ ih₁ => simp [relabel, ih₀, ih₁]
  | Panic _ _ ih => simp [relabel, ih]

instance equiv : Setoid Term where
  r a b := ∃f: Name ≃ Name, a.relabel f = b
  iseqv := {
    refl := by
      intro x
      exists .rfl
      apply relabel_id
    symm := by
      rintro x y ⟨f, rfl⟩
      exists f.symm
      rw [relabel_comp]
      show relabel (f.trans f.symm) _ = _
      rw [Equiv.trans_symm]
      apply relabel_id
    trans := by
      rintro x y z ⟨f, rfl⟩ ⟨g,  rfl⟩
      exists f.trans g
      rw [relabel_comp]
      rfl
  }

def app_congr (h: a ≈ c) (g: b ≈ d): Term.App a b ≈ Term.App c d := by
  obtain ⟨h, rfl⟩ := h
  obtain ⟨g, rfl⟩ := g

  sorry

def subst_congr (a: Term) (s t: Term) :
  (∀n, a.Introduces n -> s.Introduces n -> False) ->
  (∀n, a.Introduces n -> t.Introduces n -> False) ->
  s ≈ t -> a.subst s n ≈ a.subst t n := by
  intro nocomm₀ nocomm₁ h
  induction a with
  | Var =>
    simp [subst]
    split
    assumption
    rfl
  | Lambda _ _ _ ih  =>
    simp [subst, ih]
    sorry
  | App _ _ ih₀ ih₁ =>
    simp [subst, ih₀, ih₁]
    sorry
  | Panic body ret_ty ih  =>
    simp [subst, ih]
    sorry

end Term
