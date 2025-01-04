import Math.Data.Multiset.Basic
import Math.Data.Map.Basic

def Name := Nat
def Name.ofNat : Nat -> Name := id
def Name.toNat : Name -> Nat := id
instance : DecidableEq Name := inferInstanceAs (DecidableEq Nat)
instance : Repr Name := inferInstanceAs (Repr Nat)
attribute [irreducible] Name

inductive LamType where
| Void
| Func (arg ret: LamType)
deriving DecidableEq

inductive LamTerm where
| Panic (body: LamTerm) (ty: LamType)
| Lambda (arg_name: Name) (arg_ty: LamType) (body: LamTerm)
| App (func arg: LamTerm)
| Var (name: Name)

def nodup_keys (data: Multiset (Name × LamType)) := data.Pairwise <| fun x y => x.1 ≠ y.1

abbrev Context := Map Name LamType

inductive LamTerm.IsWellFormed : Context -> LamTerm -> Prop where
| Panic (body: LamTerm) (ty: LamType):
  IsWellFormed ctx body ->
  IsWellFormed ctx (.Panic body ty)
| Lambda (arg_name: Name) (arg_ty: LamType) (body: LamTerm):
  -- lambdas must introduce new names into the context
  arg_name ∉ ctx ->
  IsWellFormed (insert ⟨arg_name, arg_ty⟩ ctx) body ->
  IsWellFormed ctx (.Lambda arg_name arg_ty body)
| App (func arg: LamTerm) :
  IsWellFormed ctx func ->
  IsWellFormed ctx arg ->
  IsWellFormed ctx (.App func arg)
| Var (name: Name) :
  name ∈ ctx ->
  IsWellFormed ctx (.Var name)

inductive LamTerm.IsWellTyped : Context -> LamTerm -> LamType -> Prop where
| Panic (body: LamTerm) (ty: LamType):
  IsWellTyped ctx body .Void ->
  IsWellTyped ctx (.Panic body ty) ty
| Lambda (arg_name: Name) (arg_ty ret_ty: LamType) (body: LamTerm):
  -- lambdas must introduce new names into the context
  arg_name ∉ ctx ->
  IsWellTyped (insert ⟨arg_name, arg_ty⟩ ctx) body ret_ty ->
  IsWellTyped ctx (.Lambda arg_name arg_ty body) (.Func arg_ty ret_ty)
| App (arg_ty ret_ty: LamType) (func arg: LamTerm) :
  IsWellTyped ctx func (.Func arg_ty ret_ty) ->
  IsWellTyped ctx arg arg_ty ->
  IsWellTyped ctx (.App func arg) ret_ty
| Var (name: Name) (ty: LamType) (h: name ∈ ctx) :
  ty = ctx[name] ->
  IsWellTyped ctx (.Var name) ty

def LamTerm.IsWellTyped.IsWellFormed {ctx: Context} {term: LamTerm} {ty: LamType} :
  IsWellTyped ctx term ty -> term.IsWellFormed ctx := by
  intro wt
  induction wt with
  | Panic => apply IsWellFormed.Panic <;> assumption
  | Lambda => apply IsWellFormed.Lambda <;> assumption
  | App => apply IsWellFormed.App <;> assumption
  | Var => apply IsWellFormed.Var <;> assumption

inductive LamTerm.IsValue : LamTerm -> Prop where
| Lambda arg_name arg_ty body : IsValue (.Lambda arg_name arg_ty body)

inductive LamTerm.IsSubTerm : LamTerm -> LamTerm -> Prop where
| AppFunc func arg: IsSubTerm func (.App func arg)
| AppArg func arg: IsSubTerm arg (.App func arg)
| Panic body ty: IsSubTerm body (.Panic body ty)
| LambdaBody n ty body: IsSubTerm body (.Lambda n ty body)

inductive LamTerm.Introduces (name: Name) : LamTerm -> Prop where
| AppFunc func arg: Introduces name func -> Introduces name (.App func arg)
| AppArg func arg: Introduces name arg -> Introduces name (.App func arg)
| Panic body ty: Introduces name body -> Introduces name (.Panic body ty)
| LambdaBody n ty body: Introduces name body -> Introduces name (.Lambda n ty body)
| Lambda ty body: Introduces name (.Lambda name ty body)

def LamTerm.subst (term subst: LamTerm) (name: Name) : LamTerm :=
  match term with
  | .App func arg => .App (func.subst subst name) (arg.subst subst name)
  | .Panic body ty => .Panic (body.subst subst name) ty
  | .Lambda n ty body => .Lambda n ty (body.subst subst name)
  | .Var n => if n = name then subst else term

def LamTerm.IsWellFormed.NoContextIntroductions
  {ctx: Context} {term: LamTerm} : term.IsWellFormed ctx -> ∀x ∈ ctx, ¬term.Introduces x := by
  intro wf
  induction wf with
  | Var => intros _ _ _; contradiction
  | Panic body ty wf ih =>
    intro x x_in_ctx i
    cases i; rename_i i
    exact ih _ x_in_ctx i
  | App _ _ _ _ ih₀ ih₁ =>
    intro x mem i
    cases i <;> rename_i i
    apply ih₀ _ mem i
    apply ih₁ _ mem i
  | Lambda _ _ _ nomem _ ih =>
    intro x mem i
    cases i <;> rename_i i
    apply ih x _ i
    apply Map.mem_insert.mpr (.inl _)
    assumption
    contradiction

def LamTerm.NoCommonIntroductions (a b: LamTerm) := ∀x, a.Introduces x -> b.Introduces x -> False

def LamTerm.NoCommonIntroductions.symm :
  NoCommonIntroductions a b ->
  NoCommonIntroductions b a := by
  intro h x ax bx
  apply h <;> assumption

def LamTerm.NoCommonIntroductions.ofSubTerm :
  NoCommonIntroductions a b ->
  IsSubTerm a₀ a ->
  NoCommonIntroductions a₀ b := by
  intro h sub x ax bx
  cases sub <;> apply h x _ bx
  exact .AppFunc _ _ ax
  exact .AppArg _ _ ax
  exact .Panic _ _ ax
  exact .LambdaBody _ _ _ ax

def LamTerm.NoCommonIntroductions.ofTransSubTerm :
  NoCommonIntroductions a b ->
  Relation.ReflTransGen IsSubTerm a₀ a ->
  NoCommonIntroductions a₀ b := by
  intro h sub
  induction sub with
  | refl => assumption
  | cons sub _ ih =>
    apply NoCommonIntroductions.ofSubTerm
    apply ih
    assumption
    assumption

def LamTerm.IsWellFormed.weaken
  {ctx: Context} {term: LamTerm} {x}:
  IsWellFormed ctx term ->
  (¬term.Introduces x.fst) ->
  IsWellFormed (insert x ctx) term := by
  intro wf nointro
  induction wf with
  | Panic _ _ _ ih =>
    apply IsWellFormed.Panic
    apply ih
    intro h
    apply nointro
    apply Introduces.Panic
    assumption
  | App _ _ _ _ ih₀ ih₁ =>
    apply IsWellFormed.App
    apply ih₀
    intro h
    apply nointro
    apply Introduces.AppFunc
    assumption
    apply ih₁
    intro h
    apply nointro
    apply Introduces.AppArg
    assumption
  | Var =>
    apply LamTerm.IsWellFormed.Var
    apply Map.mem_insert.mpr (.inl _)
    assumption
  | Lambda arg_name _ _ _  _ ih =>
    apply IsWellFormed.Lambda
    intro h
    cases Map.mem_insert.mp h
    contradiction
    subst arg_name
    apply nointro
    apply Introduces.Lambda
    rw [Map.insert_comm]
    apply ih
    intro h
    apply nointro
    apply Introduces.LambdaBody
    assumption
    intro h
    subst h
    apply nointro
    apply Introduces.Lambda

def LamTerm.IsWellFormed.subst
  {ctx: Context}
  {term subst: LamTerm} {name: Name}:
  name ∈ ctx ->
  term.IsWellFormed ctx ->
  subst.IsWellFormed (ctx.erase name) ->
  term.NoCommonIntroductions subst ->
  (term.subst subst name).IsWellFormed (ctx.erase name) := by
  intro name_in_ctx wf subst_wf nocomm
  induction wf with
  | Panic _ _ _ ih  =>
    apply IsWellFormed.Panic
    apply ih
    assumption
    assumption
    apply NoCommonIntroductions.ofSubTerm
    assumption
    exact .Panic _ _
  | App _ _ _ _ ih₀ ih₁ =>
    apply IsWellFormed.App
    apply ih₀
    assumption
    assumption
    apply NoCommonIntroductions.ofSubTerm
    assumption
    exact .AppFunc _ _
    apply ih₁
    assumption
    assumption
    apply NoCommonIntroductions.ofSubTerm
    assumption
    exact .AppArg _ _
  | Lambda _ _ _ _ _ ih =>
    apply IsWellFormed.Lambda
    intro mem
    have ⟨arg_in_ctx, _⟩  := Map.mem_erase.mp mem
    contradiction
    rw [←Map.erase_insert_comm_of_ne]
    apply ih
    apply Map.mem_insert.mpr (.inl _)
    assumption
    · rw [Map.erase_insert_comm_of_ne]
      apply LamTerm.IsWellFormed.weaken
      assumption
      apply nocomm
      apply Introduces.Lambda
      dsimp
      intro h
      subst h
      contradiction
    apply NoCommonIntroductions.ofSubTerm
    assumption
    exact .LambdaBody _ _ _
    dsimp
    have := nocomm
    intro h
    subst h
    contradiction
  | Var n n_in_ctx =>
    unfold LamTerm.subst
    split
    assumption
    apply IsWellFormed.Var
    apply Map.mem_erase.mpr ⟨_, _⟩
    assumption
    assumption
