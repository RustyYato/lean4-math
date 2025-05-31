import Math.Order.Defs
import Math.Logic.Equiv.Basic
import Math.Relation.Defs
import Math.TypeTheory.Lambda.Defs

protected inductive SystemF.Type where
| var (name: ℕ)
| func (arg ret: SystemF.Type)
| lam (body: SystemF.Type)
deriving DecidableEq, Repr

-- the number of type lambda we are inside
protected abbrev SystemF.Type.Ctx := ℕ
-- the types in the term lambdas we are inside
protected abbrev SystemF.Ctx := List SystemF.Type

-- all type variables are bound to either some lambda in this type or some
-- type in the ambeient context
inductive SystemF.Type.IsWellFormed : Type.Ctx -> SystemF.Type -> Prop where
| var : name < ctx -> IsWellFormed ctx (.var name)
| func :
  IsWellFormed ctx arg ->
  IsWellFormed ctx ret ->
  IsWellFormed ctx (.func arg ret)
| lam :
  IsWellFormed (ctx + 1) body ->
  IsWellFormed ctx (.lam body)

-- all types in the ctx are well formed
def SystemF.Ctx.IsWellFormed (ty_ctx: SystemF.Type.Ctx) (ctx: SystemF.Ctx) : Prop :=
  ∀ty ∈ ctx, ty.IsWellFormed ty_ctx

namespace SystemF.Type

def weaken_at_level (term: SystemF.Type) (level: ℕ) : SystemF.Type :=
  match term with
  | .lam body => .lam (body.weaken_at_level (level + 1))
  | .func arg ret => .func (arg.weaken_at_level level) (ret.weaken_at_level level)
  | .var name =>
    .var <|
      if name < level then
        name
      else
        name + 1

def weaken (term: SystemF.Type) : SystemF.Type := term.weaken_at_level 0

@[simp] def weaken_at_level_lam (body: SystemF.Type) (level: ℕ) : body.lam.weaken_at_level level = (body.weaken_at_level (level + 1)).lam := rfl
@[simp] def weaken_at_level_app (arg ret: SystemF.Type) (level: ℕ) : (arg.func ret).weaken_at_level level =
  (arg.weaken_at_level level).func (ret.weaken_at_level level) := rfl

def subst (term subst: SystemF.Type) (target: ℕ) : SystemF.Type :=
  match term with
  | .lam body => .lam (body.subst subst.weaken (target + 1))
  | .func arg ret => .func (arg.subst subst target) (ret.subst subst target)
  | .var name =>
    if name = target then
      subst
    else
      .var <|
        if name < target then
          name
        else
          name - 1

end SystemF.Type

namespace SystemF.Ctx.IsWellFormed

def nil (ty_ctx: SystemF.Type.Ctx) : IsWellFormed ty_ctx [] := nofun
def cons {ty_ctx: SystemF.Type.Ctx} (wf: IsWellFormed ty_ctx ctx) {ty: SystemF.Type} (h: ty.IsWellFormed ty_ctx) : IsWellFormed ty_ctx (ty::ctx)
| _, .head _ => h
| _, .tail _ h => wf _ h

end SystemF.Ctx.IsWellFormed

-- note: since we don't have type annotations baked into `Term`, we can give multiple different types
-- to the same term. This is fine, and doesn't really change any of the analysis.
inductive SystemF.IsWellTyped : SystemF.Type.Ctx -> SystemF.Ctx -> Term -> SystemF.Type -> Prop where
| var {ty_ctx ctx} (name: ℕ) (ty: SystemF.Type) (hname: name < ctx.length) :
  ty = ctx[name] ->
  ty.IsWellFormed ty_ctx ->
  IsWellTyped ty_ctx ctx (.var name) ty

| lam {ty_ctx ctx} (arg_ty ret_ty: SystemF.Type) (body: Term) :
  arg_ty.IsWellFormed ty_ctx ->
  IsWellTyped ty_ctx (arg_ty::ctx) body ret_ty ->
  IsWellTyped ty_ctx ctx (.lam body) (.func arg_ty ret_ty)

| app {ty_ctx ctx} (arg_ty ret_ty: SystemF.Type) (func arg: Term) :
  IsWellTyped ty_ctx ctx func (.func arg_ty ret_ty) ->
  IsWellTyped ty_ctx ctx arg arg_ty ->
  IsWellTyped ty_ctx ctx (.app func arg) ret_ty

| type_lam {ty_ctx ctx} (ret_ty: SystemF.Type) (body: Term) :
  ret_ty.IsWellFormed (ty_ctx + 1) ->
  IsWellTyped (ty_ctx + 1) ctx body ret_ty ->
  -- this variable should not occur in the term since it represents a type variable
  -- and it may only occur in the type position
  ¬body.References 0 ->
  IsWellTyped ty_ctx ctx (.lam body) (.lam ret_ty)

| type_app {ty_ctx ctx} (arg ret_ty ty: SystemF.Type) (body arg_witness: Term) :
  arg.IsWellFormed ty_ctx ->
  IsWellTyped ty_ctx ctx body (.lam ret_ty) ->
  ty = ret_ty.subst arg 0 ->
  IsWellTyped ty_ctx ctx (.app body arg_witness) ty

private opaque SystemF.Term.type_witness' : Σ'term: Term, term.IsValue ∧ term.IsClosed := ⟨.lam (.var 0), _root_.Term.IsValue.lam _, Term.IsClosedUnder.lam _ (Term.IsClosedUnder.var _ (by decide))⟩

-- the type witness is an arbitrary inert value
-- which we will use to replace any types in type applications
def SystemF.Term.type_witness : _root_.Term := type_witness'.1
def SystemF.Term.type_witness_value : type_witness.IsValue := type_witness'.2.1
def SystemF.Term.type_witness_closed : type_witness.IsClosed := type_witness'.2.2
