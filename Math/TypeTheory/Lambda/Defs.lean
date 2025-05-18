import Math.Order.Defs
import Math.Logic.Equiv.Basic
import Math.Relation.Defs

inductive Term where
| lam (body: Term)
| app (func arg: Term)
| var (name: ℕ)

namespace Term

def weaken_at_level (term: Term) (level: ℕ) : Term :=
  match term with
  | .lam body => .lam (body.weaken_at_level (level + 1))
  | .app func arg => .app (func.weaken_at_level level) (arg.weaken_at_level level)
  | .var name =>
    .var <|
      if name < level then
        name
      else
        name + 1

def weaken (term: Term) : Term := term.weaken_at_level 0

def subst_at (term subst: Term) (var: ℕ) : Term :=
  match term with
  | .lam body => .lam (body.subst_at subst.weaken (var + 1))
  | .app func arg => .app (func.subst_at subst var) (arg.subst_at subst var)
  | .var name =>
    if name = var then
      subst
    else
      .var <|
        if name < var then
          name
        else
          name - 1

inductive IsValue : Term -> Prop where
| lam body : IsValue (.lam body)

instance : ∀term, Decidable (IsValue term)
| .lam body => .isTrue (.lam body)
| .var _ | .app _ _ => .isFalse nofun

-- the operational semantics of lambda calculus
inductive Reduce : Term -> Term -> Prop where
| apply (body arg) : arg.IsValue -> Reduce (.app (.lam body) arg) (body.subst_at arg 0)
| app_func (func func' arg) : Reduce func func' -> Reduce (.app func arg) (.app func' arg)
| app_arg (func arg arg') : func.IsValue -> Reduce arg arg' -> Reduce (.app func arg) (.app func arg')

-- term `a` reduces to term `b` if there are 0 or more steps
-- in the operational semantics that can be taken
def ReducesTo := Relation.ReflTransGen Reduce

-- the gold standard equvialence relation which specifies
-- when two terms reduce to the same value if they reduce to a value
def Equiv := Relation.EquivGen Reduce

def IsValue.notReduce (h: Term.IsValue t) : ∀t', ¬Reduce t t' := by
  intro t
  cases h
  nofun

instance decExistsReduction : ∀a, Decidable (∃b, Reduce a b)
| .var _ => .isFalse nofun
| .lam _ => .isFalse nofun
| .app func arg =>
  if hf:func.IsValue then
    if ha:arg.IsValue then
      match func with
      | .lam _ =>
      .isTrue ⟨_, .apply _ _ ha⟩
    else
      match decExistsReduction arg with
      | .isTrue h => .isTrue <| by
        obtain ⟨arg', h⟩ := h
        exact ⟨_, .app_arg _ _ _ hf h⟩
      | .isFalse h =>
        .isFalse <| by
          intro ⟨b, g⟩
          apply h; clear h
          cases g
          contradiction
          rename_i g
          have := IsValue.notReduce hf _ g
          contradiction
          rename_i h
          exact ⟨_, h⟩
  else
    match decExistsReduction func with
    | .isTrue h => .isTrue <| by
      obtain ⟨func', h⟩ := h
      exact ⟨_, .app_func _ _ _ h⟩
    | .isFalse h =>
      .isFalse <| by
        intro ⟨_, g⟩
        apply h; clear h
        cases g
        exfalso; apply hf
        apply IsValue.lam
        rename_i h
        exact ⟨_, h⟩
        contradiction

def Reduce.unique (h: Reduce a b) (g: Reduce a c) : b = c := by
  induction h generalizing c with
  | apply =>
    cases g
    rfl
    rename_i h
    have := IsValue.notReduce ?_ _ h
    contradiction
    apply IsValue.lam
    rename_i h _ _ g
    have := h.notReduce _ g
    contradiction
  | app_func func func' arg h ih =>
    cases g
    have := IsValue.notReduce ?_ _ h
    contradiction
    apply IsValue.lam
    rwa [ih]
    rename_i g _
    have := g.notReduce _ h
    contradiction
  | app_arg func arg arg' hf h ih =>
    cases g
    rename_i g
    have := g.notReduce _ h
    contradiction
    rename_i g
    have := hf.notReduce _ g
    contradiction
    rwa [ih]

end Term
