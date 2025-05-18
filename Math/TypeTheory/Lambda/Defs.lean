import Math.Order.Defs
import Math.Logic.Equiv.Basic
import Math.Relation.Defs

inductive Term where
| lam (body: Term)
| app (func arg: Term)
| var (name: ℕ)
deriving DecidableEq

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

def subst (term subst: Term) (var: ℕ) : Term :=
  match term with
  | .lam body => .lam (body.subst subst.weaken (var + 1))
  | .app func arg => .app (func.subst subst var) (arg.subst subst var)
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
| apply (body arg) : arg.IsValue -> Reduce (.app (.lam body) arg) (body.subst arg 0)
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

def findReduction : ∀a, (Σ'b, Reduce a b) ⊕' ¬∃b, Reduce a b
| .var _ => .inr nofun
| .lam _ => .inr nofun
| .app func arg =>
  if hf:func.IsValue then
    if ha:arg.IsValue then
      match func with
      | .lam _ =>
      .inl ⟨_, .apply _ _ ha⟩
    else
      match findReduction arg with
      | .inl h => .inl <| by
        obtain ⟨arg', h⟩ := h
        exact ⟨_, .app_arg _ _ _ hf h⟩
      | .inr h =>
        .inr <| by
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
    match findReduction func with
    | .inl h => .inl <| by
      obtain ⟨func', h⟩ := h
      exact ⟨_, .app_func _ _ _ h⟩
    | .inr h =>
      .inr <| by
        intro ⟨_, g⟩
        apply h; clear h
        cases g
        exfalso; apply hf
        apply IsValue.lam
        rename_i h
        exact ⟨_, h⟩
        contradiction

instance decExistsReduction : Decidable (∃b, Reduce a b) :=
  match findReduction a with
  | .inl h => .isTrue ⟨h.1, h.2⟩
  | .inr h => .isFalse h

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

instance : Decidable (Reduce a b) :=
  match findReduction a with
  | .inl h =>
    if g:h.1 = b then
      .isTrue (g ▸ h.2)
    else
      .isFalse fun h' =>
        (g (Reduce.unique h.2 h')).elim
  | .inr h => .isFalse <| by
    intro g; apply h
    exists b

-- a term halts iff it reduces to a value
def Halts (term: Term) := ∃v: Term, v.IsValue ∧ term.ReducesTo v

namespace Halts

def reduce {term term': Term} (h: Reduce term term') : term.Halts ↔ term'.Halts := by
  symm; apply Iff.intro
  · intro ⟨v, hv, g⟩
    refine ⟨_, hv, ?_⟩
    apply Relation.ReflTransGen.cons
    assumption
    assumption
  · intro ⟨v, hv, g⟩
    refine ⟨_, hv, ?_⟩
    cases g
    have := hv.notReduce _ h
    contradiction
    rename_i g _
    cases (h.unique g).symm
    assumption

def reduces_to {term term': Term} (h: ReducesTo term term') : term.Halts ↔ term'.Halts := by
  induction h with
  | refl => rfl
  | cons r rs ih =>
    rw [←ih]
    apply reduce
    assumption

end Halts

def Reduce.halts {term term': Term} (h: Reduce term term') : term.Halts ↔ term'.Halts := by
  apply Halts.reduce
  assumption

def ReducesTo.halts {term term': Term} (h: ReducesTo term term') : term.Halts ↔ term'.Halts := by
  apply Halts.reduces_to
  assumption

end Term
