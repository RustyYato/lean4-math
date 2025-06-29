import Math.Order.Defs
import Math.Logic.Equiv.Basic
import Math.Relation.Defs

inductive Term where
| lam (body: Term)
| app (func arg: Term)
| var (name: ℕ)
deriving DecidableEq, Repr

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

@[simp] def weaken_at_level_lam (body: Term) (level: ℕ) : body.lam.weaken_at_level level = (body.weaken_at_level (level + 1)).lam := rfl
@[simp] def weaken_at_level_app (func arg: Term) (level: ℕ) : (func.app arg).weaken_at_level level =
  (func.weaken_at_level level).app (arg.weaken_at_level level) := rfl

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

@[simp] def subst_lam (subst: Term) (body: Term) (var: ℕ) : body.lam.subst subst var = (body.subst subst.weaken (var + 1)).lam := rfl
@[simp] def subst_app (subst: Term) (func arg: Term) (var: ℕ) : (func.app arg).subst subst var = (func.subst subst var).app (arg.subst subst var) := rfl

def subst_all (term: Term) (offset: ℕ) : List Term -> Term
| [] => term
| subst::substs => (term.subst subst offset).subst_all offset substs

def weaken_all (term: Term) : ℕ -> Term
| 0 => term
| n + 1 => (term.weaken_all n).weaken

def weaken_at_level_comm (term: Term) : (term.weaken_at_level n).weaken_at_level m = (term.weaken_at_level (m - if m > n then 1 else 0)).weaken_at_level (n + if n > m then 1 else 0) := by
  induction term generalizing n m with
  | lam body ih =>
    simp
    rw [ih]
    ac_nf
    simp
    congr
    split <;> omega
  | app func arg ihf iha =>
    simp
    rw [ihf, iha]
    simp
  | var name =>
    rcases Nat.lt_trichotomy n m with h₀ | rfl | h₀
    · rw [if_pos, if_neg]
      any_goals omega
      simp [weaken_at_level]
      by_cases h₁:name < n
      simp [h₁, show name < m by omega, show name < m - 1 by omega]
      by_cases h₂:name < m - 1
      simp [h₁, h₂, show name < m by omega, show name < m - 1 by omega]
      omega
      simp [h₁, h₂]
      by_cases h₃:name + 1 < n
      simp [h₃]
      omega
      simp [h₃]
      omega
    · simp
    · rw [if_neg, if_pos]
      any_goals omega
      simp [weaken_at_level]
      by_cases h₁:name < m
      simp [h₁, show name < n by omega, show name < n + 1 by omega]
      by_cases h₂:name < n
      simp [h₁, h₂]
      simp [h₁, h₂]
      omega

def subst_at_weaken_at_level (term subst: Term) (var level: ℕ) : (term.subst subst var).weaken_at_level level = (term.weaken_at_level (level + if var ≤ level then 1 else 0)).subst (subst.weaken_at_level level) (var + if var ≤ level then 0 else 1):= by
  induction term generalizing subst level var with
  | lam body ih =>
    simp
    rw [ih]
    clear ih
    congr 1
    · ac_nf
      simp
    · unfold weaken
      rw [weaken_at_level_comm]
      simp
    · simp
      split <;> rfl
  | app func arg ihf iha =>
    simp
    apply And.intro
    apply ihf
    apply iha
  | var name =>
    split
    · simp [Term.subst, Term.weaken_at_level]
      split; subst name
      · have : var < level + 1 := by omega
        simp [this]
      · rename_i h₀ h₁
        by_cases h₂ :name < level + 1
        simp [h₂, h₁, h₀]
        unfold weaken_at_level
        simp
        split
        omega
        omega
        simp [h₂]
        simp at h₂
        have : var < name := by omega
        rw [if_neg, if_neg, if_neg]
        any_goals omega
        unfold weaken_at_level
        rw [if_neg]
        congr
        omega
        omega
    · simp [Term.subst, Term.weaken_at_level]
      rename_i h₀
      simp at h₀
      by_cases h₁:name < level
      · simp [h₁]
        rw [if_neg, if_pos, if_neg, if_pos]
        any_goals omega
        unfold weaken_at_level
        simp
        assumption
      · simp [h₁]
        simp at h₁
        by_cases h₂:name < var
        · simp [h₂]
          rw [if_neg, if_neg]
          any_goals omega
          unfold weaken_at_level
          simp
          assumption
        · simp [h₂]
          simp at h₂
          replace h₂ := lt_or_eq_of_le h₂
          rcases h₂ with h₂ | h₂
          rw [if_neg, if_neg]
          unfold weaken_at_level
          simp
          split
          any_goals omega
          subst var
          simp

inductive IsValue : Term -> Prop where
| lam body : IsValue (.lam body)

instance : ∀term, Decidable (IsValue term)
| .lam body => .isTrue (.lam body)
| .var _ | .app _ _ => .isFalse nofun

inductive References : Term -> ℕ -> Prop where
| lam_body : References body (n + 1) -> References (.lam body) n
| app_func : References func n -> References (.app func arg) n
| app_arg : References arg n -> References (.app func arg) n
| var : References (.var n) n

inductive IsClosedUnder : Term -> ℕ -> Prop where
| lam (body: Term) : IsClosedUnder body (n + 1) -> IsClosedUnder (.lam body) n
| app (func arg: Term) : IsClosedUnder func n -> IsClosedUnder arg n -> IsClosedUnder (.app func arg) n
| var (name: ℕ) : name < n -> IsClosedUnder (.var name) n

def IsClosed (term: Term) := term.IsClosedUnder 0

def closed_under_iff_not_references : IsClosedUnder t n ↔ ∀m, n ≤ m -> ¬t.References m := by
  apply Iff.intro
  · intro h m g r
    induction r generalizing n with
    | lam_body _ ih =>
      cases h
      apply ih
      assumption
      apply Nat.succ_le_succ
      assumption
    | app_func _ ih =>
      cases h
      apply ih
      assumption
      assumption
    | app_arg _ ih =>
      cases h
      apply ih
      assumption
      assumption
    | var =>
      cases h
      rw [←Nat.not_lt] at g
      contradiction
  · intro h
    induction t generalizing n with
    | lam body ih  =>
      apply IsClosedUnder.lam
      apply ih
      intro m hm r
      match m with
      | m + 1 =>
      apply h
      apply Nat.le_of_succ_le_succ
      assumption
      apply References.lam_body
      assumption
    | app func arg ihf iha =>
      apply IsClosedUnder.app
      · apply ihf
        intro m hm r
        apply h
        assumption
        apply References.app_func
        assumption
      · apply iha
        intro m hm r
        apply h
        assumption
        apply References.app_arg
        assumption
    | var name =>
      apply IsClosedUnder.var
      rw [←Nat.not_le]
      intro g; apply h _ g
      apply References.var

def closed_iff_not_references : IsClosed t ↔ ∀m, ¬t.References m := by
  simp [IsClosed, closed_under_iff_not_references]

def closed_under_weaken_at_level {term: Term} (h: term.IsClosedUnder n) (g: n ≤ m) : term.weaken_at_level m = term := by
  induction h generalizing m with
  | @lam n body h ih =>
    unfold weaken_at_level
    congr; apply ih
    apply Nat.succ_le_succ
    assumption
  | app func arg _ _ ihf iha =>
    unfold weaken_at_level
    congr; apply ihf
    assumption
    apply iha
    assumption
  | var name =>
    unfold weaken_at_level
    rw [if_pos]
    omega

def closed_weaken_at_level {term: Term} (h: term.IsClosed) : term.weaken_at_level n = term := by
  apply closed_under_weaken_at_level
  assumption
  apply Nat.zero_le

def closed_weaken {term: Term} (h: term.IsClosed) : term.weaken = term := by
  apply closed_weaken_at_level
  assumption

def closed_under_subst {term subst: Term} (h: term.IsClosedUnder n) (g: n ≤ m) : term.subst subst m = term := by
  induction h generalizing m subst with
  | @lam n body h ih =>
    unfold Term.subst
    congr; apply ih
    apply Nat.succ_le_succ
    assumption
  | app func arg _ _ ihf iha =>
    unfold Term.subst
    congr; apply ihf
    assumption
    apply iha
    assumption
  | var name =>
    unfold Term.subst
    rw [if_neg, if_pos]
    omega
    omega

def closed_subst {term subst: Term} (h: term.IsClosed) : term.subst subst m = term := by
  apply closed_under_subst
  assumption
  apply Nat.zero_le

-- if a term doesn't reference a variable, then any two substitutions are equal
def erase {var} (term: Term) (h: ¬term.References var) : Term :=
  match term with
  | .lam body => .lam (body.erase (var := var + 1) (by
    intro g; apply h
    apply References.lam_body
    assumption))
  | .app func arg => .app (func.erase (var := var) (by
    intro g; apply h
    apply References.app_func
    assumption)) (arg.erase (var := var) (by
    intro g; apply h
    apply References.app_arg
    assumption))
  | .var name =>
      .var <|
        if name < var then
          name
        else
          name - 1

-- if a term doesn't reference a variable, then a substitution is the same as just removing the variable
def not_reference_subst (term subst: Term) (h: ¬term.References n) : term.subst subst n = term.erase h := by
  induction term generalizing subst n with
  | lam body ih =>
    unfold Term.subst Term.erase
    rw [ih]
  | app func arg ihf iha =>
    unfold Term.subst Term.erase
    rw [ihf, iha]
  | var =>
    unfold Term.subst Term.erase
    split
    subst n; exfalso; apply h
    apply References.var
    rfl

-- the operational semantics of lambda calculus
inductive Reduce : Term -> Term -> Prop where
| apply (body arg) : arg.IsValue -> Reduce (.app (.lam body) arg) (body.subst arg 0)
| app_func (func func' arg) : Reduce func func' -> Reduce (.app func arg) (.app func' arg)
| app_arg (func arg arg') : func.IsValue -> Reduce arg arg' -> Reduce (.app func arg) (.app func arg')

-- term `a` reduces to term `b` if there are 0 or more steps
-- in the operational semantics that can be taken
def ReducesTo := Relation.ReflTransGen Reduce

-- term `a` reduces to term `b` if there are 0 or more steps
-- in the operational semantics that can be taken
def StrictReducesTo := Relation.TransGen Reduce

protected def StrictReducesTo.exists_reduce (h: StrictReducesTo term term') : ∃term₀, Reduce term term₀ := by
  induction h
  rename_i term₀ _
  exists term₀
  assumption

def ReducesTo.eq_or_strict (h: ReducesTo term term') : term = term' ∨ StrictReducesTo term term' := by
  apply Relation.ReflTransGen.eq_or_transgen
  assumption

instance : Relation.IsRefl ReducesTo :=
  inferInstanceAs (Relation.IsRefl (Relation.ReflTransGen _))
instance : Relation.IsTrans ReducesTo :=
  inferInstanceAs (Relation.IsTrans (Relation.ReflTransGen _))

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

def ReducesTo.unique (a v w: Term) (hav: Term.ReducesTo a v) (haw: Term.ReducesTo a w) (hv: Term.IsValue v) (hw: Term.IsValue w) : v = w := by
  induction hav with
  | @refl a =>
    cases haw with
    | refl => rfl
    | @cons _ b _ h ih =>
      have := hv.notReduce _ h
      contradiction
  | @cons a b v hab h ih =>
    apply ih _ hv
    cases haw
    have := hw.notReduce _ hab
    contradiction
    rename_i b' hb' _
    cases Reduce.unique hab hb'
    assumption

-- a term halts iff it reduces to a value
def Halts (term: Term) := ∃v: Term, v.IsValue ∧ term.ReducesTo v

namespace Reduce

def weaken_at_level (r: Reduce term term') : Reduce (term.weaken_at_level n) (term'.weaken_at_level n) := by
  induction r generalizing n with
  | apply body arg arg_value =>
    simp [subst_at_weaken_at_level]
    apply Reduce.apply
    cases arg_value
    apply IsValue.lam
  | app_func func func' arg r ih =>
    simp
    apply Reduce.app_func
    apply ih
  | app_arg func arg arg' hf r ih =>
    simp
    apply Reduce.app_arg
    cases hf
    apply IsValue.lam
    apply ih

end Reduce

namespace ReducesTo

def weaken_at_level (r: ReducesTo term term') : ReducesTo (term.weaken_at_level n) (term'.weaken_at_level n) := by
  induction r with
  | refl => rfl
  | cons r rs ih =>
    apply flip Relation.trans'
    apply ih
    apply Relation.ReflTransGen.single
    apply r.weaken_at_level

end ReducesTo

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

def weaken_at_level {term: Term} (h: term.Halts) : (term.weaken_at_level n).Halts := by
  obtain ⟨v, hv, h⟩ := h
  exists v.weaken_at_level n
  apply And.intro
  cases hv
  apply IsValue.lam
  apply h.weaken_at_level

end Halts

def Reduce.halts {term term': Term} (h: Reduce term term') : term.Halts ↔ term'.Halts := by
  apply Halts.reduce
  assumption

def ReducesTo.halts {term term': Term} (h: ReducesTo term term') : term.Halts ↔ term'.Halts := by
  apply Halts.reduces_to
  assumption

end Term
