import Math.Data.WellFounded.Basic

inductive Relation.ReflTransGen (r: α -> α -> Prop) : α -> α -> Prop where
| refl : ReflTransGen r a a
| cons : r a b -> ReflTransGen r b c -> ReflTransGen r a c

inductive Relation.EquivGen (r: α -> α -> Prop) : α -> α -> Prop where
| single : r a b -> EquivGen r a b
| refl : EquivGen r a a
| symm : EquivGen r a b -> EquivGen r b a
| trans : EquivGen r a b -> EquivGen r b c -> EquivGen r a c

namespace Relation.ReflTransGen

def single (x: r a b) : ReflTransGen r a b := by
  apply ReflTransGen.cons x
  apply ReflTransGen.refl

def trans (x: ReflTransGen r a b) (y: ReflTransGen r b c) : ReflTransGen r a c := by
  induction x with
  | refl => assumption
  | cons ab bc ih =>
    apply ReflTransGen.cons
    assumption
    apply ih
    assumption

end Relation.ReflTransGen

class IsLawfulLT (α: Type _) [LT α] [LE α]: Prop where
  lt_iff_le_and_not_le: ∀{a b: α}, a < b ↔ a ≤ b ∧ ¬b ≤ a

export IsLawfulLT (lt_iff_le_and_not_le)
def IsLawfulLT.instLT (α: Type _) [LE α] : LT α where
  lt a b := a ≤ b ∧ ¬b ≤ a

def IsLawfulLT.inst (α: Type _) [LE α] : let _ := instLT α; IsLawfulLT α :=
  let _ := instLT α
  {
    lt_iff_le_and_not_le := Iff.rfl
  }

namespace Relation

variable (rel: α -> α -> Prop)
variable {r: α -> α -> Prop} {s: β -> β -> Prop} {t: α₁ -> α₁ -> Prop}

class IsRefl: Prop where
  refl (a): rel a a
export IsRefl (refl)
attribute [refl] IsRefl.refl

instance : IsRefl (ReflTransGen r) where
  refl _ := ReflTransGen.refl
instance [IsRefl rel] : IsRefl (TransGen rel) where
  refl a := TransGen.single (refl a)

class IsSymmetric: Prop where
  symm: ∀{a b}, rel a b -> rel b a
export IsSymmetric (symm)

instance {r: β -> β -> Prop} (f: α -> β) [IsSymmetric r] : IsSymmetric (fun x y => r (f x) (f y)) where
  symm := symm
instance : IsSymmetric (fun x y: α => x ≠ y) where
  symm := Ne.symm

instance [IsSymmetric rel] : IsSymmetric (ReflTransGen rel) where
  symm := by
    intro a b h
    induction h with
    | refl => exact .refl
    | cons a as ih =>
      apply ih.trans
      apply ReflTransGen.single
      apply symm
      assumption

instance [IsSymmetric rel] : IsSymmetric (TransGen rel) where
  symm := by
    intro a b h
    induction h with
    | single =>
      apply TransGen.single
      apply symm
      assumption
    | tail a as ih =>
      apply TransGen.trans
      apply TransGen.single
      apply symm
      assumption
      assumption

class IsTrans: Prop where
  trans: ∀{a b c}, rel a b -> rel b c -> rel a c
def trans' [IsTrans r] : ∀{a b c}, r a b -> r b c -> r a c := IsTrans.trans

instance [IsTrans rel] : Trans rel rel rel where
  trans := IsTrans.trans

instance : IsTrans (TransGen r) where
  trans := TransGen.trans
instance : IsTrans (ReflTransGen r) where
  trans := ReflTransGen.trans

class IsEquiv: Prop extends IsRefl rel, IsSymmetric rel, IsTrans rel where
instance (priority := 500) [IsRefl rel] [IsSymmetric rel] [IsTrans rel] : IsEquiv rel where

instance : IsEquiv (EquivGen rel) where
  refl _ := .refl
  symm := .symm
  trans := .trans

instance : @IsEquiv α (· = ·) where
  refl _ := rfl
  symm := Eq.symm
  trans := Eq.trans

variable (eqv: α -> α -> Prop) [IsEquiv eqv]

class CongrEquiv (eqv: α -> α -> Prop) [IsEquiv eqv]: Prop where
  congr_eqv: eqv a c -> eqv b d -> rel a b -> rel c d
export CongrEquiv (congr_eqv)

instance : CongrEquiv rel (· = ·) where
  congr_eqv := by rintro a b c d rfl rfl; exact id

instance [IsEquiv rel] : CongrEquiv rel rel where
  congr_eqv h g r := trans (symm h) (trans r g)

class IsAntisymmBy (eqv: outParam <| α -> α -> Prop) [IsEquiv eqv]: Prop extends CongrEquiv rel eqv where
  antisymm_by: rel a b -> rel b a -> eqv a b
export IsAntisymmBy (antisymm_by)

abbrev IsAntisymm := IsAntisymmBy rel (· = ·)

def _root_.antisymm (rel: α -> α -> Prop) [IsAntisymm rel] : rel a b -> rel b a -> a = b := antisymm_by

class IsAsymm: Prop where
  asymm: ∀{a b}, rel a b -> rel b a -> False
export IsAsymm (asymm)

class IsIrrefl: Prop where
  irrefl: ∀{a}, ¬rel a a
export IsIrrefl (irrefl)

instance (priority := 500) [IsAsymm rel] : IsIrrefl rel where
  irrefl {_} h := asymm h h

instance (priority := 500) [IsTrans rel] [IsIrrefl rel] : IsAsymm rel where
  asymm { _ _ } h g := irrefl (trans h g)

class IsWellFounded: Prop where
  wf: WellFounded rel
def wellFounded [inst: IsWellFounded rel] := inst.wf
def wfInduction [inst: IsWellFounded rel] := @WellFounded.induction _ _ inst.wf
def acc [inst: IsWellFounded rel] : ∀x, Acc rel x := (wellFounded rel).apply

instance [IsWellFounded rel] : IsWellFounded (TransGen rel) where
  wf := (wellFounded rel).transGen

instance [IsWellFounded rel] : IsAsymm rel where
  asymm {_ _} h g := WellFounded.irrefl (wellFounded _) <| (TransGen.single h).trans (TransGen.single g)

instance [IsWellFounded rel] : IsIrrefl rel := inferInstance

class IsTotal: Prop where
  total (a b): rel a b ∨ rel b a
def total [IsTotal rel] : ∀(a b: α), rel a b ∨ rel b a := IsTotal.total

class IsConnectedBy: Prop where
  protected connected_by: ∀a b, rel a b ∨ eqv a b ∨ rel b a
def connected_by [IsConnectedBy rel eqv] : ∀(a b: α), rel a b ∨ eqv a b ∨ rel b a := IsConnectedBy.connected_by
abbrev IsConnected := IsConnectedBy rel (· = ·)
def connected [IsConnected rel] : ∀(a b: α), rel a b ∨ a = b ∨ rel b a := connected_by _ _

def IsConnected.toTotal (h: IsConnected r) [IsRefl r] : IsTotal r where
  total a b := by
    rcases connected r a b with h | rfl | h
    left; assumption
    left; rfl
    right; assumption

instance (priority := 500) [h: IsConnected r] [IsRefl r] : IsTotal r := h.toTotal
instance (priority := 500) [h: IsTotal r] : IsConnected r where
  connected_by a b := by
    rcases total r a b with h | h
    left; assumption
    right; right; assumption

def eq_of_not_lt_or_gt [IsConnected rel] : ∀a b, ¬rel a b -> ¬rel b a -> a = b := by
  intro a b nab nba
  rcases connected rel a b with h | h | h
  exact (nab h).elim
  assumption
  exact (nba h).elim

class IsWellOrder : Prop extends IsWellFounded rel, IsTrans rel, IsConnected rel where
instance [IsWellFounded rel] [IsTrans rel] [IsConnected rel] : IsWellOrder rel where

instance [IsWellOrder rel] : IsIrrefl rel := inferInstance

-- class IsDense : Prop where
--   dense:

def symm_iff [IsSymmetric r] : ∀{a b}, r a b ↔ r b a := Iff.intro symm symm

/-- In a trichotomous irreflexive order, every element is determined by the set of predecessors. -/
def extensional_of_trichotomous_of_irrefl (r : α → α → Prop) [IsConnected r] [IsIrrefl r]
    {a b : α} (H : ∀ x, r x a ↔ r x b) : a = b :=
  ((@connected _ r _ a b).resolve_left <| mt (H _).2 <| irrefl).resolve_right <| mt (H _).1
    <| irrefl

def equiv [IsRefl rel] [IsSymmetric rel] [IsTrans rel] : Equivalence rel where
  refl := refl
  symm := symm
  trans := trans

def setoid [IsRefl rel] [IsSymmetric rel] [IsTrans rel] : Setoid α where
  r := rel
  iseqv := equiv rel

def ofTransGen [IsTrans r] (h: TransGen r a b) : r a b := by
  induction h with
  | single => assumption
  | tail x xs ih => apply trans' <;> assumption

def ofReflTransGen [IsRefl r] [IsTrans r] (h: ReflTransGen r a b) : r a b := by
  induction h with
  | refl => rfl
  | cons x xs ih => apply trans' <;> assumption

def ofEquivGen [IsRefl r] [IsSymmetric r] [IsTrans r] (h: EquivGen r a b) : r a b := by
  induction h with
  | single => assumption
  | refl => rfl
  | symm _ _ =>
    apply symm
    assumption
  | trans => apply trans' <;> assumption

end Relation

section

open Relation

instance [IsWellFounded r] [IsWellFounded s] : IsWellFounded (Sum.Lex r s) where
  wf := Sum.lex_wf (wellFounded r) (wellFounded s)
instance [IsTrans r] [IsTrans s] : IsTrans (Sum.Lex r s) where
  trans := by
    intro a b c ab bc
    cases ab <;> cases bc
    apply Sum.Lex.inl
    apply trans' <;> assumption
    apply Sum.Lex.sep
    apply Sum.Lex.inr
    apply trans' <;> assumption
    apply Sum.Lex.sep
instance [IsConnected r] [IsConnected s] : IsConnected (Sum.Lex r s) where
  connected_by a b := by
    cases a <;> cases b
    rename_i a b
    rcases connected r a b with ab | eq | ba
    left; apply Sum.Lex.inl; assumption
    right; left; congr
    right; right; apply Sum.Lex.inl; assumption
    left; apply Sum.Lex.sep
    right; right; apply Sum.Lex.sep
    rename_i a b
    rcases connected s a b with ab | eq | ba
    left; apply Sum.Lex.inr; assumption
    right; left; congr
    right; right; apply Sum.Lex.inr; assumption

instance {r: α -> α -> Prop} {s: β -> β -> Prop} [IsWellFounded r] [IsWellFounded s] : IsWellFounded (Prod.Lex r s) where
  wf :=
    let _wfr := WellFoundedRelation.mk r (wellFounded r)
    let _wfs := WellFoundedRelation.mk s (wellFounded s)
    let this := inferInstanceAs (WellFoundedRelation (Prod α β))
    this.wf

instance [IsTrans r] [IsTrans s] : IsTrans (Prod.Lex r s) where
  trans := by
    intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ x y
    cases x <;> cases y
    apply Prod.Lex.left
    apply trans' <;> assumption
    apply Prod.Lex.left
    assumption
    apply Prod.Lex.left
    assumption
    apply Prod.Lex.right
    apply trans' <;> assumption

instance [IsConnected r] [IsConnected s] : IsConnected (Prod.Lex r s) where
  connected_by := by
    intro ⟨a, b⟩ ⟨c, d⟩
    rcases connected r a c with ac | eq | ca
    left; apply Prod.Lex.left; assumption
    · subst c
      rcases connected s b d with bd | eq | bd
      left; apply Prod.Lex.right; assumption
      right; left; congr
      right; right; apply Prod.Lex.right; assumption
    right; right; apply Prod.Lex.left; assumption

end

namespace Relation

instance (s: Setoid α) : IsRefl s.r := ⟨s.refl⟩
instance (s: Setoid α) : IsSymmetric s.r := ⟨s.symm⟩
instance (s: Setoid α) : IsTrans s.r := ⟨s.trans⟩

instance (s: Setoid α) : IsRefl (HasEquiv.Equiv (α := α)) := ⟨s.refl⟩
instance (s: Setoid α) : IsSymmetric (HasEquiv.Equiv (α := α)) := ⟨s.symm⟩
instance (s: Setoid α) : IsTrans (HasEquiv.Equiv (α := α)) := ⟨s.trans⟩

abbrev relAnd (r s: α -> α -> Prop) (x y: α): Prop := r x y ∧ s x y
abbrev relOr (r s: α -> α -> Prop) (x y: α): Prop := r x y ∨ s x y

infixl:90 " ∧r " => relAnd
infixl:90 " ∨r " => relOr

instance {r s: α -> α -> Prop} [IsRefl r] [IsRefl s] : IsRefl (r ∧r s) where
  refl _ := ⟨refl _, refl _⟩

instance {r s: α -> α -> Prop} [IsRefl r] : IsRefl (r ∨r s) where
  refl _ := .inl (refl _)

instance {r s: α -> α -> Prop} [IsRefl s] : IsRefl (r ∨r s) where
  refl _ := .inr (refl _)

instance {r s: α -> α -> Prop} [IsSymmetric r] [IsSymmetric s] : IsSymmetric (r ∧r s) where
  symm t := ⟨symm t.1, symm t.2⟩

instance {r s: α -> α -> Prop} [IsSymmetric r] [IsSymmetric s] : IsSymmetric (r ∨r s) where
  symm
  | .inl t => .inl (symm t)
  | .inr t => .inr (symm t)

instance {r s: α -> α -> Prop} [IsTrans r] [IsTrans s] : IsTrans (r ∧r s) where
  trans t₀ t₁ := ⟨trans t₀.1 t₁.1, trans t₀.2 t₁.2⟩

abbrev trivial: α -> α -> Prop := fun _ _ => True

instance : @IsEquiv α trivial where
  refl _ := True.intro
  symm _ := True.intro
  trans _ _ := True.intro

instance : @IsWellFounded Nat (· < ·) where
  wf := Nat.lt_wfRel.wf

instance [LE α] [IsRefl (· ≤ (·: α))] : IsRefl (· ≥ (·: α)) where
  refl a := by rfl

def strict (rel: α -> α -> Prop) (a b: α) := rel a b ∧ ¬rel b a
def or_eqv (rel eqv: α -> α -> Prop) (a b: α) := rel a b ∨ eqv a b

instance [IsRefl rel] : IsIrrefl (strict rel) where
  irrefl h := h.right (by rfl)

instance [IsTrans rel] : IsTrans (strict rel) where
  trans h g := ⟨trans h.left g.left, by
    intro h'
    exact g.right (trans h' h.left)⟩

instance [IsEquiv eqv] [CongrEquiv rel eqv] [IsTrans rel] : Trans rel eqv rel where
  trans {a b c} h g := congr_eqv (by rfl) g h
instance [IsEquiv eqv] [CongrEquiv rel eqv] [IsTrans rel] : Trans eqv rel rel where
  trans {a b c} h g := congr_eqv (symm h) (by rfl) g

instance [IsRefl eqv] : IsRefl (or_eqv rel eqv) where
  refl _ := .inr (by rfl)
instance [IsRefl rel] : IsRefl (or_eqv rel eqv) where
  refl _ := .inl (by rfl)
instance [IsEquiv eqv] [CongrEquiv rel eqv] [IsTrans rel] : IsTrans (or_eqv rel eqv) where
  trans h g := by
    cases h <;> cases g <;> rename_i h g
    repeat left; exact trans h g
    right; exact trans h g
instance [IsEquiv eqv] [CongrEquiv rel eqv] [IsConnectedBy rel eqv] : IsTotal (or_eqv rel eqv) where
  total a b := by
    rcases connected_by rel eqv a b with h | h | h
    left; left; assumption
    left; right; assumption
    right; left; assumption

instance [IsEquiv eqv] [CongrEquiv rel eqv] : CongrEquiv (or_eqv rel eqv) eqv where
  congr_eqv {a b c d} h g r := by
    cases r
    left; apply congr_eqv h g
    assumption
    right; apply congr_eqv h g
    assumption
    assumption

def quot_rel (rel eqv: α -> α -> Prop) [IsEquiv eqv] [CongrEquiv rel eqv] : Quotient (Relation.setoid eqv) -> Quotient (Relation.setoid eqv) -> Prop := by
  refine Quotient.lift₂ rel ?_
  intro a b c d h g
  apply propext
  apply Iff.intro; intro r
  apply congr_eqv (eqv := eqv) h g r
  intro r
  apply congr_eqv (eqv := eqv) (symm h) (symm g) r

end Relation

namespace Quot

private def rel {r : α -> α -> Prop} (q₁ q₂ : Quot r) : Prop := by
  apply Quot.liftOn q₁ _ _
  intro x₁
  apply Quot.liftOn q₂ _ _
  intro x₂
  exact Relation.EquivGen r x₁ x₂
  intro a b req
  apply propext
  apply Iff.intro
  intro h
  apply h.trans
  apply Relation.EquivGen.single
  assumption
  intro h
  apply h.trans
  apply Relation.EquivGen.symm
  apply Relation.EquivGen.single
  assumption
  intro a b eq
  apply propext
  induction q₂ using Quot.ind
  rename_i x₂
  show Relation.EquivGen _ _ _ ↔ Relation.EquivGen _ _ _
  apply Iff.intro
  intro h
  apply Relation.EquivGen.trans _ h
  apply Relation.EquivGen.symm
  apply Relation.EquivGen.single
  assumption
  intro h
  apply Relation.EquivGen.trans _ h
  apply Relation.EquivGen.single
  assumption

private def rel.refl {r : α -> α -> Prop} (q : Quot r) : rel q q := by
  induction q using Quot.ind
  apply Relation.EquivGen.refl

private def rel_of_eq {r : α -> α -> Prop} {q₁ q₂ : Quot r} : q₁ = q₂ → rel q₁ q₂ :=
  fun h => Eq.ndrecOn h (rel.refl q₁)

def exact {r: α -> α -> Prop} {x y: α} : Quot.mk r x = Quot.mk r y -> Relation.EquivGen r x y := by
  intro h
  exact Quot.rel_of_eq h

end Quot

namespace Relation
variable (rel eqv: α -> α -> Prop) [IsEquiv eqv]

class IsPreorder: Prop extends IsTrans rel, IsRefl rel where
class IsPartialOrder: Prop extends IsPreorder rel, IsAntisymmBy rel eqv where
class IsLinearOrder: Prop extends IsPartialOrder rel eqv, IsTotal rel where

class IsStrictPartialOrder: Prop extends IsTrans rel, IsAsymm rel where
class IsStrictLinearOrder: Prop extends IsStrictPartialOrder rel, IsConnectedBy rel eqv where

def strict_rel_or_eqv_of_rel [IsAntisymmBy rel eqv] (a b: α) : rel a b -> strict rel a b ∨ eqv a b := by
  intro h
  apply Classical.or_iff_not_imp_right.mpr
  intro g
  apply And.intro h
  intro h'
  have := antisymm_by h h'
  contradiction

instance [IsPreorder rel] : IsStrictPartialOrder (strict rel) where
instance [IsLinearOrder rel eqv] : IsStrictLinearOrder (strict rel) eqv where
  connected_by a b := by
    rcases total rel a b with h | h <;> rcases strict_rel_or_eqv_of_rel rel eqv _ _ h with g | g
    left; assumption
    right; left; assumption
    right; right; assumption
    right; left; apply symm
    assumption

instance [IsWellOrder rel] : IsStrictLinearOrder rel (· = ·) where

instance [IsEquiv eqv] [CongrEquiv rel eqv] [IsStrictLinearOrder rel eqv] : IsLinearOrder (or_eqv rel eqv) eqv where
  antisymm_by {a b} h g := by
    cases h; cases g
    rename_i h g
    exact (asymm h g).elim
    apply symm
    assumption
    assumption

instance [IsWellOrder rel] : IsLinearOrder (or_eqv rel (· = ·)) (· = ·) := inferInstance

end Relation
