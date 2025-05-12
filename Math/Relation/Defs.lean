import Math.Data.WellFounded.Basic

abbrev Relation (α: Sort u) := α -> α -> Prop

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

def symm_iff [IsSymmetric r] : ∀{a b}, r a b ↔ r b a := Iff.intro symm symm

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

class CongrEquiv (eqv: α -> α -> Prop): Prop where
  congr_eqv: eqv a c -> eqv b d -> rel a b -> rel c d
export CongrEquiv (congr_eqv)

instance : CongrEquiv rel (· = ·) where
  congr_eqv := by rintro a b c d rfl rfl; exact id

instance [IsEquiv rel] : CongrEquiv rel rel where
  congr_eqv h g r := trans (symm h) (trans r g)

class IsAntisymmBy (eqv: outParam <| α -> α -> Prop): Prop extends CongrEquiv rel eqv where
  antisymm_by: rel a b -> rel b a -> eqv a b
export IsAntisymmBy (antisymm_by)

abbrev IsAntisymm := IsAntisymmBy rel (· = ·)

def _root_.antisymm (rel: α -> α -> Prop) [IsAntisymm rel] : rel a b -> rel b a -> a = b := antisymm_by

class IsAsymm: Prop where
  asymm: ∀{a b}, rel a b -> rel b a -> False
export IsAsymm (asymm)
def _root_.asymm [IsAsymm rel] {a b: α} : rel a b -> rel b a -> False := IsAsymm.asymm

class IsIrrefl: Prop where
  irrefl: ∀{a}, ¬rel a a
export IsIrrefl (irrefl)
def _root_.irrefl [IsIrrefl rel] (a: α) : ¬rel a a := IsIrrefl.irrefl

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

class IsDense : Prop where
  dense: ∀a b: α, rel a b -> ∃x: α, rel a x ∧ rel x b
export IsDense (dense)

class IsTop (a: α) : Prop where
  is_top : ∀x, ¬eqv x a -> rel x a
export IsTop (is_top)

class IsBot (a: α) : Prop where
  is_bot : ∀x, ¬eqv x a -> rel a x
export IsBot (is_bot)

class IsLawfulStrict (rel srel: α -> α -> Prop) : Prop where
  is_lawful_strict (a b: α): srel a b ↔ rel a b ∧ ¬rel b a
export IsLawfulStrict (is_lawful_strict)

class IsLawfulNonstrict (rel srel eqv: α -> α -> Prop) : Prop where
  is_lawful_nonstrict (a b: α): rel a b ↔ srel a b ∨ eqv a b
export IsLawfulNonstrict (is_lawful_nonstrict)

/-- In a connected irreflexive order, every element is determined by the set of predecessors. -/
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

variable {rel srel eqv: α -> α -> Prop}
variable [IsEquiv eqv] [CongrEquiv rel eqv]

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

abbrev empty: α -> α -> Prop := fun _ _ => False

instance : @IsAsymm α empty where
  asymm := nofun

instance : @IsTrans α empty where
  trans := nofun

instance : @IsWellFounded α empty where
  wf := by
    apply WellFounded.intro
    intro a ; apply Acc.intro
    nofun

instance [Subsingleton α] : @IsConnectedBy α empty eqv where
  connected_by a b := by
    right; left
    rw [Subsingleton.allEq a b]

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

instance [IsTrans rel] : Trans rel eqv rel where
  trans {a b c} h g := congr_eqv (by rfl) g h
instance [IsTrans rel] : Trans eqv rel rel where
  trans {a b c} h g := congr_eqv (symm h) (by rfl) g

instance [IsRefl eqv] : IsRefl (or_eqv rel eqv) where
  refl _ := .inr (by rfl)
instance [IsRefl rel] : IsRefl (or_eqv rel eqv) where
  refl _ := .inl (by rfl)
instance [IsTrans rel] : IsTrans (or_eqv rel eqv) where
  trans h g := by
    cases h <;> cases g <;> rename_i h g
    repeat left; exact trans h g
    right; exact trans h g
instance [IsConnectedBy rel eqv] : IsTotal (or_eqv rel eqv) where
  total a b := by
    rcases connected_by rel eqv a b with h | h | h
    left; left; assumption
    left; right; assumption
    right; left; assumption

instance : CongrEquiv (strict rel) eqv where
  congr_eqv := by
    intro a b c d ac bd ⟨r₀, r₁⟩
    apply And.intro
    exact congr_eqv ac bd r₀
    intro r; apply r₁
    exact congr_eqv (symm bd) (symm ac) r

instance : CongrEquiv (or_eqv rel eqv) eqv where
  congr_eqv {a b c d} h g r := by
    cases r
    left; apply congr_eqv h g
    assumption
    right; apply congr_eqv h g
    assumption

instance : IsLawfulStrict rel (strict rel) where
  is_lawful_strict _ _ := Iff.rfl

instance [IsAsymm rel] : IsLawfulStrict (or_eqv rel eqv) rel where
  is_lawful_strict a b := by
    apply Iff.intro
    · intro h
      apply And.intro
      left; assumption
      intro g; rcases g with g | g
      exact asymm h g
      exact irrefl (congr_eqv (by rfl) g h)
    · intro ⟨h, g⟩
      apply h.resolve_right
      intro h'
      apply g
      right; exact symm h'

instance [IsAntisymmBy rel eqv] [IsRefl rel] : IsLawfulNonstrict rel (strict rel) eqv where
  is_lawful_nonstrict a b := by
    apply Iff.intro
    intro h
    apply Classical.or_iff_not_imp_right.mpr
    intro g; apply And.intro
    assumption
    intro h'; apply g
    apply antisymm_by (rel := rel)
    assumption
    assumption
    intro h
    rcases h with h | h
    exact h.left
    exact congr_eqv (by rfl) h (by rfl)

instance [IsAntisymmBy rel eqv] [IsLawfulStrict rel srel] [IsRefl rel] : IsLawfulNonstrict rel srel eqv where
  is_lawful_nonstrict a b := by
    rw [is_lawful_strict (rel := rel) (srel := srel)]
    apply Iff.intro
    intro h
    apply Classical.or_iff_not_imp_right.mpr
    intro g; apply And.intro
    assumption
    intro h'; apply g
    apply antisymm_by (rel := rel)
    assumption
    assumption
    intro h
    rcases h with h | h
    exact h.left
    exact congr_eqv (by rfl) h (by rfl)

instance : IsLawfulNonstrict (or_eqv rel eqv) rel eqv where
  is_lawful_nonstrict _ _ := Iff.rfl

section subtype_rel

variable {P: α -> Prop}

def subtype_rel (rel: α -> α -> Prop) (P: α -> Prop) : Subtype P -> Subtype P -> Prop := fun a b => rel a b

def subtype_rel_to_rel : subtype_rel rel P a b -> rel a b := id
def subtype_rel_of_rel { a b: Subtype P } : rel a b -> subtype_rel rel P a b := id

instance [Relation.IsTrans rel] : Relation.IsTrans (subtype_rel rel P) where
  trans h g := subtype_rel_of_rel <| trans (subtype_rel_to_rel h) (subtype_rel_to_rel g)

instance [Relation.CongrEquiv rel eqv] : Relation.CongrEquiv (subtype_rel rel P) (subtype_rel eqv P)  where
  congr_eqv := by
    intro a b c d h g r
    exact congr_eqv (rel := rel) (eqv := eqv) h g r

instance [Relation.IsAntisymmBy rel eqv] : Relation.IsAntisymmBy (subtype_rel rel P) (subtype_rel eqv P)  where
  antisymm_by := Relation.antisymm_by (rel := rel)

instance [Relation.IsAntisymm rel] : Relation.IsAntisymm (subtype_rel rel P) where
  antisymm_by {a b} h g := by
    have := antisymm rel h g
    cases a; congr

instance [Relation.IsRefl rel] : Relation.IsRefl (subtype_rel rel P) where
  refl _ := Relation.refl (rel := rel) _

instance [Relation.IsConnectedBy rel eqv] : Relation.IsConnectedBy (subtype_rel rel P) (subtype_rel eqv P) where
  connected_by a b := Relation.connected_by rel eqv a.val b.val

instance [Relation.IsConnected rel] : Relation.IsConnected (subtype_rel rel P) where
  connected_by a b := by
    rcases Relation.connected rel a.val b.val with h | h | h
    left; assumption
    right; left; cases a; congr
    right; right; assumption

instance [Relation.IsTotal rel] : Relation.IsTotal (subtype_rel rel P) where
  total a b := by
    rcases Relation.total rel a.val b.val with h | h
    left; assumption
    right; assumption

instance [Relation.IsWellFounded rel] : Relation.IsWellFounded (subtype_rel rel P) where
  wf := by
    apply WellFounded.intro
    intro ⟨a, h⟩
    induction a using Relation.wfInduction rel with
    | h a ih =>
    apply Acc.intro
    intro ⟨b, hb⟩ r
    apply ih b r hb

instance [Relation.IsIrrefl rel] : Relation.IsIrrefl (subtype_rel rel P) where
  irrefl h := Relation.irrefl (rel := rel) h

instance [Relation.IsAsymm rel] : Relation.IsAsymm (subtype_rel rel P) where
  asymm h := Relation.asymm (rel := rel) h

end subtype_rel

section quot_rel

def quot_rel (rel eqv: α -> α -> Prop) [IsEquiv eqv] [CongrEquiv rel eqv] : Quotient (Relation.setoid eqv) -> Quotient (Relation.setoid eqv) -> Prop := by
  refine Quotient.lift₂ rel ?_
  intro a b c d h g
  apply propext
  apply Iff.intro; intro r
  apply congr_eqv (eqv := eqv) h g r
  intro r
  apply congr_eqv (eqv := eqv) (symm h) (symm g) r

instance [IsRefl rel] : IsRefl (quot_rel rel eqv) where
  refl a := by
    induction a using Quotient.ind with | _ a =>
    show rel a a
    rfl

instance [IsTrans rel] : IsTrans (quot_rel rel eqv) where
  trans {a b c} h g := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    induction c using Quotient.ind with | _ c =>
    exact trans (r := rel) h g

instance [IsAntisymmBy rel eqv] : IsAntisymm (quot_rel rel eqv) where
  antisymm_by {a b} h g := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    exact Quotient.sound (antisymm_by (rel := rel) h g)

instance [IsTotal rel] : IsTotal (quot_rel rel eqv) where
  total a b := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    apply total rel a b

instance [IsIrrefl rel] : IsIrrefl (quot_rel rel eqv) where
  irrefl {a} h := by
    induction a using Quotient.ind with | _ a =>
    exact irrefl (rel := rel) h

instance [IsAsymm rel] : IsAsymm (quot_rel rel eqv) where
  asymm {a b} h g := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    exact asymm (rel := rel) h g

instance [IsConnectedBy rel eqv] : IsConnected (quot_rel rel eqv) where
  connected_by a b := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    show rel a b ∨ _ ∨ rel b a
    rcases connected_by rel eqv a b with h | h | h
    left; assumption
    right; left; exact Quotient.sound h
    right; right; assumption

instance quot_rel.instIsLawfulStrict [IsLawfulStrict rel srel] [CongrEquiv srel eqv] : IsLawfulStrict (quot_rel rel eqv) (quot_rel srel eqv) where
  is_lawful_strict {a b} := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    show srel a b ↔ rel a b ∧ ¬rel b a
    apply is_lawful_strict

instance quot_rel.instIsLawfulNonstrict [IsLawfulNonstrict rel srel eqv] [CongrEquiv srel eqv] : IsLawfulNonstrict (quot_rel rel eqv) (quot_rel srel eqv) (· = ·) where
  is_lawful_nonstrict {a b} := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    show rel a b ↔ srel a b ∨ _
    apply (is_lawful_nonstrict (srel := srel) (eqv := eqv) a b).trans
    refine or_congr ?_ ?_
    rfl
    apply Iff.intro
    intro h; apply Quotient.sound h
    intro h; apply Quotient.exact h

end quot_rel

instance (priority := 500) [LE α] [LT α] [IsLawfulLT α] : @IsLawfulStrict α (· ≤ ·) (· < ·) where
  is_lawful_strict _ _ := lt_iff_le_and_not_le

instance (priority := 500) [LE α] [LT α] [@IsLawfulStrict α (· ≤ ·) (· < ·)] : IsLawfulLT α where
  lt_iff_le_and_not_le := is_lawful_strict _ _

instance [IsTrans rel] [IsLawfulStrict rel srel] : Trans rel srel srel where
  trans := by
    intro a b c ab bc
    rw [is_lawful_strict (srel := srel) (rel := rel)] at *
    apply And.intro
    exact trans ab bc.left
    intro h; apply bc.right
    exact trans h ab

instance [IsTrans rel] [IsLawfulStrict rel srel] : Trans srel rel srel where
  trans := by
    intro a b c ab bc
    rw [is_lawful_strict (srel := srel) (rel := rel)] at *
    apply And.intro
    exact trans ab.left bc
    intro h; apply ab.right
    exact trans bc h

protected def IsLawfulStrict.IsTrans [IsTrans rel] [IsLawfulStrict rel srel] : IsTrans srel where
  trans := by
    intro a b c ab bc
    rw [is_lawful_strict (srel := srel) (rel := rel)] at *
    apply And.intro
    exact trans ab.left bc.left
    intro h
    exact bc.right (trans h ab.left)

protected def IsLawfulStrict.IsIrrefl [IsRefl rel] [IsLawfulStrict rel srel] : IsIrrefl srel where
  irrefl {a} h := (propext (is_lawful_strict (rel := rel) (srel := srel) a a) ▸ h).right (by rfl)
instance [LE α] [LT α] [@IsTrans α (· ≤ ·)] [IsLawfulLT α] : @IsTrans α (· < ·) :=
  IsLawfulStrict.IsTrans (rel := (· ≤ ·))
instance [LE α] [LT α] [@IsRefl α (· ≤ ·)] [IsLawfulLT α] : @IsIrrefl α (· < ·) :=
  IsLawfulStrict.IsIrrefl (rel := (· ≤ ·))
instance [LE α] [LT α] [@IsAntisymm α (· ≤ ·)] [@IsRefl α (· ≤ ·)] [IsLawfulLT α] : @IsLawfulNonstrict α (· ≤ ·) (· < ·) (· = ·) :=
  inferInstance

protected def IsLawfulStrict.IsConnected [IsTotal rel] [IsAntisymmBy rel eqv] [IsLawfulStrict rel srel] : IsConnectedBy srel eqv where
  connected_by a b := by
    iterate 2 rw [is_lawful_strict (rel := rel) (srel := srel)]
    by_cases h:rel a b
    by_cases g:rel b a
    right; left; apply antisymm_by h g
    left; trivial
    have := (total rel a b).resolve_left h
    right ;right ; trivial

instance [LE α] [LT α] [IsLawfulLT α] [IsTotal (α := α) (· ≤ ·)] [@IsAntisymm (α := α) (· ≤ ·)] : IsConnected (α := α) (· < ·) :=
  IsLawfulStrict.IsConnected (rel := (· ≤ ·))

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

instance [IsPreorder rel] [CongrEquiv rel eqv] : IsPreorder (quot_rel rel eqv) where
instance [IsPartialOrder rel eqv] [CongrEquiv rel eqv] : IsPartialOrder (quot_rel rel eqv) (· = ·) where
instance [IsLinearOrder rel eqv] [CongrEquiv rel eqv] : IsLinearOrder (quot_rel rel eqv) (· = ·) where
instance [IsStrictPartialOrder rel] [CongrEquiv rel eqv] : IsStrictPartialOrder (quot_rel rel eqv) where
instance [IsStrictLinearOrder rel eqv] [CongrEquiv rel eqv] : IsStrictLinearOrder (quot_rel rel eqv) (· = ·) where

end Relation

namespace Relation

def exists_min {P: α -> Prop} (r: α -> α -> Prop) [IsWellFounded r] (h: ∃x, P x) : ∃x, P x ∧ ∀y, r y x -> ¬P y := by
  obtain ⟨x, px⟩ := h
  induction x using wfInduction r with
  | h x ih =>
  by_cases h:∃y, r y x ∧ P y
  obtain ⟨y, ryx, px⟩ := h
  apply ih
  assumption
  assumption
  refine ⟨x, px, ?_⟩
  intro y
  exact not_and.mp (not_exists.mp h y)

instance (f: α -> β) {r: β -> β -> Prop} [IsWellFounded r] : IsWellFounded (fun x y => r (f x) (f y)) where
  wf := by
    apply WellFounded.intro
    intro a
    generalize h:f a = b
    induction b using wfInduction r generalizing a with | h b ih =>
    subst b
    apply Acc.intro
    intro a' ra
    exact ih (f a') ra _ rfl

noncomputable
def argMin (f: α -> β) (r: β -> β -> Prop) [IsWellFounded r] [h: Nonempty α]: α :=
  Classical.choose <|
    have ⟨a⟩ := h
    exists_min (fun x y => r (f x) (f y)) (P := fun _ => True) ⟨a, True.intro⟩

def not_lt_argMin (a : α) (f: α -> β) {r: β -> β -> Prop} [IsWellFounded r] :
  have : Nonempty α := ⟨a⟩
  ¬r (f a) (f (argMin f r)) := by
    have := exists_min (fun x y => r (f x) (f y)) (P := fun _ => True) ⟨a, True.intro⟩
    have ⟨_, spec⟩ := Classical.choose_spec this
    intro h h
    have := spec _ h
    contradiction

end Relation
