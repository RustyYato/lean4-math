import Math.Data.WellFounded.Basic

inductive Relation.ReflTransGen (r: α -> α -> Prop) : α -> α -> Prop where
| refl : ReflTransGen r a a
| cons : r a b -> ReflTransGen r b c -> ReflTransGen r a c

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

namespace Relation

variable (rel: α -> α -> Prop)
variable {r: α -> α -> Prop} {s: β -> β -> Prop} {t: α₁ -> α₁ -> Prop}

class IsWellFounded: Prop where
  wf: WellFounded rel
def wellFounded [inst: IsWellFounded rel] := inst.wf
def wfInduction [inst: IsWellFounded rel] := @WellFounded.induction _ _ inst.wf
def acc [inst: IsWellFounded rel] : ∀x, Acc rel x := (wellFounded rel).apply

class IsTrans: Prop where
  trans: ∀{a b c}, rel a b -> rel b c -> rel a c
def trans [IsTrans r] : ∀{a b c}, r a b -> r b c -> r a c := IsTrans.trans

instance [IsTrans rel] : Trans rel rel rel where
  trans := trans

class IsTrichotomous: Prop where
  tri: ∀a b, rel a b ∨ a = b ∨ rel b a
def trichotomous [IsTrichotomous rel] : ∀(a b: α), rel a b ∨ a = b ∨ rel b a := IsTrichotomous.tri

def eq_of_not_lt_or_gt [IsTrichotomous rel] : ∀a b, ¬rel a b -> ¬rel b a -> a = b := by
  intro a b nab nba
  rcases trichotomous rel a b with h | h | h
  exact (nab h).elim
  assumption
  exact (nba h).elim

class IsIrrefl: Prop where
  irrefl: ∀{a}, ¬rel a a
def irrefl [IsIrrefl r] : ∀{a}, ¬r a a := IsIrrefl.irrefl

instance IsWellFounded.toIsIrrefl [wf: IsWellFounded rel] : IsIrrefl rel where
  irrefl := wf.wf.irrefl

class IsWellOrder extends IsWellFounded rel, IsTrans rel, IsTrichotomous rel: Prop where
instance [IsWellFounded rel] [IsTrans rel] [IsTrichotomous rel] : IsWellOrder rel where

instance IsWellOrder.toIsIrrefl [wo: IsWellOrder rel] : IsIrrefl rel where
  irrefl := wo.wf.irrefl

class IsSymmetric: Prop where
  symm: ∀{a b}, rel a b -> rel b a

def symm [IsSymmetric r] : ∀{a b}, r a b -> r b a := IsSymmetric.symm
def symm_iff [IsSymmetric r] : ∀{a b}, r a b ↔ r b a := Iff.intro symm symm

instance {r: β -> β -> Prop} (f: α -> β) [IsSymmetric r] : IsSymmetric (fun x y => r (f x) (f y)) where
  symm := symm
instance : IsSymmetric (fun x y: α => x ≠ y) where
  symm := Ne.symm

/-- In a trichotomous irreflexive order, every element is determined by the set of predecessors. -/
theorem extensional_of_trichotomous_of_irrefl (r : α → α → Prop) [IsTrichotomous r] [IsIrrefl r]
    {a b : α} (H : ∀ x, r x a ↔ r x b) : a = b :=
  ((@trichotomous _ r _ a b).resolve_left <| mt (H _).2 <| irrefl).resolve_right <| mt (H _).1
    <| irrefl

instance [IsWellFounded r] : IsWellFounded (TransGen r) where
  wf := (wellFounded r).transGen
instance : IsTrans (TransGen r) where
  trans := TransGen.trans
instance : IsTrans (ReflTransGen r) where
  trans := ReflTransGen.trans

instance [IsWellFounded r] [IsWellFounded s] : IsWellFounded (Sum.Lex r s) where
  wf := Sum.lex_wf (wellFounded r) (wellFounded s)
instance [IsTrans r] [IsTrans s] : IsTrans (Sum.Lex r s) where
  trans := by
    intro a b c ab bc
    cases ab <;> cases bc
    apply Sum.Lex.inl
    apply trans <;> assumption
    apply Sum.Lex.sep
    apply Sum.Lex.inr
    apply trans <;> assumption
    apply Sum.Lex.sep
instance [IsTrichotomous r] [IsTrichotomous s] : IsTrichotomous (Sum.Lex r s) where
  tri a b := by
    cases a <;> cases b
    rename_i a b
    rcases trichotomous r a b with ab | eq | ba
    left; apply Sum.Lex.inl; assumption
    right; left; congr
    right; right; apply Sum.Lex.inl; assumption
    left; apply Sum.Lex.sep
    right; right; apply Sum.Lex.sep
    rename_i a b
    rcases trichotomous s a b with ab | eq | ba
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
    apply trans <;> assumption
    apply Prod.Lex.left
    assumption
    apply Prod.Lex.left
    assumption
    apply Prod.Lex.right
    apply trans <;> assumption

instance [IsTrichotomous r] [IsTrichotomous s] : IsTrichotomous (Prod.Lex r s) where
  tri := by
    intro ⟨a, b⟩ ⟨c, d⟩
    rcases trichotomous r a c with ac | eq | ca
    left; apply Prod.Lex.left; assumption
    · subst c
      rcases trichotomous s b d with bd | eq | bd
      left; apply Prod.Lex.right; assumption
      right; left; congr
      right; right; apply Prod.Lex.right; assumption
    right; right; apply Prod.Lex.left; assumption

def asymm [IsTrans r] [IsIrrefl r] : r a b -> r b a -> False := fun h g => irrefl (trans h g)

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

end Relation
