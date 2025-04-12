import Math.Order.Lattice.Basic

section

inductive FreeLattice.Pre (α: Type*) where
| of (a: α)
| max (a b: Pre α)
| min (a b: Pre α)

variable {α: Type*}

protected inductive FreeLattice.Pre.LE : Pre α -> Pre α -> Prop where
| refl (a: Pre α): Pre.LE a a
| trans: Pre.LE a b -> Pre.LE b c -> Pre.LE a c

| le_max_left : Pre.LE a (max a b)
| le_max_right : Pre.LE b (max a b)

| min_le_left : Pre.LE (min a b) a
| min_le_right : Pre.LE (min a b) b

| max_le : Pre.LE a k -> Pre.LE b k -> Pre.LE (max a b) k
| le_min : Pre.LE k a -> Pre.LE k b -> Pre.LE k (min a b)

inductive FreeLattice.Pre.Equiv : Pre α -> Pre α -> Prop where
| refl (a: Pre α): Equiv a a
| symm: Equiv a b -> Equiv b a
| trans: Equiv a b -> Equiv b c -> Equiv a c

| max_comm : Equiv (max a b) (max b a)
| min_comm : Equiv (min a b) (min b a)

| max_assoc : Equiv (max (max a b) c) (max a (max b c))
| min_assoc : Equiv (min (min a b) c) (min a (min b c))

| max_min : Equiv (max a (min a b)) a
| min_max : Equiv (min a (max a b)) a

| min_congr : Equiv a c -> Equiv b d -> Equiv (min a b) (min c d)
| max_congr : Equiv a c -> Equiv b d -> Equiv (max a b) (max c d)

instance FreeLattice.setoid : Setoid (Pre α) where
  r := FreeLattice.Pre.Equiv
  iseqv := {
    refl := .refl
    symm := .symm
    trans := .trans
  }

namespace FreeLattice.Pre

variable {α: Type*}

@[refl]
def refl (a: Pre α): a ≈ a := Pre.Equiv.refl _
@[symm]
def symm {a b: Pre α}: a ≈ b -> b ≈ a := Pre.Equiv.symm
def trans {a b c: Pre α}: a ≈ b -> b ≈ c -> a ≈ c := Pre.Equiv.trans

variable (a b c d k: Pre α)

def max_comm : (max a b) ≈ (max b a) := Pre.Equiv.max_comm
def min_comm : (min a b) ≈ (min b a) := Pre.Equiv.min_comm

def min_assoc : min (min a b) c ≈ min a (min b c) := Pre.Equiv.min_assoc
def max_assoc : max (max a b) c ≈ max a (max b c) := Pre.Equiv.max_assoc

def max_min : (max a (min a b)) ≈ a := Pre.Equiv.max_min
def min_max : (min a (max a b)) ≈ a := Pre.Equiv.min_max

def min_congr {a b c d: Pre α} : a ≈ c -> b ≈ d -> (min a b) ≈ (min c d) := Pre.Equiv.min_congr
def max_congr {a b c d: Pre α} : a ≈ c -> b ≈ d -> (max a b) ≈ (max c d) := Pre.Equiv.max_congr

def min_self : (min a a) ≈ a := by
  apply trans _ (min_max a (min a a))
  apply min_congr
  rfl
  symm; apply max_min
def max_self : (max a a) ≈ a := by
  apply trans _ (max_min a a)
  apply max_congr
  rfl
  symm; apply min_self

instance : LE (FreeLattice.Pre α) where
  le a b := .min a b ≈ a
instance : LT (FreeLattice.Pre α) where
  lt a b := a ≤ b ∧ ¬b ≤ a
instance : IsLawfulLT (FreeLattice.Pre α) where
  lt_iff_le_and_not_le := Iff.rfl
instance : IsPreOrder (FreeLattice.Pre α) where
  le_refl := FreeLattice.Pre.min_self
  le_trans {a b c} := by
    show _ ≈ _ -> _ ≈ _ -> _ ≈ _
    intro h g
    apply trans
    apply min_congr
    symm; assumption
    rfl
    apply trans
    apply min_assoc
    apply trans
    apply min_congr
    rfl
    assumption
    assumption

def le_iff_min_eq_left : (a ≤ b) ↔ min a b ≈ a := Iff.rfl
def le_iff_max_eq_right : (a ≤ b) ↔ max a b ≈ b := by
  apply Iff.trans (le_iff_min_eq_left _ _)
  apply Iff.intro
  intro h
  apply trans
  apply max_congr
  symm; assumption
  rfl
  apply trans
  apply max_comm
  apply trans
  apply max_congr; rfl
  apply min_comm
  apply max_min
  intro h
  apply trans
  apply min_congr; rfl
  symm; assumption
  apply min_max

def le_max_left: a ≤ (max a b) := by apply min_max
def le_max_right: b ≤ (max a b) := by
  show _ ≈ _
  apply trans
  apply min_congr
  rfl
  apply max_comm
  apply min_max

def min_le_left: (min a b) ≤ a := by
  show _ ≈ _
  apply trans
  apply min_comm
  apply trans
  symm; apply min_assoc
  apply min_congr
  apply min_self
  rfl
def min_le_right: (min a b) ≤ b := by
  show _ ≈ _
  apply trans
  apply min_assoc
  apply min_congr
  rfl; apply min_self

def le_antisymm {a b: Pre α} (h: a ≤ b) (g: b ≤ a) : a ≈ b := by
  apply trans
  symm; assumption
  apply trans
  apply min_comm
  assumption

def max_le: a ≤ k -> b ≤ k -> (max a b) ≤ k := by
  rw [le_iff_max_eq_right, le_iff_max_eq_right, le_iff_max_eq_right]
  intro ak bk
  apply trans
  apply max_assoc
  apply trans
  apply max_congr; rfl
  assumption
  assumption
def le_min: k ≤ a -> k ≤ b -> k ≤ (min a b) := by
  show _ ≈ _ -> _ ≈ _ -> _ ≈ _
  intro ak bk
  apply trans
  symm; apply min_assoc
  apply trans
  apply flip min_congr; rfl
  assumption
  assumption

def prele_of_eqv : a ≈ b -> Pre.LE a b ∧ Pre.LE b a := by
  intro h
  induction h with
  | refl => apply And.intro <;> apply Pre.LE.refl
  | symm => apply And.symm; assumption
  | trans _ _ ih₀ ih₁ =>
    sorry
  | max_comm => sorry
  | max_assoc => sorry
  | min_comm => sorry
  | min_assoc => sorry
  | max_min => sorry
  | min_max => sorry
  | min_congr => sorry
  | max_congr => sorry

end FreeLattice.Pre

def FreeLattice (α: Type*) := Quotient (FreeLattice.setoid (α := α))

end

namespace FreeLattice

def ofPre : FreeLattice.Pre α -> FreeLattice α := Quotient.mk _

scoped notation "⟦" x "⟧" => ofPre x

private def resp_le' {a b c d: Pre α} (ac : a ≈ c) (bd: b ≈ d) : a ≤ b ↔ c ≤ d := by
  revert a b c d
  suffices ∀{a b c d: Pre α}, a ≈ c -> b ≈ d -> a ≤ b -> c ≤ d by
    intro a b c d h g
    apply Iff.intro
    apply this
    assumption
    assumption
    apply this
    apply Relation.symm
    assumption
    apply Relation.symm
    assumption
  intro a b c d ac bd ab
  rw [Pre.le_iff_min_eq_left] at *
  apply Pre.trans
  apply Pre.min_congr
  symm; assumption
  symm; assumption
  apply Pre.trans ab
  assumption

instance : LE (FreeLattice α) where
  le := by
    refine Quotient.lift₂ (· ≤ ·) ?_
    intro a b c d ac bd
    ext
    apply resp_le'
    assumption
    assumption

instance : LT (FreeLattice α) where
  lt := by
    refine Quotient.lift₂ (· < ·) ?_
    intro a b c d ac bd
    ext
    show a < b ↔ c < d
    rw [lt_iff_le_and_not_le, lt_iff_le_and_not_le,
      resp_le' ac bd, resp_le' bd ac]

instance : Min (FreeLattice α) where
  min := by
    refine Quotient.lift₂ ?_ ?_
    exact (⟦·.min ·⟧)
    intro a b c d ac bd
    apply Quotient.sound
    apply Pre.min_congr
    assumption
    assumption

instance : Max (FreeLattice α) where
  max := by
    refine Quotient.lift₂ ?_ ?_
    exact (⟦·.max ·⟧)
    intro a b c d ac bd
    apply Quotient.sound
    apply Pre.max_congr
    assumption
    assumption

instance : IsLattice (FreeLattice α) where
  lt_iff_le_and_not_le {a b} := by
    induction a, b using Quotient.ind₂
    apply lt_iff_le_and_not_le (α := Pre α)
  le_refl a := by
    induction a using Quotient.ind
    apply le_refl (α := Pre α)
  le_trans {a b c} := by
    induction a, b using Quotient.ind₂
    induction c using Quotient.ind
    apply le_trans (α := Pre α)
  le_antisymm {a b} h g := by
    induction a, b using Quotient.ind₂
    apply Quotient.sound
    apply Pre.le_antisymm
    assumption
    assumption
  le_max_left {a b} := by
    induction a, b using Quotient.ind₂
    apply Pre.le_max_left
  le_max_right {a b} := by
    induction a, b using Quotient.ind₂
    apply Pre.le_max_right
  max_le {a b k} := by
    induction a, b using Quotient.ind₂
    induction k using Quotient.ind
    apply Pre.max_le
  min_le_left {a b} := by
    induction a, b using Quotient.ind₂
    apply Pre.min_le_left
  min_le_right {a b} := by
    induction a, b using Quotient.ind₂
    apply Pre.min_le_right
  le_min {a b k} := by
    induction a, b using Quotient.ind₂
    induction k using Quotient.ind
    apply Pre.le_min

def ι :  α -> FreeLattice α := (⟦.of ·⟧)

private def Pre.preLift [LatticeOps L] [IsLattice L] (f: α -> L) : Pre α -> L
| .of a => f a
| .min a b => preLift f a ⊓ preLift f b
| .max a b => preLift f a ⊔ preLift f b

private def Pre.lift [LatticeOps L] [IsLattice L] (f: α -> L) : Pre α →o L where
  toFun := Pre.preLift f
  resp_rel {a b} h := by

    sorry
    -- induction h with
    -- | refl => rfl
    -- | trans =>
    --   apply le_trans
    --   assumption
    --   assumption
    -- | le_max_left => apply le_max_left
    -- | le_max_right => apply le_max_right
    -- | max_le => apply max_le <;> assumption
    -- | min_le_left => apply min_le_left
    -- | min_le_right => apply min_le_right
    -- | le_min => apply le_min <;> assumption

private def preLift [LatticeOps L] [IsLattice L] (f: α -> L) : FreeLattice α →o L where
  toFun := by
    refine Quotient.lift (Pre.lift f) ?_
    sorry
  resp_rel := by
    intro a b h
    induction a, b using Quotient.ind₂
    apply (Pre.lift _).resp_rel
    assumption

def lift [LatticeOps L] [IsLattice L] : (α -> L) ≃ (FreeLattice α →o L) where
  toFun := sorry
  invFun f := f ∘ ι
  leftInv := sorry
  rightInv := sorry

def ι_inj : Function.Injective (ι (α := α)) := by
  intro x y h
  -- have ⟨h, g⟩ := Quotient.exact h
  -- cases h
  -- rfl
  sorry

end FreeLattice
