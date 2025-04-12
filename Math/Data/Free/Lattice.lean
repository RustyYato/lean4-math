import Math.Order.Lattice.Basic

section

inductive FreeLattice.Pre (α: Type*) where
| of (a: α)
| max (a b: Pre α)
| min (a b: Pre α)

variable (α: Type*)

inductive FreeLattice.Pre.LE : Pre α -> Pre α -> Prop where
| refl (a: Pre α): LE a a
| trans: LE a b -> LE b c -> LE a c
| le_max_left: LE a (max a b)
| le_max_right: LE b (max a b)
| min_le_left: LE (min a b) a
| min_le_right: LE (min a b) b
| max_le: LE a k -> LE b k -> LE (max a b) k
| le_min: LE k a -> LE k b -> LE k (min a b)

instance : LE (FreeLattice.Pre α) where
  le := FreeLattice.Pre.LE α
instance : LT (FreeLattice.Pre α) where
  lt a b := a ≤ b ∧ ¬b ≤ a
instance : IsLawfulLT (FreeLattice.Pre α) where
  lt_iff_le_and_not_le := Iff.rfl
instance : IsPreOrder (FreeLattice.Pre α) where
  le_refl := FreeLattice.Pre.LE.refl
  le_trans := FreeLattice.Pre.LE.trans

instance FreeLattice.setoid : Setoid (Pre α) := le_setoid (FreeLattice.Pre α)

def FreeLattice (α: Type*) := Quotient (FreeLattice.setoid α)

end

namespace FreeLattice

def ofPre : FreeLattice.Pre α -> FreeLattice α := Quotient.mk _

scoped notation "⟦" x "⟧" => ofPre x

private def resp_le' {a b c d: Pre α} (ac : a ≈ c) (bd: b ≈ d) : a ≤ b ↔ c ≤ d := by
  apply Iff.intro
  intro h
  apply le_trans ac.right
  apply le_trans h bd.left
  intro h
  apply le_trans ac.left
  apply le_trans h bd.right

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
    apply And.intro
    apply FreeLattice.Pre.LE.le_min
    apply flip FreeLattice.Pre.LE.trans
    exact ac.left
    apply FreeLattice.Pre.LE.min_le_left
    apply flip FreeLattice.Pre.LE.trans
    exact bd.left
    apply FreeLattice.Pre.LE.min_le_right
    apply FreeLattice.Pre.LE.le_min
    apply flip FreeLattice.Pre.LE.trans
    exact ac.right
    apply FreeLattice.Pre.LE.min_le_left
    apply flip FreeLattice.Pre.LE.trans
    exact bd.right
    apply FreeLattice.Pre.LE.min_le_right

instance : Max (FreeLattice α) where
  max := by
    refine Quotient.lift₂ ?_ ?_
    exact (⟦·.max ·⟧)
    intro a b c d ac bd
    apply Quotient.sound
    apply And.intro
    apply FreeLattice.Pre.LE.max_le
    apply FreeLattice.Pre.LE.trans
    exact ac.left
    apply FreeLattice.Pre.LE.le_max_left
    apply FreeLattice.Pre.LE.trans
    exact bd.left
    apply FreeLattice.Pre.LE.le_max_right
    apply FreeLattice.Pre.LE.max_le
    apply FreeLattice.Pre.LE.trans
    exact ac.right
    apply FreeLattice.Pre.LE.le_max_left
    apply FreeLattice.Pre.LE.trans
    exact bd.right
    apply FreeLattice.Pre.LE.le_max_right

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
    apply And.intro
    assumption
    assumption
  le_max_left {a b} := by
    induction a, b using Quotient.ind₂
    apply Pre.LE.le_max_left
  le_max_right {a b} := by
    induction a, b using Quotient.ind₂
    apply Pre.LE.le_max_right
  max_le {a b k} := by
    induction a, b using Quotient.ind₂
    induction k using Quotient.ind
    apply Pre.LE.max_le
  min_le_left {a b} := by
    induction a, b using Quotient.ind₂
    apply Pre.LE.min_le_left
  min_le_right {a b} := by
    induction a, b using Quotient.ind₂
    apply Pre.LE.min_le_right
  le_min {a b k} := by
    induction a, b using Quotient.ind₂
    induction k using Quotient.ind
    apply Pre.LE.le_min

def ι :  α -> FreeLattice α := (⟦.of ·⟧)

end FreeLattice
