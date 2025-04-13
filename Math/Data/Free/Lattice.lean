import Math.Order.Lattice.Basic
import Math.Order.Hom.Defs
import Math.Order.Monotone.Defs

section

inductive FreeLattice.Pre (α: Type*) where
| of (a: α)
| max (a b: Pre α)
| min (a b: Pre α)

variable {α: Type*}

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

private def Pre.lift [LatticeOps L] [IsLattice L] (f: α -> L) : Pre α -> L
| .of a => f a
| .min a b => lift f a ⊓ lift f b
| .max a b => lift f a ⊔ lift f b

private def preLift [LatticeOps L] [IsLattice L] (f: α -> L) : FreeLattice α -> L := by
  refine Quotient.lift (Pre.lift f) ?_
  intro a b h
  induction h with
  | refl => rfl
  | symm => symm; assumption
  | trans _ _ ih₀ ih₁ => rw [ih₀, ih₁]
  | max_comm => apply max_comm
  | min_comm => apply min_comm
  | max_assoc => apply max_assoc
  | min_assoc => apply min_assoc
  | max_min => apply max_min_self
  | min_max => apply min_max_self
  | min_congr =>
    show _ ⊓ _ = _ ⊓ _
    congr
  | max_congr =>
    show _ ⊔ _ = _ ⊔ _
    congr

def lift [LatticeOps L] [IsLattice L] : (α -> L) ≃ (FreeLattice α →⊓⊔ L) where
  toFun f := {
    toFun := preLift f
    map_min a b := by
      induction a, b using Quotient.ind₂
      rfl
    map_max a b := by
      induction a, b using Quotient.ind₂
      rfl
  }
  invFun f := f ∘ ι
  leftInv x := rfl
  rightInv f := by
    apply DFunLike.ext
    intro x
    induction x using Quotient.ind with | _ x =>
    show FreeLattice.Pre.lift (f ∘ ι) x = f ⟦x⟧
    induction x with
    | of => rfl
    | max _ _ ih₀ ih₁ =>
      show Pre.lift _ _ ⊔ Pre.lift _ _ = f (⟦_⟧ ⊔ ⟦_⟧)
      rw [ih₀, ih₁, map_max]
    | min _ _ ih₀ ih₁ =>
      show Pre.lift _ _ ⊓ Pre.lift _ _ = f (⟦_⟧ ⊓ ⟦_⟧)
      rw [ih₀, ih₁, map_min]

def apply_lift_ι [LatticeOps L] [IsLattice L] (f: α -> L) : lift f (ι a) = f a := rfl

def ι_inj : Function.Injective (ι (α := α)) := by
  intro x y h
  classical
  let f := lift (fun z => if x = z then 0 else 1)
  have : f (ι x) = 0 := by rw [apply_lift_ι, if_pos rfl]
  rw [h, apply_lift_ι] at this
  split at this; assumption
  contradiction

-- private def IsInfinite.gen (a b c: α) : Nat -> FreeLattice α
-- | 0 => ι a
-- | n + 1 => ι a ⊔ (ι b ⊓ (ι c ⊔ (ι a ⊓ (ι b ⊔ (ι c ⊓ (gen a b c n))))))

-- def IsInfinite.lt_succ
--    (x y z: α) (xy: x ≠ y) (yz: y ≠ z) (xz: x ≠ z) (n: Nat) :
--   gen x y z n < gen x y z (n + 1) := by
--   rw [FreeLattice.IsInfinite.gen]
--   generalize FreeLattice.IsInfinite.gen x y z n = p

--   clear n
--   apply lt_of_le_of_ne
--   · let a := ι z ⊓ p
--     let b := ι y ⊔ a
--     let c := ι x ⊓ b
--     let d := ι z ⊔ c
--     let e := ι y ⊓ d
--     let f := ι x ⊔ e
--     show p ≤ f
--     have a_le_p : a ≤ p := by apply min_le_right
--     have : p ≤ b := by
--       show p ≤ _ ⊔ a
--       apply flip le_trans
--       apply le_max_right




--       sorry

--     sorry



--   repeat sorry


-- protected def IsInfinite.Monotone (a b c: α) (ab: a ≠ b) (bc: b ≠ c) (ac: a ≠ c) : Monotone (IsInfinite.gen a b c) := by
--   intro n m h
--   induction n generalizing m with
--   | zero =>
--     clear h
--     induction m with
--     | zero => rfl
--     | succ m ih =>
--       apply le_trans
--       assumption
--       apply le_of_lt
--       apply IsInfinite.lt_succ <;> assumption
--   | succ n ih =>
--     cases m with
--     | zero => contradiction
--     | succ m =>
--     unfold gen
--     repeat first|apply max_le_max_left|apply min_le_min_left
--     apply ih
--     apply Nat.le_of_succ_le_succ
--     assumption

-- protected def IsInfinite.StrictMonotone (a b c: α) (ab: a ≠ b) (bc: b ≠ c) (ac: a ≠ c) : StrictMonotone (IsInfinite.gen a b c) := by
--   intro n m h
--   rw [←Nat.succ_le] at h
--   cases h
--   apply IsInfinite.lt_succ <;> assumption
--   apply lt_of_lt_of_le
--   apply IsInfinite.lt_succ <;> assumption
--   apply IsInfinite.Monotone
--   assumption
--   assumption
--   assumption
--   apply le_trans
--   assumption
--   apply Nat.le_succ

-- def IsInfinite (a b c: α) (ab: a ≠ b) (bc: b ≠ c) (ac: a ≠ c) : (Fin n ≃ FreeLattice α) -> False := by
--   intro h

--   sorry

end FreeLattice
