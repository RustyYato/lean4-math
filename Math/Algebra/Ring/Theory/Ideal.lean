import Math.Algebra.Ring.Theory.Subring
import Math.Order.Atom.Basic

namespace Ring

structure LeftIdeal (R: Ring α) extends AddSubgroup R where
  mem_mul_left: ∀(r: R) {x}, x ∈ carrier -> r * x ∈ carrier

structure RightIdeal (R: Ring α) extends AddSubgroup R where
  mem_mul_right: ∀(r: R) {x}, x ∈ carrier -> x * r ∈ carrier

structure Ideal (R: Ring α) extends LeftIdeal R, RightIdeal R where

instance : SetLike (LeftIdeal R) R where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : SetLike (RightIdeal R) R where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : SetLike (Ideal R) R where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsAddSubgroup (LeftIdeal R) where
  mem_add i := i.mem_add
  mem_neg i := i.mem_neg
  mem_zero i := i.mem_zero

instance : IsAddSubgroup (RightIdeal R) where
  mem_add i := i.mem_add
  mem_neg i := i.mem_neg
  mem_zero i := i.mem_zero

instance : IsAddSubgroup (Ideal R) where
  mem_add i := i.mem_add
  mem_neg i := i.mem_neg
  mem_zero i := i.mem_zero

instance : IsMulMem (LeftIdeal R) where
  mem_mul i := by
    intro a b ha hb
    apply i.mem_mul_left
    assumption

instance : IsMulMem (RightIdeal R) where
  mem_mul i := by
    intro a b ha hb
    apply i.mem_mul_right
    assumption

instance : IsMulMem (Ideal R) where
  mem_mul i := by
    intro a b ha hb
    apply i.mem_mul_right
    assumption

def Ideal.zero (R: Ring α) : Ideal R where
  carrier := {0}
  mem_zero := rfl
  mem_add := by
    rintro _ _ rfl rfl
    apply add_zero
  mem_neg := by
    rintro _ rfl
    apply neg_zero
  mem_mul_left := by
    rintro r _ rfl
    apply mul_zero
  mem_mul_right := by
    rintro r _ rfl
    apply zero_mul

def Ideal.univ (R: Ring α) : Ideal R where
  carrier := ⊤
  mem_zero := True.intro
  mem_add _ _ := True.intro
  mem_neg _ := True.intro
  mem_mul_left _ _ _ := True.intro
  mem_mul_right _ _ _ := True.intro

instance (R: Ring α) : Membership R (LeftIdeal R) where
  mem i x := x ∈ i.carrier

instance (R: Ring α) : Membership R (RightIdeal R) where
  mem i x := x ∈ i.carrier

instance (R: Ring α) : Membership R (Ideal R) where
  mem i x := x ∈ i.carrier

@[ext]
def LeftIdeal.ext {a b: LeftIdeal R} : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

@[ext]
def RightIdeal.ext {a b: RightIdeal R} : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

@[ext]
def Ideal.ext {a b: Ideal R} : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

section Ideal.Lattice

instance : LE (Ideal R) where
  le a b := a.carrier ⊆ b.carrier

instance : LT (Ideal R) where
  lt a b := a ≤ b ∧ ¬b ≤ a

inductive Ideal.Generate (R: Ring α) (U: Set R) : R -> Prop where
| of (x: R) : x ∈ U -> Generate R U x
| zero : Generate R U 0
| add (a b: R) : Generate R U a -> Generate R U b -> Generate R U (a + b)
| neg (a: R) : Generate R U a -> Generate R U (-a)
| mul_left (r: R) (x: R) : Generate R U x -> Generate R U (r * x)
| mul_right (r: R) (x: R) : Generate R U x -> Generate R U (x * r)

def toIdeal (R: Ring α) (U: Set R) : Ideal R where
  carrier := Set.mk (Ideal.Generate R U)
  mem_zero := Ideal.Generate.zero
  mem_add := Ideal.Generate.add _ _
  mem_neg := Ideal.Generate.neg _
  mem_mul_left _ _ := Ideal.Generate.mul_left _ _
  mem_mul_right _ _ := Ideal.Generate.mul_right _ _

def Ideal.oemb : Ideal R ↪o Set R where
  toFun a := a.carrier
  resp_rel := Iff.rfl
  inj' := SetLike.coe_inj

instance : IsLawfulLT (Ideal R) := ⟨Iff.rfl⟩

instance : IsPartialOrder (Ideal R) :=
  Ideal.oemb.inducedIsPartialOrder'

def Ideal.giGenerate (R: Ring α) : @GaloisInsertion (Set R) (Ideal R) _ _ R.toIdeal (fun x => x.carrier) where
  choice S hS := {
    carrier := S
    mem_add := by
      intro a b ha hb
      apply hS
      apply Generate.add
      apply Generate.of
      assumption
      apply Generate.of
      assumption
    mem_neg := by
      intro a ha
      apply hS
      apply Generate.neg
      apply Generate.of
      assumption
    mem_zero := by
      apply hS
      apply Generate.zero
    mem_mul_left := by
      intro _ _ ha
      apply hS
      apply Generate.mul_left
      apply Generate.of
      assumption
    mem_mul_right := by
      intro _ _ ha
      apply hS
      apply Generate.mul_right
      apply Generate.of
      assumption
  }
  choice_eq := by
    intro S h
    simp
    apply le_antisymm
    apply Generate.of
    apply h
  gc := by
    intro a b
    dsimp
    apply Iff.intro
    · intro h x x_in_a
      exact h x (Ideal.Generate.of _ x_in_a)
    · intro h x hx
      induction hx with
      | of =>
        apply h
        assumption
      | zero => apply mem_zero b
      | add => apply mem_add b <;> assumption
      | neg => apply mem_neg b <;> assumption
      | mul_left => apply b.mem_mul_left <;> assumption
      | mul_right => apply b.mem_mul_right <;> assumption
  le_l_u := by
    intro x r hx
    apply Ideal.Generate.of
    assumption

instance (R: Ring α) : CompleteLattice (Ideal R) := {
  (Ideal.giGenerate R).liftCompleteLattice with
  bot := Ideal.zero R
  bot_le := by
    rintro x h rfl
    apply mem_zero x
}

end Ideal.Lattice

section LeftIdeal.Lattice

instance : LE (LeftIdeal R) where
  le a b := a.carrier ⊆ b.carrier

instance : LT (LeftIdeal R) where
  lt a b := a ≤ b ∧ ¬b ≤ a

inductive LeftIdeal.Generate (R: Ring α) (U: Set R) : R -> Prop where
| of (x: R) : x ∈ U -> Generate R U x
| zero : Generate R U 0
| add (a b: R) : Generate R U a -> Generate R U b -> Generate R U (a + b)
| neg (a: R) : Generate R U a -> Generate R U (-a)
| mul_left (r: R) (x: R) : Generate R U x -> Generate R U (r * x)

def toLeftIdeal (R: Ring α) (U: Set R) : LeftIdeal R where
  carrier := Set.mk (LeftIdeal.Generate R U)
  mem_zero := LeftIdeal.Generate.zero
  mem_add := LeftIdeal.Generate.add _ _
  mem_neg := LeftIdeal.Generate.neg _
  mem_mul_left _ _ := LeftIdeal.Generate.mul_left _ _

def LeftIdeal.oemb : LeftIdeal R ↪o Set R where
  toFun a := a.carrier
  resp_rel := Iff.rfl
  inj' := SetLike.coe_inj

instance : IsLawfulLT (LeftIdeal R) := ⟨Iff.rfl⟩

instance : IsPartialOrder (LeftIdeal R) :=
  LeftIdeal.oemb.inducedIsPartialOrder'

def LeftIdeal.giGenerate (R: Ring α) : @GaloisInsertion (Set R) (LeftIdeal R) _ _ R.toLeftIdeal (fun x => x.carrier) where
  choice S hS := {
    carrier := S
    mem_add := by
      intro a b ha hb
      apply hS
      apply Generate.add
      apply Generate.of
      assumption
      apply Generate.of
      assumption
    mem_neg := by
      intro a ha
      apply hS
      apply Generate.neg
      apply Generate.of
      assumption
    mem_zero := by
      apply hS
      apply Generate.zero
    mem_mul_left := by
      intro _ _ ha
      apply hS
      apply Generate.mul_left
      apply Generate.of
      assumption
  }
  choice_eq := by
    intro S h
    simp
    apply le_antisymm
    apply Generate.of
    apply h
  gc := by
    intro a b
    dsimp
    apply Iff.intro
    · intro h x x_in_a
      exact h x (LeftIdeal.Generate.of _ x_in_a)
    · intro h x hx
      induction hx with
      | of =>
        apply h
        assumption
      | zero => apply mem_zero b
      | add => apply mem_add b <;> assumption
      | neg => apply mem_neg b <;> assumption
      | mul_left => apply b.mem_mul_left <;> assumption
  le_l_u := by
    intro x r hx
    apply LeftIdeal.Generate.of
    assumption

instance (R: Ring α) : CompleteLattice (LeftIdeal R) := {
  (LeftIdeal.giGenerate R).liftCompleteLattice with
  bot := (Ideal.zero R).toLeftIdeal
  bot_le := by
    rintro x h rfl
    apply mem_zero x
}

end LeftIdeal.Lattice

section RightIdeal.Lattice

instance : LE (RightIdeal R) where
  le a b := a.carrier ⊆ b.carrier

instance : LT (RightIdeal R) where
  lt a b := a ≤ b ∧ ¬b ≤ a

inductive RightIdeal.Generate (R: Ring α) (U: Set R) : R -> Prop where
| of (x: R) : x ∈ U -> Generate R U x
| zero : Generate R U 0
| add (a b: R) : Generate R U a -> Generate R U b -> Generate R U (a + b)
| neg (a: R) : Generate R U a -> Generate R U (-a)
| mul_right (r: R) (x: R) : Generate R U x -> Generate R U (x * r)

def toRightIdeal (R: Ring α) (U: Set R) : RightIdeal R where
  carrier := Set.mk (RightIdeal.Generate R U)
  mem_zero := RightIdeal.Generate.zero
  mem_add := RightIdeal.Generate.add _ _
  mem_neg := RightIdeal.Generate.neg _
  mem_mul_right _ _ := RightIdeal.Generate.mul_right _ _

def RightIdeal.oemb : RightIdeal R ↪o Set R where
  toFun a := a.carrier
  resp_rel := Iff.rfl
  inj' := SetLike.coe_inj

instance : IsLawfulLT (RightIdeal R) := ⟨Iff.rfl⟩

instance : IsPartialOrder (RightIdeal R) :=
  RightIdeal.oemb.inducedIsPartialOrder'

def RightIdeal.giGenerate (R: Ring α) : @GaloisInsertion (Set R) (RightIdeal R) _ _ R.toRightIdeal (fun x => x.carrier) where
  choice S hS := {
    carrier := S
    mem_add := by
      intro a b ha hb
      apply hS
      apply Generate.add
      apply Generate.of
      assumption
      apply Generate.of
      assumption
    mem_neg := by
      intro a ha
      apply hS
      apply Generate.neg
      apply Generate.of
      assumption
    mem_zero := by
      apply hS
      apply Generate.zero
    mem_mul_right := by
      intro _ _ ha
      apply hS
      apply Generate.mul_right
      apply Generate.of
      assumption
  }
  choice_eq := by
    intro S h
    simp
    apply le_antisymm
    apply Generate.of
    apply h
  gc := by
    intro a b
    dsimp
    apply Iff.intro
    · intro h x x_in_a
      exact h x (RightIdeal.Generate.of _ x_in_a)
    · intro h x hx
      induction hx with
      | of =>
        apply h
        assumption
      | zero => apply mem_zero b
      | add => apply mem_add b <;> assumption
      | neg => apply mem_neg b <;> assumption
      | mul_right => apply b.mem_mul_right <;> assumption
  le_l_u := by
    intro x r hx
    apply RightIdeal.Generate.of
    assumption

instance (R: Ring α) : CompleteLattice (RightIdeal R) := {
  (RightIdeal.giGenerate R).liftCompleteLattice with
  bot := (Ideal.zero R).toRightIdeal
  bot_le := by
    rintro x h rfl
    apply mem_zero x
}

end RightIdeal.Lattice

def LeftIdeal.eq_univ_of_mem_unit {R: Ring α} (i: LeftIdeal R) (u: Units R) : u.val ∈ i.carrier -> i = ⊤ := by
  intro h
  ext r
  apply Iff.intro
  intro h; trivial
  intro h; clear h
  have : (r * u.inv) * u.val ∈ i.carrier := by
    apply i.mem_mul_left
    assumption
  rw [mul_assoc, u.inv_mul_val, mul_one] at this
  assumption

def RightIdeal.eq_univ_of_mem_unit {R: Ring α} (i: RightIdeal R) (u: Units R) : u.val ∈ i.carrier -> i = ⊤ := by
  intro h
  ext r
  apply Iff.intro
  intro h; trivial
  intro h; clear h
  have : u.val * (u.inv * r) ∈ i.carrier := by
    apply i.mem_mul_right
    assumption
  rw [←mul_assoc, u.val_mul_inv, one_mul] at this
  assumption

def Ideal.eq_univ_of_mem_unit {R: Ring α} (i: Ideal R) (u: Units R) : u.val ∈ i.carrier -> i = ⊤ := by
  intro h
  ext r
  apply Iff.intro
  intro h; trivial
  intro h; clear h
  have : u.val * (u.inv * r) ∈ i.carrier := by
    apply i.mem_mul_right
    assumption
  rw [←mul_assoc, u.val_mul_inv, one_mul] at this
  assumption

def Ideal.Quot (i: Ideal R) : Type _ := Quotient (AddSubgroup.setoid i.toAddSubgroup)

@[cases_eliminator]
private def Ideal.Quot.ind
  {i: Ideal R} {motive: i.Quot -> Prop} : (mk: ∀x: R, motive (Quotient.mk _ x)) -> ∀q, motive q := Quotient.ind

def Ideal.toRing (i: Ideal R) : Ring i.Quot := by
  apply Ring.ofMinimalAxioms
  case zero => exact Quotient.mk _ 0
  case one => exact Quotient.mk _ 1
  case neg =>
    apply Quotient.lift (fun a => Quotient.mk _ (-a))
    intro a b eq
    apply Quotient.sound
    show _ - _ ∈ i
    rw [neg_sub_neg, ←neg_sub]
    apply mem_neg
    assumption
  case add =>
    apply Quotient.lift₂ (fun a b => Quotient.mk _ (a + b))
    intro a b c d ac bd
    apply Quotient.sound
    show _ - _ ∈ i
    rw [sub_eq_add_neg, neg_add_rev, add_assoc, ←add_assoc b,
      ←sub_eq_add_neg b, add_comm _ (-c), ←add_assoc,
      ←sub_eq_add_neg]
    apply mem_add
    assumption
    assumption
  case mul =>
    apply Quotient.lift₂ (fun a b => Quotient.mk _ (a * b))
    intro a b c d ac bd
    apply Quotient.sound
    show _ - _ ∈ _
    rw [←add_zero (_ - _), ←add_neg_cancel (a * d), sub_add_assoc,
      ←add_assoc (-_), add_comm _ (a * d), add_comm (_ + _),
      ←add_assoc, ←sub_eq_add_neg, ←sub_eq_add_neg,
      ←mul_sub, ←sub_mul]
    apply mem_add
    apply i.mem_mul_left
    assumption
    apply i.mem_mul_right
    assumption

  case add_comm =>
    intro a b
    cases a with | mk a =>
    cases b with | mk b =>
    apply Quotient.sound
    rw [add_comm]
  case add_assoc =>
    intro a b c
    cases a with | mk a =>
    cases b with | mk b =>
    cases c with | mk c =>
    apply Quotient.sound
    rw [add_assoc]
  case mul_assoc =>
    intro a b c
    cases a with | mk a =>
    cases b with | mk b =>
    cases c with | mk c =>
    apply Quotient.sound
    rw [mul_assoc]
  case zero_add =>
    intro a
    cases a with | mk a =>
    apply Quotient.sound
    rw [zero_add]
  case neg_add_cancel =>
    intro a
    cases a with | mk a =>
    apply Quotient.sound
    rw [neg_add_cancel]
  case one_mul =>
    intro a
    cases a with | mk a =>
    apply Quotient.sound
    rw [one_mul]
  case mul_one =>
    intro a
    cases a with | mk a =>
    apply Quotient.sound
    rw [mul_one]
  case mul_add =>
    intro a b c
    cases a with | mk a =>
    cases b with | mk b =>
    cases c with | mk c =>
    apply Quotient.sound
    rw [mul_add]
  case add_mul =>
    intro a b c
    cases a with | mk a =>
    cases b with | mk b =>
    cases c with | mk c =>
    apply Quotient.sound
    rw [add_mul]

-- the canonical projection into the subring generated by the ideal
def Ideal.mkQuot (i: Ideal R) : R →+* i.toRing where
  toFun := Quotient.mk _
  map_zero := rfl
  map_one := rfl
  map_add := rfl
  map_mul := rfl

def Ideal.mkQuot_surj (i: Ideal R) : Function.Surjective i.mkQuot := by
  intro a
  have ⟨x, eq⟩ := Quotient.exists_rep a
  exists x
  rw [←eq]
  rfl

-- the kernel (preimage of 0) of a ring homomorphism generates an ideal
def Ideal.kernel {S R: Ring α} (f: S →+* R) : Ideal S where
  carrier := Set.preimage {0} f
  mem_zero := map_zero _
  mem_add := by
    intro a b ha hb
    rw [Set.mem_preimage, map_add, ha, hb, add_zero]
    rfl
  mem_neg := by
    intro a ha
    rw [Set.mem_preimage, map_neg, ha, neg_zero]
    rfl
  mem_mul_left := by
    intro a b hb
    rw [Set.mem_preimage, map_mul, hb, mul_zero]
    rfl
  mem_mul_right := by
    intro a b hb
    rw [Set.mem_preimage, map_mul, hb, zero_mul]
    rfl

-- the kernel of Ideal.mkQuot is exactly the ideal itself
def Ideal.mkQuot_kernel (i: Ideal R) : i.carrier = Set.preimage {0} i.mkQuot := by
  ext x
  rw [Set.mem_preimage, Set.mem_singleton]
  apply Iff.intro
  intro h
  apply Quotient.sound
  show _ - _ ∈ i
  rw [sub_zero]
  assumption
  intro h
  have : _ - _ ∈ i := Quotient.exact h
  rw [sub_zero] at this
  assumption

def Ideal.isMaximal (i: Ideal R): Prop := IsCoatom i

end Ring
