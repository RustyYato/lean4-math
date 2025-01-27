 import Math.Data.Group.Basic

-- has one swap
private def has_one_swap (a b: Fin n ≃ Fin n): Prop :=
  ∃x y, x ≠ y ∧ a x = b y ∧ a y = b x ∧ ∀z, z ≠ x -> z ≠ y -> a z = b z

def has_one_swap.symm (a b: Fin n ≃ Fin n) :
  has_one_swap a b -> has_one_swap b a := by
  intro ⟨x, y, ne, h₀, h₁, g⟩
  refine ⟨x, y, ?_, ?_, ?_, ?_⟩
  assumption
  symm; assumption
  symm; assumption
  intro z hx hy
  symm; apply g
  assumption
  assumption

private
inductive even_perm : Fin n ≃ Fin n -> Prop where
| refl : even_perm .refl
| swap_swap a b c : has_one_swap a b -> has_one_swap b c -> even_perm c -> even_perm a

namespace Group

-- the symmetric group of all permutations
def EvenPermuatation (n: Nat) : Group where
  ty := { x: (Fin n) ≃ (Fin n) // even_perm x }
  one' := by
    refine ⟨Equiv.refl, ?_⟩
    apply even_perm.refl
  mul' := by
    intro ⟨A, aperm⟩ ⟨B, bperm⟩
    refine ⟨A.trans B ,?_⟩
    induction aperm with
    | refl => assumption
    | swap_swap  a b c ab bc ceven ih =>
      replace ⟨abx, aby, abne, axby, aybx, ab⟩ := ab
      replace ⟨bcx, bcy, bcne, bxcy, bycx, bc⟩ := bc
      apply even_perm.swap_swap (a.trans B) (b.trans B) (c.trans B)
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        exact abx
        exact aby
        assumption
        show B (a abx) = B (b aby)
        rw [axby]
        show B (a aby) = B (b abx)
        rw [aybx]
        intro z zx zy
        show B (a _) = B (b _)
        rw [ab z]
        assumption
        assumption
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        exact bcx
        exact bcy
        assumption
        show B (b bcx) = B (c bcy)
        rw [bxcy]
        show B (b bcy) = B (c bcx)
        rw [bycx]
        intro z zx zy
        show B (b _) = B (c _)
        rw [bc z]
        assumption
        assumption
      exact ih
  inv' := by
    intro ⟨A, aperm⟩
    refine ⟨A.symm, ?_⟩
    induction aperm with
    | refl => apply even_perm.refl
    | swap_swap a b c ab bc ceven ih =>
      replace ⟨abx, aby, abne, axby, aybx, ab⟩ := ab
      replace ⟨bcx, bcy, bcne, bxcy, bycx, bc⟩ := bc
      apply even_perm.swap_swap a.symm b.symm c.symm
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        exact (a abx)
        exact (a aby)
        intro h
        have := a.toFun_inj h
        contradiction
        rw [a.coe_symm, aybx, b.coe_symm]
        rw [a.coe_symm, axby, b.coe_symm]
        intro z hx hy
        have hx' : a.symm z ≠ abx := by
          intro h
          rw [←h, a.symm_coe] at hx; contradiction
        have hy' : a.symm z ≠ aby := by
          intro h
          rw [←h, a.symm_coe] at hy; contradiction
        rw [←a.symm_coe z]
        conv => { rhs; rw [ab _ hx' hy'] }
        rw [a.coe_symm, b.coe_symm]
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        exact (b bcx)
        exact (b bcy)
        intro h
        have := b.toFun_inj h
        contradiction
        rw [b.coe_symm, bycx, c.coe_symm]
        rw [b.coe_symm, bxcy, c.coe_symm]
        intro z hx hy
        have hx' : b.symm z ≠ bcx := by
          intro h
          rw [←h, b.symm_coe] at hx; contradiction
        have hy' : b.symm z ≠ bcy := by
          intro h
          rw [←h, b.symm_coe] at hy; contradiction
        rw [←b.symm_coe z]
        conv => { rhs; rw [bc _ hx' hy'] }
        rw [b.coe_symm, c.coe_symm]
      assumption
  one_mul' := by
    intro ⟨a, aperm⟩
    dsimp
    congr
  mul_assoc' := by
    intro ⟨a, aperm⟩ ⟨b, bperm⟩ ⟨c, cperm⟩
    dsimp
    congr 1
  inv_mul' := by
    intro ⟨a, aperm⟩
    dsimp
    congr
    apply Equiv.symm_trans_self

def IsoClass.Alternating (n: Nat) : IsoClass := ⟦EvenPermuatation n⟧

private def to_perm {g: Group} (a: g.ty) : g.ty ≃ g.ty where
  toFun b := b * a
  invFun b := b * a⁻¹
  leftInv := by
    intro x
    dsimp
    rw [mul_assoc, mul_inv_cancel, mul_one]
  rightInv := by
    intro b
    dsimp
    rw [mul_assoc, inv_mul_cancel, mul_one]

def even_perm_3_simple : (EvenPermuatation 3).IsSimple := by
  intro x ⟨nsub⟩
  sorry

private
def count_inversions (eqv: Fin n ≃ Fin n) := Fin.sum (n := n) fun x =>
  Fin.sum (n := x.val) fun y => if eqv x < eqv (y.castLE (Nat.le_of_lt x.isLt)) then 1 else 0

instance (eqv: Fin n ≃ Fin n) : Decidable (even_perm eqv) :=
  if h:count_inversions eqv % 2 = 0 then
    .isTrue <| by
      induction n using Nat.strongRecOn with
      | ind n ih =>
      cases n with
      | zero =>
        have : Subsingleton (Fin 0 ≃ Fin 0) := Fintype.subsingleton (by decide)
        rw [this.allEq eqv]
        apply even_perm.refl
      | succ n =>
      cases n with
      | zero =>
        have : Subsingleton (Fin 1 ≃ Fin 1) := Fintype.subsingleton (by decide)
        rw [this.allEq eqv]
        apply even_perm.refl
      | succ n =>
        replace h := Nat.dvd_of_mod_eq_zero h
        rw [Group.count_inversions, Fin.sum_pop] at h

        let x := eqv.symm (Fin.last _)
        have := Equiv.swap (Fin.last n)
        sorry
  else
    .isFalse sorry

end Group
