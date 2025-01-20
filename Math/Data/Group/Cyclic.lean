import Math.Data.Group.Basic

instance {n m: Nat} [NeZero n] [NeZero m] : NeZero (n * m) where
  out := by
    intro h
    cases Nat.mul_eq_zero.mp h <;> (rename_i h; exact NeZero.ne _ h)

def fin_inverse (x: Fin n): Fin n :=
  Fin.mk ((n - x.val) % n) (Nat.mod_lt _ (Nat.zero_lt_of_ne_zero (by
    intro h
    cases h
    exact x.elim0)))

namespace Group

-- a cyclic group with n elements
def NatAddMod (n: Nat) (h: n ≠ 0 := by exact NeZero.ne _) : Group where
  ty := Fin n
  one' := ⟨0, Nat.zero_lt_of_ne_zero h⟩
  mul' a b := a + b
  inv' := fin_inverse
  one_mul' x := by
    apply Fin.val_inj.mp
    show ((0: Nat) + x.val) % _ = x.val
    rw [Nat.zero_add, Nat.mod_eq_of_lt x.isLt]
  mul_assoc' := by
    intro a b c
    simp [Fin.add_def]
    rw [Nat.add_assoc]
  inv_mul' := by
    intro a
    simp [Fin.add_def, fin_inverse]

def IsoClass.Cyclic (n: Nat) [NeZero n] := ⟦NatAddMod n⟧

instance : Subsingleton (NatAddMod 1).ty :=
  inferInstanceAs (Subsingleton (Fin 1))

def cyclic_one_eq_trivial : IsoClass.Cyclic 1 = 1 := by
  apply Quotient.sound
  apply eq_trivial_of_subsingleton

def sub_cyclic (hn: n ≠ 0) (g: Group) (h: g ⊆ NatAddMod n hn) : ∃m: Nat, g ≈ NatAddMod m.succ := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero =>
      dsimp at h
      obtain ⟨h⟩ := h
      exists 0
      refine ⟨?_⟩
      apply Isomorphsism.mk _ _ _ _
      apply Equiv.mk _ _ _ _
      intro
      exact 1
      intro
      exact 1
      intro x
      dsimp
      apply h.inj
      apply Subsingleton.allEq _ _
      intro
      apply Subsingleton.allEq _ _
      rfl
      intro x
      dsimp
      rw [inv_one]
      intro x y
      dsimp
      rw [mul_one]
    | succ n =>
      obtain ⟨h⟩ := h
      by_cases hf:Function.Surjective h.toFun
      · exists (n + 1)
        have ⟨eq, spec⟩  := Equiv.ofBij ⟨h.inj, hf⟩
        replace spec : eq.toFun = h.toFun := spec
        refine ⟨?_⟩
        apply Isomorphsism.mk eq
        rw [spec, h.resp_one]
        intro x
        rw [spec, h.resp_inv]
        intro x y
        rw [spec, h.resp_mul]
      · apply ih (nomatch ·)
        replace hf := Classical.not_forall.mp hf
        obtain ⟨x, hf⟩ := hf
        replace hf: ∀y, h.toFun y ≠ x := not_exists.mp hf
        refine ⟨?_⟩
        apply SubgroupEmbedding.mk _ _ _ _
        apply Fin.embed_reduce h.toEmbedding x hf
        unfold Fin.embed_reduce
        dsimp

        sorry
end Group
