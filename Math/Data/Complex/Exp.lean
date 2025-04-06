import Math.Data.Complex.MetricSpace
import Math.Topology.Filter.Defs
import Math.Data.Fintype.Algebra
import Math.Data.Nat.Factorial
import Math.Topology.Separable.Basic
import Math.Data.Complex.Completion

def fact_nonzero [SemiringOps α] [IsSemiring α] [IsAddCancel α] [HasChar α 0]
  (n: ℕ) : (n !: α) ≠ 0 := by
  intro h
  rw [←natCast_zero] at h
  replace h := HasChar.natCast_inj (α := α) h
  have := fact_pos n
  rw [h] at this
  contradiction

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply fact_nonzero)

instance : HasChar ℚ[i] 0 := HasChar.of_ring_emb {
  (algebraMap: ℚ →+* _) with
  inj' := Rsqrtd.coe_inj
}

def reduce_grat (x: ℚ[i]) : ℚ[i] := ⟨x.a.reduce, x.b.reduce⟩

namespace ℝi

def exp_seq (f: CauchySeq ℚ[i]) (i: ℕ) : ℚ[i] :=
  reduce_grat <| ∑j: Fin (i + 1), ((f i) ^ j.val /? j.val !)

def exp.spec (a b: CauchySeq ℚ[i]) (h: a ≈ b) :
  CauchySeq.is_cauchy_equiv (exp_seq a) (exp_seq b) := by
  intro ε εpos
  replace ⟨δ, h⟩ := h ε εpos
  exists δ
  intro n m hn hm
  replace h := h n m hn hm
  simp at h
  unfold exp_seq
  sorry

def exp : ℝi -> ℝi := by
  refine Quotient.lift ?_ ?_
  intro a
  exact Cauchy.ofSeq {
    seq := exp_seq a
    is_cacuhy := by
      apply exp.spec
      rfl
  }
  intro a b h
  apply Quotient.sound
  apply exp.spec
  assumption

end ℝi

namespace Complex

def exp (x: ℂ) : ℂ := equivℂ (equivℂ.symm x).exp

end Complex

-- noncomputable section

-- namespace Complex

-- def expTaylor (x: ℂ) (n: ℕ) : ℂ :=
--   ∑i: Fin (n+1), x ^ i.val /? (i.val !: ℂ)

-- def expFilter (x: ℂ) : Filter ℂ := Filter.of_seq (expTaylor x)
-- def expFilterNeBot (x: ℂ) : expFilter x ≠ ⊥ := by
--   suffices ⊥ ∉ expFilter x by
--     intro h
--     apply this
--     rw [h]; trivial
--   intro ⟨n, h⟩
--   replace h := Set.sub_empty _ h
--   suffices (Filter.tail x.expTaylor n).Nonempty by
--     rw [h] at this
--     nomatch this
--   exists expTaylor x n
--   clear h
--   unfold Filter.tail
--   rw [Set.mem_image]
--   exists n
--   apply And.intro
--   rw [Set.mem_Ici]
--   rfl

-- instance : FilterBase.NeBot (expFilter x) where
--   ne := expFilterNeBot _

-- def exp (x: ℂ) : ℂ := Topology.lim (α := ℂ) (expFilter x)

-- instance : Topology.T2 ℂ where
--   proof := by
--     intro a b h f ha hb
--     let d := dist a b /? 2
--     let Sa := Ball a d
--     let Sb := Ball b d
--     suffices Sa ⊓ Sb = ∅ by
--       have hf := f.closed_min (ha Sa ?_) (hb Sb ?_)
--       rw [this] at hf
--       intro x hx
--       apply f.closed_upward
--       assumption
--       apply Set.empty_sub
--       · rw [Topology.mem_nhds]
--         refine ⟨Sa, Set.sub_refl _, ?_, ?_⟩
--         apply Topology.IsOpen.Ball
--         rw [mem_ball]
--         rw [dist_self]
--         show 0 < dist a b /? 2
--         rw [div?_eq_mul_inv?]
--         apply mul_pos
--         apply dist_pos
--         assumption
--         apply inv?_pos
--         exact two_pos
--       · rw [Topology.mem_nhds]
--         refine ⟨Sb, Set.sub_refl _, ?_, ?_⟩
--         apply Topology.IsOpen.Ball
--         rw [mem_ball]
--         rw [dist_self]
--         show 0 < dist a b /? 2
--         rw [div?_eq_mul_inv?]
--         apply mul_pos
--         apply dist_pos
--         assumption
--         apply inv?_pos
--         exact two_pos
--     apply Set.ext_empty
--     intro x ⟨ha, hb⟩
--     rw [mem_ball] at ha hb
--     rw [dist_comm] at hb
--     have : dist a b ≤ dist a x + dist x b := by apply dist_triangle
--     have : dist a b < dist a b /? 2 + dist a b /? 2 := lt_of_le_of_lt this (add_lt_add _ _ _ _ ha hb)
--     rw [add_half] at this
--     exact lt_irrefl this

-- def exp_zero : exp 0 = 1 := by
--   apply Topology.lim_eq'
--   intro S Sopen b_in_S x hx
--   refine ⟨0, ?_⟩
--   unfold Filter.tail
--   intro y hy
--   rw [Set.mem_image] at hy
--   obtain ⟨n, hn, rfl⟩ := hy
--   unfold expTaylor
--   rw [Set.mem_Ici] at hn
--   clear hn
--   rw [sum_succ', sum_eq_zero]
--   simp
--   conv => { arg 2; arg 2; rw [natCast_one] }
--   rw [div?_one]
--   apply hx
--   assumption
--   intro i
--   rw (occs := [1]) [Fin.val_succ, npow_succ, mul_zero, div?_eq_mul_inv?, zero_mul]

-- def exp_add (a b: ℂ) : exp (a + b) = exp a * exp b := by
--   apply Topology.lim_eq'
--   intro S hS hx s hs
--   replace hs : S ≤ s := hs
--   replace hx' := hs _ hx
--   have ⟨δ, δpos, ball_sub⟩ := hS _ hx
--   sorry

-- instance : Topology.IsContinuous exp where
--   isOpen_preimage := by
--     intro S Sopen x hx
--     replace hx : exp x ∈ S := hx
--     have ⟨ε, εpos, ball⟩ := Sopen _ hx
--     refine ⟨ε, ?_, ?_⟩
--     sorry
--     intro y hy
--     show exp y ∈ S
--     apply ball (exp y)
--     rw [mem_ball] at *
--     sorry

-- end Complex

-- end
