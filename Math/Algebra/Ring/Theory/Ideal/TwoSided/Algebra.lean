import Math.Algebra.Ring.Theory.Ideal.TwoSided.Basic
import Init.Data.Fin.Basic
import Math.Data.List.Algebra
import Math.Algebra.AddGroupWithOne.SetLike.Basic
import Math.Algebra.Ring.Basic

namespace Ideal

variable [RingOps α] [IsRing α]

instance (i: Ideal α) : IsAddGroup i := inferInstance

instance : Add (Ideal α) where
  add a b := {
    carrier := Set.mk fun z => ∃x: α × α, x.fst ∈ a ∧ x.snd ∈ b ∧ x.fst + x.snd = z
    mem_zero := ⟨(0, 0), mem_zero _, mem_zero _, add_zero _⟩
    mem_neg := by
      rintro _ ⟨⟨x, y⟩, hx, hy, rfl⟩
      refine ⟨(-x, -y), ?_, ?_, ?_⟩
      apply mem_neg; assumption
      apply mem_neg; assumption
      rw [neg_add_rev, add_comm]
    mem_add := by
      rintro _ _ ⟨⟨xa, xb⟩, hxa, hxb, rfl⟩ ⟨⟨ya, yb⟩, hya, hyb, rfl⟩
      refine ⟨(xa + ya, xb + yb), ?_, ?_, ?_⟩
      apply mem_add <;> assumption
      apply mem_add <;> assumption
      dsimp only; ac_rfl
    mem_mul_left := by
      rintro r _ ⟨⟨x, y⟩, hx, hy, rfl⟩
      refine ⟨(r * x, r * y), ?_, ?_, ?_⟩
      apply mem_mul_left a; assumption
      apply mem_mul_left b; assumption
      rw [mul_add]
    mem_mul_right := by
      rintro r _ ⟨⟨x, y⟩, hx, hy, rfl⟩
      refine ⟨(x * r, y * r), ?_, ?_, ?_⟩
      apply mem_mul_right; assumption
      apply mem_mul_right; assumption
      rw [add_mul]
  }

instance : Mul (Ideal α) where
  mul a b := {
    carrier := Set.mk fun x => ∃l: List (a × b), (l.map (fun (a, b) => a.val * b.val)).sum = x
    mem_zero := by
      refine ⟨[(⟨0, ?_⟩, ⟨0, ?_⟩)], ?_⟩
      apply mem_zero
      apply mem_zero
      simp [mul_zero, add_zero]
    mem_add := by
      intro _ _ ⟨x, hx⟩ ⟨y, hy⟩
      simp at *
      exists x ++ y
      rw [List.map_append, List.sum_append]
      congr
    mem_neg := by
      intro _ ⟨xs, hxs⟩
      simp at *
      exists xs.map (fun (a, b) => (-a, b))
      rw [←hxs, neg_eq_neg_one_zsmul, List.smul_sum, List.map_map, List.map_map]
      congr; ext ⟨x, y⟩
      show -x.val * y.val = -1 • (x.val * y.val)
      rw [neg_one_zsmul, neg_mul_left]
    mem_mul_left := by
      intro r _ ⟨xs, hxs⟩
      exists xs.map (fun (a, b) => (⟨r * a.val, mem_mul_left _ _ _ a.property⟩, b))
      rw [←hxs, List.mul_sum, List.map_map, List.map_map]
      congr; ext
      apply mul_assoc
    mem_mul_right := by
      intro r _ ⟨xs, hxs⟩
      exists xs.map (fun (a, b) => (a, ⟨b.val * r, mem_mul_right _ _ _ b.property⟩))
      rw [←hxs, List.sum_mul, List.map_map, List.map_map]
      congr; ext; symm
      apply mul_assoc
  }

instance : SMul ℕ (Ideal α) := instNSMulrec
instance : Pow (Ideal α) ℕ := instNPowrec

instance : NatCast (Ideal α) := _root_.instNatCast

instance : SemiringOps (Ideal α) := inferInstance

instance : IsAddZeroClass (Ideal α) where
  zero_add a := by
    ext x
    apply Iff.intro
    · rintro ⟨⟨_, y⟩, rfl, _, rfl⟩
      rwa [zero_add]
    · intro h
      refine ⟨(0, x), ?_, ?_, ?_⟩
      trivial
      trivial
      rw [zero_add]
  add_zero a := by
    ext x
    apply Iff.intro
    · rintro ⟨⟨_, _⟩, _, rfl, rfl⟩
      rwa [add_zero]
    · intro h
      refine ⟨(x, 0), ?_, ?_, ?_⟩
      trivial
      trivial
      rw [add_zero]

instance : IsMulOneClass (Ideal α) where
  one_mul a := by
    ext x
    apply Iff.intro
    · rintro ⟨l, rfl⟩
      dsimp only
      apply mem_list_sum
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨⟨x, y⟩, h, rfl⟩ := hx
      dsimp
      apply mem_mul_left
      exact y.property
    · intro h
      exists [(⟨1, True.intro⟩, ⟨x, h⟩)]
      simp
  mul_one a := by
    ext x
    apply Iff.intro
    · rintro ⟨l, rfl⟩
      dsimp only
      apply mem_list_sum
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨⟨x, y⟩, h, rfl⟩ := hx
      dsimp
      apply mem_mul_right
      exact x.property
    · intro h
      exists [(⟨x, h⟩, ⟨1, True.intro⟩)]
      simp

instance : IsAddSemigroup (Ideal α) where
  add_assoc a b c := by
    ext x
    apply Iff.intro
    · rintro ⟨⟨_, z⟩, ⟨⟨x, y⟩, _, _, rfl⟩ , _, rfl⟩
      refine ⟨(x, _), ?_, ⟨(y, z), ?_, ?_, rfl⟩, ?_⟩
      any_goals assumption
      rw [add_assoc]
    · rintro ⟨⟨x, _⟩, _, ⟨⟨y, z⟩, _, _, rfl⟩, rfl⟩
      refine ⟨(_, z), ⟨(x, y), ?_, ?_, rfl⟩, ?_, ?_⟩
      any_goals assumption
      rw [add_assoc]

instance : IsAddMonoid (Ideal α) where

instance : IsMulZeroClass (Ideal α) where
  zero_mul a := by
    ext x
    apply Iff.intro
    rintro ⟨l, rfl⟩
    simp
    apply List.sum_eq_zero_of_all_zeros
    intro x
    rw [List.mem_map]
    rintro ⟨⟨⟨_, rfl⟩, y⟩, _, rfl⟩
    apply zero_mul
    rintro rfl
    exists [(0, 0)]
    simp
  mul_zero a := by
    ext x
    apply Iff.intro
    rintro ⟨l, rfl⟩
    simp
    apply List.sum_eq_zero_of_all_zeros
    intro x
    rw [List.mem_map]
    rintro ⟨⟨x, ⟨_, rfl⟩⟩, _, rfl⟩
    apply mul_zero
    rintro rfl
    exists [(0, 0)]
    simp

instance : IsAddCommMagma (Ideal α) where
  add_comm a b := by
    ext x
    apply Iff.intro
    all_goals
      rintro ⟨⟨x, y⟩, _, _, rfl⟩
      refine ⟨(y, x), ?_, ?_, add_comm _ _⟩ <;> assumption

instance : IsAddMonoidWithOne (Ideal α) where
  natCast_zero := rfl
  natCast_succ _ := rfl

instance : IsSemigroup (Ideal α) where
  mul_assoc a b c := by
    ext x
    apply Iff.intro
    · rintro ⟨l, rfl⟩
      refine ⟨?_, ?_⟩
      exact l.flatMap fun x => by
        let l' := Classical.choose x.fst.property
        apply l'.map
        intro (a', b')
        refine (a', ⟨b'.val * x.snd.val, ?_⟩)
        exists [(b', x.snd)]
        simp [add_zero]
      dsimp only
      conv => {
        rw [List.map_flatMap]; lhs; arg 1; arg 1; intro x
        rw [List.map_map]
      }
      induction l with
      | nil => rfl
      | cons l ls ih =>
        rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]; clear ih
        congr
        rw [Function.comp_def]; dsimp
        conv => { rhs; rw [←Classical.choose_spec l.fst.property] }
        rw [List.sum_mul, List.map_map]
        congr; ext x
        rw [←mul_assoc]
        rfl
    · rintro ⟨l, rfl⟩
      refine ⟨?_, ?_⟩
      exact l.flatMap fun x => by
        let l' := Classical.choose x.snd.property
        apply l'.map
        intro (b', c')
        refine (⟨x.fst.val * b'.val, ?_⟩, c')
        exists [(x.fst, b')]
        simp [add_zero]
      dsimp only
      conv => {
        rw [List.map_flatMap]; lhs; arg 1; arg 1; intro x
        rw [List.map_map]
      }
      induction l with
      | nil => rfl
      | cons l ls ih =>
        rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]; clear ih
        congr
        rw [Function.comp_def]; dsimp
        conv => { rhs; rw [←Classical.choose_spec l.snd.property] }
        rw [List.mul_sum, List.map_map]
        congr; ext x
        rw [mul_assoc]
        rfl

instance : IsSemiring (Ideal α) where
  mul_add k a b := by
    ext x
    apply Iff.intro
    · rintro ⟨l, rfl⟩
      dsimp
      refine ⟨(?_, ?_), ?_, ?_, ?_⟩
      exact List.sum <| l.map <| by
        intro (k', x')
        exact k'.val * (Classical.choose x'.property).fst
      exact List.sum <| l.map <| by
        intro (k', x')
        exact k'.val * (Classical.choose x'.property).snd
      refine ⟨?_, ?_⟩
      exact l.map <| by
        intro (k', x')
        refine (k', ⟨(Classical.choose x'.property).fst, ?_⟩)
        exact (Classical.choose_spec x'.property).left
      · dsimp; rw [List.map_map]
        rfl
      refine ⟨?_, ?_⟩
      exact l.map <| by
        intro (k', x')
        refine (k', ⟨(Classical.choose x'.property).snd, ?_⟩)
        exact (Classical.choose_spec x'.property).right.left
      · dsimp; rw [List.map_map]
        rfl
      · dsimp
        rw [List.map_sum_map]
        congr; ext x
        rw [←mul_add, (Classical.choose_spec x.snd.property).right.right]
    · rintro ⟨⟨_, _⟩, ⟨xs, rfl⟩, ⟨ys, rfl⟩, rfl⟩
      dsimp
      rw [←List.sum_append]
      refine ⟨?_ ++ ?_, ?_⟩
      exact xs.map (fun (k', a') => by
        refine (k', ⟨a'.val, ?_⟩)
        refine ⟨(a'.val, 0), ?_, ?_, ?_⟩
        apply a'.property
        apply mem_zero
        apply add_zero)
      exact ys.map (fun (k', b') => by
        refine (k', ⟨b'.val, ?_⟩)
        refine ⟨(0, b'.val), ?_, ?_, ?_⟩
        apply mem_zero
        apply b'.property
        apply zero_add)
      dsimp
      rw [List.map_append, List.map_map, List.map_map]
      rfl
  add_mul a b k := by
    ext x
    apply Iff.intro
    · rintro ⟨l, rfl⟩
      dsimp
      refine ⟨(?_, ?_), ?_, ?_, ?_⟩
      exact List.sum <| l.map <| by
        intro (x', k')
        exact (Classical.choose x'.property).fst * k'.val
      exact List.sum <| l.map <| by
        intro (x', k')
        exact (Classical.choose x'.property).snd * k'.val
      refine ⟨?_, ?_⟩
      exact l.map <| by
        intro (x', k')
        refine (⟨(Classical.choose x'.property).fst, ?_⟩, k')
        exact (Classical.choose_spec x'.property).left
      · dsimp; rw [List.map_map]
        rfl
      refine ⟨?_, ?_⟩
      exact l.map <| by
        intro (x', k')
        refine (⟨(Classical.choose x'.property).snd, ?_⟩, k')
        exact (Classical.choose_spec x'.property).right.left
      · dsimp; rw [List.map_map]
        rfl
      · dsimp
        rw [List.map_sum_map]
        congr; ext x
        rw [←add_mul, (Classical.choose_spec x.fst.property).right.right]
    · rintro ⟨⟨_, _⟩, ⟨xs, rfl⟩, ⟨ys, rfl⟩, rfl⟩
      dsimp
      rw [←List.sum_append]
      refine ⟨?_ ++ ?_, ?_⟩
      exact xs.map (fun (a', k') => by
        refine (⟨a'.val, ?_⟩, k')
        refine ⟨(a'.val, 0), ?_, ?_, ?_⟩
        apply a'.property
        apply mem_zero
        apply add_zero)
      exact ys.map (fun (b', k') => by
        refine (⟨b'.val, ?_⟩, k')
        refine ⟨(0, b'.val), ?_, ?_, ?_⟩
        apply mem_zero
        apply b'.property
        apply zero_add)
      dsimp
      rw [List.map_append, List.map_map, List.map_map]
      rfl

end Ideal
