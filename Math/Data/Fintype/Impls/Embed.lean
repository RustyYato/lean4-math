import Math.Data.Fintype.Defs
import Math.Logic.Equiv.Basic

open List

namespace List

def eq_of_sublist_of_length_eq {as bs: List α} (h: as <+ bs) (g: bs.length ≤ as.length) : as = bs := by
  induction h with
  | slnil => rfl
  | cons a h ih =>
    clear as bs; rename_i as bs
    cases ih (Nat.le_trans (Nat.le_succ _) g)
    rw [List.length_cons, ←Nat.not_lt] at g
    have := g (Nat.lt_succ_self _)
    contradiction
  | cons₂ a h ih =>
    clear as bs; rename_i as bs
    rw [ih]
    apply Nat.le_of_succ_le_succ
    assumption

end List

namespace Embedding

variable [_root_.DecidableEq α]

private def sublists (as: List α) : List (α × List α) :=
  (List.finRange as.length).map (fun x => (as[x], List.eraseIdx as x.val))

private def allOn (as: List α) (bs: List β) (hbs: bs.Nodup) : List (as ↪ bs) :=
  match as with
  | [] => [{
    toFun := nofun
    inj' := Function.empty_inj
  }]
  | a::as =>
    (sublists bs).attach.flatMap (fun ⟨(b, bs'), h⟩ => by
      apply (allOn as bs' ?_).map
      intro f
      refine {
        toFun x := ⟨?_, ?_⟩
        inj' := ?_
      }
      · if x.val = a then
          exact b
        else
          refine (f ⟨x, ?_⟩).val
          cases x with | mk x hx =>
          cases hx
          contradiction
          assumption
      · simp [sublists, List.mem_map, List.finRange,] at h
        obtain ⟨i, rfl, rfl⟩ := h
        split
        exact getElem_mem (Embedding.sublists.proof_1 bs i)
        apply List.mem_of_mem_eraseIdx
        apply (f ⟨x.val, _⟩).property
      · simp [sublists, List.mem_map, List.finRange,] at h
        obtain ⟨i, rfl, rfl⟩ := h
        intro ⟨x, hx⟩ ⟨y, hy⟩ eq
        dsimp at eq
        split at eq <;> split at eq
        · subst x; subst y; rfl
        · replace eq := Subtype.mk.inj eq
          have := (f ⟨y, ?_⟩).property
          rw [List.mem_eraseIdx_iff_getElem] at this
          obtain ⟨i₀, ne, hi₀, eq'⟩ := this
          rw [←eq'] at eq
          have := nodup_getElem_inj hbs eq.symm
          contradiction
          cases hy
          contradiction
          assumption
        · replace eq := Subtype.mk.inj eq
          have := (f ⟨x, ?_⟩).property
          rw [List.mem_eraseIdx_iff_getElem] at this
          obtain ⟨i₀, ne, hi₀, eq'⟩ := this
          rw [←eq'] at eq
          have := nodup_getElem_inj hbs eq
          contradiction
          cases hx
          contradiction
          assumption
        · cases f.inj <| Subtype.val_inj (Subtype.mk.inj eq)
          rfl
      · simp [sublists, List.mem_map, List.finRange,] at h
        obtain ⟨_, _, rfl⟩ := h
        apply Nodup.eraseIdx
        assumption)

private def nodup_sublists {as: List α} : as.Nodup -> (sublists as).Nodup := by
  intro h
  apply nodup_iff_getElem_inj.mpr
  intro i j eq
  simp [Embedding.sublists, List.finRange] at eq
  erw [List.getElem_map, List.getElem_map] at eq
  simp at eq
  apply Fin.val_inj.mp
  exact nodup_getElem_inj h eq.left

private def nodup_allOn {as: List α} {bs: List β} {has: as.Nodup} {hbs: bs.Nodup} : (allOn as bs hbs).Nodup := by
  induction as generalizing bs with
  | nil => apply List.Nodup.singleton
  | cons a as ih =>
    simp [Embedding.allOn]
    apply List.nodup_flatMap
    · apply (List.nodup_attach _).mp
      apply nodup_sublists
      assumption
    · have : a ∉ as := (has.head _ · _root_.rfl)
      intro ⟨x, hx⟩
      apply List.nodup_map
      · intro f₀ f₁ eq
        simp at eq
        replace eq := congrFun eq
        ext ⟨a₀, ha₀⟩
        replace eq := eq ⟨a₀, List.Mem.tail _ ha₀⟩
        dsimp at eq
        split at eq
        subst a
        contradiction
        injection eq
      · apply ih
        exact has.tail
    · intro ⟨⟨a₀, f₀⟩ , hf₀⟩ ⟨⟨a₁, f₁⟩ , hf₁⟩ gf₀ gf₁ f₂ hf₂
      simp; simp at hf₂
      obtain ⟨f₃, hf₃, rfl⟩ := hf₂
      clear gf₀ gf₁
      intro f₄ hf₄ g
      injection g with g
      replace g := congrFun g
      simp [sublists, List.finRange]  at hf₀ hf₁
      obtain ⟨i₀, rfl, rfl⟩ := hf₀
      obtain ⟨i₁, rfl, rfl⟩ := hf₁
      have := g ⟨a, List.Mem.head _⟩
      simp at this
      apply And.intro
      · have := g ⟨a, List.Mem.head _⟩
        simp at this
        symm; assumption
      · congr
        apply Fin.val_inj.mp
        apply nodup_getElem_inj hbs
        symm; assumption

private def mem_allOn {as: List α} {bs: List β} {has: as.Nodup} {hbs: bs.Nodup} : ∀{x}, x ∈ allOn as bs hbs := by
  classical
  intro f
  induction as generalizing bs with
  | nil =>
    apply List.mem_singleton.mpr
    ext x
    exact elim_empty x
  | cons a as ih =>
    simp [Embedding.allOn, List.mem_flatMap, List.mem_map]
    let f': as ↪ (bs.erase (f ⟨_, List.Mem.head _⟩ )) := {
      toFun a := ⟨(f ⟨a, List.Mem.tail _ a.property⟩).val, (by
        rw [List.mem_erase_of_ne]
        apply Subtype.property
        intro h
        cases (f.inj (Subtype.val_inj h))
        exact has.head a.val a.property _root_.rfl)⟩
      inj' := by
        intro ⟨x, hx⟩ ⟨y, hy⟩ eq
        dsimp at eq
        cases f.inj (Subtype.val_inj (Subtype.mk.inj eq))
        rfl
    }
    let b := f ⟨a, List.Mem.head _⟩
    refine ⟨?_, _, ?_, f', ?_, ?_⟩
    · exact b.val
    · simp [Embedding.sublists, List.finRange]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      exact bs.idxOf b.val
      refine idxOf_lt_length ?_
      exact b.property
      rw [List.getElem_idxOf]
      apply b.property
      simp; symm
      apply erase_eq_eraseIdx_of_idxOf
      rfl
    · apply ih
      exact has.tail
    · ext ⟨x, hx⟩
      simp
      split
      subst x
      rfl
      rfl

instance [ha: Fintype α] [hb: Fintype β] : Fintype (α ↪ β) := by
  apply ha.recOnSubsingleton
  intro as asnodup ascomplete
  apply hb.recOnSubsingleton
  intro bs bsnodup bscomplete
  refine Fintype.ofList ?_ ?_ ?_
  · apply (allOn as bs bsnodup).map
    intro f
    apply Equiv.congrEmbed _ _ f
    exact {
      toFun x := x
      invFun x := ⟨x, ascomplete _⟩
      leftInv x := by rfl
      rightInv x := by rfl
    }
    exact {
      toFun x := x
      invFun x := ⟨x, bscomplete _⟩
      leftInv x := by rfl
      rightInv x := by rfl
    }
  · apply List.nodup_map
    · intro x y eq
      exact Equiv.inj _ eq
    apply nodup_allOn
    assumption
  · intro f
    simp
    refine ⟨?_, ?_, ?_⟩
    apply Equiv.congrEmbed _ _ f
    exact {
      toFun x := ⟨x, ascomplete _⟩
      invFun x := x
      leftInv x := by rfl
      rightInv x := by rfl
    }
    exact {
      toFun x := ⟨x, bscomplete _⟩
      invFun x := x
      leftInv x := by rfl
      rightInv x := by rfl
    }
    apply mem_allOn
    assumption
    rfl

end Embedding
