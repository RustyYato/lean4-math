import Math.Data.Fintype.Defs
import Math.Logic.Equiv.Basic

variable [DecidableEq α] [DecidableEq β]

open List

namespace Equiv

private def allOn₁ {as: List α} {bs bs': List β} (x: (a :: as).Elem) (b: β) (hb: ∃i: Fin bs.length, bs[i] = b ∧ bs.eraseIdx i = bs') (f: as ≃ bs') : bs :=
  if g:x.val = a then
    ⟨b, by
      obtain ⟨_, rfl, rfl⟩ := hb
      apply mem_of_getElem
      rfl⟩
  else
    ⟨f ⟨x.val, by
      rcases x with ⟨x, hx⟩
      cases hx
      contradiction
      assumption⟩, by
      obtain ⟨i, rfl, rfl⟩ := hb
      apply List.mem_of_mem_eraseIdx
      apply Subtype.property⟩

private def allOn₂ {as: List α} {bs bs': List β} (x: bs.Elem) (b: β) (hb: ∃i: Fin bs.length, bs[i] = b ∧ bs.eraseIdx i = bs') (f: as ≃ bs') : a::as :=
  if g:x.val = b then
    ⟨a, by
      obtain ⟨_, rfl, rfl⟩ := hb
      apply List.Mem.head⟩
  else
    ⟨f.symm ⟨x.val, by
      obtain ⟨i, rfl, rfl⟩ := hb
      rw [List.mem_eraseIdx_iff_getElem]
      refine ⟨bs.idxOf x.val, ?_, ?_, ?_⟩
      apply idxOf_lt_length
      apply x.property
      intro h
      replace g : x.val ≠ bs[i.val] := g
      conv at g => { rhs; lhs; rw [←h] }
      rw [getElem_idxOf] at g
      contradiction
      apply x.property
      rw [getElem_idxOf]
      apply x.property⟩, by
      apply List.Mem.tail
      apply Subtype.property (p := (· ∈ as))⟩

private def allOn (as: List α) (bs: List β) (has: as.Nodup) (hbs: bs.Nodup) : List (as ≃ bs) :=
  match as with
  | [] =>
    match bs with
    | [] => [Equiv.empty]
    | b::bs => []
  | a::as =>
     (sublists bs).attach.flatMap fun ⟨⟨b, bs'⟩, hb⟩ =>
     (allOn as bs' has.tail (by
      simp [sublists, finRange] at hb
      obtain ⟨i, rfl, rfl⟩ := hb
      exact Nodup.eraseIdx (↑i) hbs)).map fun f => by
      have notmem_head := (has.head _ · _root_.rfl)
      have hb : ∃a: Fin bs.length, bs[a] = b ∧ bs.eraseIdx a = bs' := by
        simp [sublists, finRange] at hb
        assumption
      refine {
        toFun x := allOn₁ x b hb f
        invFun x := allOn₂ x b hb f
        leftInv := ?_
        rightInv := ?_
      }
      · intro ⟨x, hx⟩
        simp [allOn₁, allOn₂]
        dsimp only
        split
        rw [dif_pos _root_.rfl]
        symm; congr
        rw [dif_neg]
        simp
        erw [Equiv.coe_symm]
        obtain ⟨i, rfl, rfl⟩ := hb
        intro h
        replace h : (f ⟨x, _⟩).val = bs[i] := h
        have := (f ⟨x, ?_⟩).property
        rw [h, List.mem_eraseIdx_iff_getElem] at this
        obtain ⟨i₀, i₀_lt, i₀ne, eq⟩ := this
        have := nodup_getElem_inj hbs eq
        contradiction
        cases hx
        contradiction
        assumption
      · intro ⟨x, hx⟩
        simp [allOn₁, allOn₂]
        split
        rw [dif_pos _root_.rfl]
        symm; congr
        rw [dif_neg]
        simp
        erw [Equiv.symm_coe]

        obtain ⟨i, rfl, rfl⟩ := hb
        intro h
        replace h : (f.symm ⟨x, _⟩).val = a := h
        have := (f.symm ⟨x, ?_⟩).property
        rw [h] at this
        contradiction
        rw [List.mem_eraseIdx_iff_getElem]
        refine ⟨bs.idxOf x, ?_, ?_, ?_⟩
        exact idxOf_lt_length hx
        intro h
        rename_i g _
        replace g : x ≠ bs[i.val] := g
        conv at g => { rhs; lhs; rw [←h] }
        rw [getElem_idxOf] at g
        contradiction
        assumption
        rw [getElem_idxOf bs x hx]

private def nodup_allOn {as: List α} {bs: List β} {has: as.Nodup} {hbs: bs.Nodup} : (allOn as bs has hbs).Nodup := by
  induction as generalizing bs with
  | nil =>
    cases bs
    apply Nodup.singleton
    apply Pairwise.nil
  | cons a as ih =>
    apply nodup_flatMap
    apply (nodup_attach _).mp
    apply nodup_sublists
    assumption
    · intro ⟨⟨b, bs'⟩, hx⟩
      simp
      apply nodup_map
      · intro f₀ f₁ eq
        dsimp at eq
        injection eq with eq
        apply DFunLike.ext
        intro ⟨x, hx⟩
        have := congrFun eq ⟨x, List.Mem.tail _ hx⟩
        simp [Equiv.allOn₁] at this
        rw [dif_neg, dif_neg] at this
        injection this with this
        exact Subtype.val_inj this
        iterate 2
        intro h
        have has := has
        rw [←h] at has
        have := (has.head _ hx _root_.rfl)
        contradiction
      · apply ih
    · intro ⟨(b₀, bs₀'), hb₀⟩ ⟨(b₁, bs₁'), hb₁⟩
      intro h₀ h₁; clear h₀ h₁
      intro f g₀ g₁
      simp at g₀ g₁
      simp
      obtain ⟨f₀, hf₀', eq₀⟩ := g₀
      obtain ⟨f₁, hf₁', eq₁⟩ := g₁
      have eq := eq₀.trans eq₁.symm
      clear hf₀' hf₁' eq₀ eq₁
      injection eq with eq₀ eq₁
      have := congrFun eq₀ ⟨a, List.Mem.head _⟩
      simp [Equiv.allOn₁]  at this
      cases this
      simp [sublists, finRange] at hb₀ hb₁
      obtain ⟨i, rfl, rfl⟩ := hb₀
      obtain ⟨j, eq, rfl⟩ := hb₁
      apply And.intro _root_.rfl
      congr 1; symm
      exact nodup_getElem_inj hbs eq

private def mem_allOn {as: List α} {bs: List β} {has: as.Nodup} {hbs: bs.Nodup} : ∀f, f ∈ allOn as bs has hbs := by
  intro f
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil =>
      apply List.mem_singleton.mpr
      apply Subsingleton.allEq
    | cons b bs => exact elim_empty (f.symm ⟨b, List.Mem.head _⟩ )
  | cons a as ih =>
    simp [allOn]
    let b := f ⟨a, List.Mem.head _⟩
    let i : Nat := bs.idxOf b.val
    let hi: i < bs.length := by
      apply idxOf_lt_length
      apply b.property
    let f' : as ≃ bs.erase b := {
      toFun x := ⟨(f ⟨x.val, List.Mem.tail _ x.property⟩).val, by
        refine (mem_erase_of_ne ?_).mpr ?_
        intro h
        cases f.inj (Subtype.val_inj h)
        have := (has.head _ · _root_.rfl) x.property
        contradiction
        apply Subtype.property (p := (· ∈ bs))⟩
      invFun x := ⟨f.symm ⟨x.val, by
        apply List.mem_of_mem_erase
        apply x.property⟩, by
        have hx : x.val ∈ bs := by
          apply List.mem_of_mem_erase
          apply x.property
        have := (f.symm ⟨x.val, hx⟩).property
        simp at this
        cases this
        rename_i h
        have : (f (⟨(f.symm ⟨x.val, hx⟩).val, Subtype.property _⟩ )).val = x := by rw [f.symm_coe]
        conv at this => { lhs; arg 1; arg 2; lhs; rw [h] }
        replace this : b.val = x.val := this
        have hx' := x.property
        rw [←this] at hx'
        have := Nodup.not_mem_erase hbs hx'
        contradiction
        assumption⟩
      leftInv := by
        intro x
        simp
        ext; simp
        rw [f.coe_symm]
      rightInv := by
        intro x
        simp
        ext; simp
        rw [f.symm_coe]
    }
    refine ⟨f ⟨a, List.Mem.head _⟩ , _, ?_, f', ih _, ?_⟩
    · simp [sublists, finRange]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      exact bs.idxOf b.val
      apply idxOf_lt_length
      exact b.property
      rw [getElem_idxOf]
      exact b.property
      rw [erase_eq_eraseIdx_of_idxOf _ _ _ _root_.rfl]
    · ext ⟨x, hx⟩
      simp
      simp [Equiv.allOn₁]
      split
      subst x; rfl
      rfl

end Equiv

instance [ha: Fintype α] [hb: Fintype β] : Fintype (α ≃ β) := by
  apply ha.recOnSubsingleton
  intro as as_nodup as_complete
  apply hb.recOnSubsingleton
  intro bs bs_nodup bs_complete
  have eqv : (as ≃ bs) ≃ (α ≃ β) := by
    apply Equiv.congrEquiv
    exact {
      toFun x := x
      invFun x := ⟨x, as_complete _⟩
      leftInv x := by rfl
      rightInv x := by rfl
    }
    exact {
      toFun x := x
      invFun x := ⟨x, bs_complete _⟩
      leftInv x := by rfl
      rightInv x := by rfl
    }
  refine Fintype.ofList ?_ ?_ ?_
  apply (Equiv.allOn as bs as_nodup bs_nodup).map
  intro x
  exact eqv x
  · apply List.nodup_map
    · intro f₀ f₁ eq
      dsimp at eq
      exact Equiv.inj _ eq
    · apply Equiv.nodup_allOn
  · intro f
    apply List.mem_map.mpr
    refine ⟨?_, ?_, ?_⟩
    apply eqv.symm f
    apply Equiv.mem_allOn
    rw [eqv.symm_coe]
