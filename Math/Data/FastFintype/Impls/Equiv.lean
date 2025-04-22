import Math.Data.FastFintype.Defs
import Math.Data.Nat.Factorial
import Math.Data.Fin.Pairing
import Math.Data.List.Defs

private def perm_list (a: Array α) (n: Nat) (h: n = a.size) (x: Fin (n !)) : List α :=
  match n with
  | 0 => []
  | n + 1 =>
    have ⟨x₀, x⟩ := Equiv.finProd.symm x
    let a' : Array α := a.eraseIdx x₀.val
    have := perm_list a' n (by
      rw [Array.size_eraseIdx]
      apply Nat.succ.inj
      show n + 1 = a.size - 1 + 1
      rw [h, Nat.sub_add_cancel]
      apply Nat.succ_le_of_lt
      rw [←h]; apply Nat.zero_lt_succ) x
    a[x₀]::this

private def perm_list_inj (a: Array α) (ha: a.toList.Nodup) (n: Nat) (hlen: n = a.size)
  : Function.Injective (perm_list a n hlen) := by
  intro x y h
  induction n generalizing a with
  | zero => apply Subsingleton.allEq (α := Fin 1)
  | succ n ih =>
    unfold perm_list at h
    simp at h
    obtain ⟨h₀, h⟩ := h
    replace h₀ := h₀
    have := List.nodup_iff_getElem_inj.mp ha (x := x.pair_left.cast hlen) (y := y.pair_left.cast hlen) h₀
    rw [←Fin.val_inj] at this; simp at this
    rw [Fin.val_inj] at this
    conv at h => { rhs; arg 1; arg 2; rw [←this] }
    have := ih _ ?_ _ h
    apply Equiv.finProd.symm.inj
    ext
    simp; rwa [Fin.val_inj]
    simp; rwa [Fin.val_inj]
    simp
    apply List.nodup_eraseIdx
    assumption

private def perm_list_spec (a: Array α) (n: Nat) (h: n = a.size) (idx: Fin (n !)) : ∀{x}, x ∈ perm_list a n h idx ↔ x ∈ a := by
  intro x
  induction n generalizing a with
  | zero =>
    match a with
    | ⟨[]⟩ =>
    simp; intro; contradiction
  | succ n ih =>
    apply flip Iff.intro
    · intro hx
      unfold perm_list
      simp
      obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
      by_cases i = idx.pair_left.val
      left; congr
      right
      apply (ih _ _ _).mpr
      rw [Array.mem_eraseIdx_iff_getElem]
      refine ⟨i, hi, ?_, rfl⟩
      assumption
    · intro hx
      unfold perm_list at hx
      simp at hx
      cases hx
      subst x
      exact Array.mem_of_getElem rfl
      rename_i ha
      apply Array.mem_of_mem_eraseIdx
      apply (ih _ _ _).mp
      assumption

private def perm_list_length (a: Array α) (n: Nat) (h: n = a.size) (idx: Fin (n !)) : (perm_list a n h idx).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    show _ + 1 = _
    congr
    apply ih

def perm_list_nodup (a: Array α) (ha: a.toList.Nodup) (n: Nat) (hlen: n = a.size)  (x: Fin (n !)) : (perm_list a n hlen x).Nodup := by
  induction n generalizing a with
  | zero => apply List.Pairwise.nil
  | succ n ih =>
    apply List.Pairwise.cons
    · intro a₀ ha₀
      simp at *
      rw [perm_list_spec] at ha₀
      rw [Array.mem_eraseIdx_iff_getElem] at ha₀
      obtain ⟨i, hi, ne_left, eq⟩ := ha₀
      rw [←eq]; clear eq
      intro h
      have := List.nodup_getElem_inj ha h
      subst i
      contradiction
    · apply ih
      simp ; apply List.nodup_eraseIdx
      assumption

private instance Fintype.instPerm [DecidableEq α] [fα: Fintype α] : Fintype (α ≃ α) :=
  fα.map fun fα =>
  let src := Array.ofFn fα.all
  let eqv := fα.equiv_fin_card
  have src_size : fα.card = src.size := by simp [src]
  have src_nodup : src.toList.Nodup := by
    simp [src]
    apply (List.nodup_ofFn _).mp
    exact fα.all.inj
  have mem_src (x: α) : x ∈ src := by
    rw [Array.mem_ofFn]
    have ⟨i, hi⟩ := fα.complete x
    exists i; symm; assumption
  {
    card := (fα.card !)
    all := {
      toFun i :=
        let l := perm_list src fα.card (by assumption) i
        have l_length : l.length = fα.card := by rw [←perm_list_length src fα.card (by assumption) i]
        have mem_l (x: α) : x ∈ l := by
          apply (perm_list_spec _ _ _ _).mpr
          apply mem_src
        have idx_of_lt (x: α): List.idxOf x l < fα.card := by
          rw [←l_length]
          refine List.idxOf_lt_length ?_
          apply mem_l
        {
          toFun x := l[eqv x]'(by rw [perm_list_length]; apply Fin.isLt)
          invFun x := eqv.symm ⟨l.idxOf x, by apply idx_of_lt⟩
          rightInv := by
            intro x
            simp
            rw [List.getElem_idxOf]
            apply mem_l
          leftInv := by
            intro x
            simp
            conv => { lhs; rhs; lhs }
            have := perm_list_nodup src src_nodup fα.card src_size i
            rw [List.nodup_iff_getElem_inj] at this
            have := this (x := (eqv x).cast (by rw [perm_list_length])) (y := ⟨List.idxOf l[(eqv x)] l, by
              conv => { rhs; rw [perm_list_length, ←l_length] }
              apply List.idxOf_lt_length
              apply mem_l⟩) ?_
            rw [←Fin.val_inj] at this
            simp at this
            symm; apply Equiv.eq_symm_of_coe_eq
            rw [←Fin.val_inj]
            simp; assumption
            simp; clear this
            rw [List.getElem_idxOf]
            rw [perm_list_spec]
            apply mem_src
        }
      inj' := by
        intro x y h
        simp at h
        -- have := perm_list_inj
        have g : perm_list src fα.card src_size x = perm_list src fα.card src_size y := by
          apply List.ext_getElem
          rw [perm_list_length, perm_list_length]
          intro i h₀ h₁
          have := congrFun h.left (eqv.symm ⟨i, by rwa [←perm_list_length src fα.card]⟩)
          simpa using this
        exact perm_list_inj _ src_nodup _ _ g
    }
    complete x := by
      dsimp
      sorry
  }

instance Fintype.instEquiv
  [DecidableEq α] [DecidableEq β]
  [Fintype α] [Fintype β] : Fintype (α ≃ β) :=
  if hcard:card α = card β then
    (Fintype.equiv_of_card_eq α β hcard).recOnSubsingleton fun eqv =>
    Fintype.ofEquiv (Equiv.congrEquiv .rfl eqv.symm)
  else
    have : IsEmpty (α ≃ β) := {
      elim := by
        intro h
        apply hcard
        apply card_eq_of_equiv
        assumption
    }
    inferInstance
