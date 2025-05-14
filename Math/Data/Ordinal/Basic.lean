import Math.Algebra.Semigroup.Defs
import Math.Data.Ordinal.Defs

namespace Ordinal

section Algebra

instance : IsAddZeroClass Ordinal where
  zero_add a := by simp
  add_zero a := by simp

def add_succ (a b: Ordinal) : a + (b + 1) = (a + b) + 1 := by
  cases a with | _ α relα =>
  cases b with | _ β relβ =>
  rw [←succ_eq_add_one, ←succ_eq_add_one]
  apply sound
  simp
  exact {
    toFun
    | .inl x => .some (.inl x)
    | .inr (.some x) => .some (.inr x)
    | .inr .none => .none
    invFun
    | .some (.inl x) => .inl x
    | .some (.inr x) => .inr (.some x)
    | .none => .inr .none
    leftInv x :=
      match x with
      | .inl x
      | .inr (.some x)
      | .inr .none => rfl
    rightInv x :=
      match x with
      | .some (.inl x)
      | .some (.inr x)
      | .none => rfl
    resp_rel := by
      intro x y
      simp
      match x with
      | .inl x =>
        match y with
        | .inl y => simp
        | .inr (.some y) => simp
        | .inr .none => simp
      | .inr (.some x) =>
        match y with
        | .inl y => simp
        | .inr (.some y) => simp
        | .inr .none => simp
      | .inr .none =>
        match y with
        | .inl y => simp
        | .inr (.some y) => simp
        | .inr .none =>
          simp
          apply Iff.intro nofun nofun
  }

def add_limit (a b: Ordinal) (hb: IsSuccLimitOrdinal b) : a + b = ⨆b': { o // o < b }, a + b'.val := by
  apply le_antisymm
  · apply le_csInf
    · exists a + b
      rintro _ ⟨x, rfl⟩
      simp
      apply le_iff_add_left.mp
      exact le_of_lt x.property
    · intro x hx
      have := hx (a + b)
      rw [←not_lt]
      intro h
      have := hx (a + b)
      rw [←not_lt] at this
      replace this := (this · h)
      rw [Set.mem_range] at this
      simp at this

      sorry
  · apply csInf_le
    apply Ordinal.BoundedBelow
    rintro _ ⟨x, rfl⟩
    simp
    apply le_iff_add_left.mp
    exact le_of_lt x.property

def add_sup (a: Ordinal) (b: ι -> Ordinal) [Nonempty ι] : a + (⨆i, b i) = ⨆i, a + b i := by
  sorry

instance : IsAddSemigroup Ordinal where
  add_assoc a b c := by
    induction c generalizing a b with
    | zero => simp
    | succ a ih => rw [add_succ, add_succ, add_succ, ih]
    | limit c hc ih =>
      have : Nonempty { o // o < c } := ⟨0, by
        apply lt_of_not_le
        intro h; cases le_antisymm h (bot_le _)
        have := hc.ne
        contradiction⟩
      rw [add_limit _ c, add_limit _ c, add_sup]
      conv => { rhs; rhs; intro a'; rw [←ih _ a'.property] }
      assumption
      assumption

end Algebra

section Order

def sup_of_lt (a: Ordinal) (h: IsLimitOrdinal a) : a = ⨆a': { o // o < a }, a'.val := by
  sorry

def add_lt_limit (a b c: Ordinal) (h: IsLimitOrdinal a) (hb: b < a) (hc: c < a) : b + c < a := by
  sorry

def exists_add_left_of_le {a b: Ordinal} (h: a ≤ b) : ∃k, b = a + k := by
  induction b generalizing a with
  | zero =>
    cases le_antisymm h (bot_le _)
    exists 0
    simp
  | succ b ih =>
    rcases lt_or_eq_of_le h with h | h
    replace h := Ordinal.le_of_lt_succ h
    obtain ⟨k, rfl⟩ := ih h
    exists k + 1
    rw [←add_assoc]
    subst a
    exists 0
    simp
  | limit b hb ih =>
    rcases Or.symm (lt_or_eq_of_le h) with h | h
    · subst b
      exists 0
      simp
    · exists b
      rw [add_limit]
      suffices ⨆b': { o // o < b }, a + b' =⨆b': { o // o < b }, b'.val by
        rw [this, ←sup_of_lt b]
        infer_instance
      · have zero_lt_b : 0 < b := by
          apply lt_of_le_of_ne
          apply bot_le
          symm; exact hb.ne
        apply le_antisymm
        · apply csSup_le_csSup
          · exists b
            rintro _ ⟨x, rfl⟩
            apply le_of_lt
            apply x.property
          · exists a
            rw [Set.mem_range]
            exists ⟨0, zero_lt_b⟩
            simp
          · rintro _ ⟨x, rfl⟩
            simp
            apply add_lt_limit
            infer_instance
            assumption
            exact x.property
        · apply csSup_le_csSup'
          · exists b
            rintro _ ⟨x, rfl⟩
            simp
            apply le_of_lt
            apply add_lt_limit
            infer_instance
            assumption
            exact x.property
          · exists 0
            exists ⟨0, zero_lt_b⟩
          · rintro x hx y ⟨⟨_, hy⟩, rfl⟩
            apply flip le_trans
            apply hx
            exists ⟨y, hy⟩
            simp
            exact le_add_right a y
      assumption

end Order


end Ordinal
