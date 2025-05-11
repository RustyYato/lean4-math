import Math.Data.Cardinal.Algebra
import Math.Data.Cardinal.Order
import Math.Data.Ordinal.Basic

namespace Cardinal

private noncomputable def preAleph' (o: Ordinal.{u}) : Cardinal.{u} :=
  let S : Set Cardinal := Set.mk fun c : Cardinal => ∀x < o, preAleph' x < c
  ⨅ S
termination_by o

private def preAleph'_set (o: Ordinal) : Set Cardinal :=
  Set.mk fun c : Cardinal => ∀x < o, preAleph' x < c

private def preAleph'_eq : preAleph' o = ⨅ (preAleph'_set o) := by
  rw [preAleph']; rfl

private def preAleph'_set_nonempty.{u} (o: Ordinal.{u}) : (preAleph'_set o).Nonempty := by
  suffices ¬∀c: Cardinal, ∃x < o, c ≤ preAleph' x by
    simp [←not_lt] at this
    obtain ⟨x, hx⟩ := this
    exists x
  intro h
  replace h (c: Cardinal) : ∃x < o, c = preAleph' x := by
    have ⟨x, ⟨hx, h⟩, is_min⟩ := Relation.exists_min (· < ·) (h c)
    rename_i h₀; clear h₀
    exists x
    apply And.intro hx
    apply le_antisymm
    assumption
    simp [not_le] at is_min
    rw [preAleph'_eq]
    apply csInf_le
    apply Cardinal.BoundedBelow
    intro y hy
    apply is_min
    assumption
    apply lt_trans
    assumption
    assumption
  replace h := Classical.axiomOfChoice h
  obtain ⟨f, hf⟩ := h
  let o' := ⨆ (Set.range f)
  have f_bounded (x) : f x ≤ o' := by
    apply le_csSup
    exists o
    rintro _ ⟨a, rfl⟩
    apply le_of_lt
    apply (hf _).left
    apply Set.mem_range'
  have f_bounded' (x) : f x < o' + 1 := by
    apply lt_of_le_of_lt
    apply f_bounded
    apply Ordinal.lt_succ_self

  have left_inv : Function.IsLeftInverse preAleph' f := by
    intro c; rw [←(hf c).right]
  have f_inj := left_inv.Injective
  have preAleph'_surj := left_inv.Surjective

  have card_le_ulift : #(Set.range f) ≤ ulift.{u, u+1} (o' + 1).card := by
    induction ho':o' using Ordinal.ind with | _ α relα =>
    rw [←Ordinal.succ_eq_add_one]
    conv at f_bounded' => { intro; rw [←Ordinal.succ_eq_add_one, ho'] }
    have (x) := Ordinal.rank_surj (Ordinal.rel_succ relα) _ (f_bounded' x)
    replace this := Classical.axiomOfChoice this
    obtain ⟨f', hf'⟩ := this
    refine ⟨Equiv.congrEmbed .rfl (Equiv.ulift _).symm ?_⟩
    simp
    exact {
      toFun x := f' (Classical.choose x.property)
      inj' := by
        intro x y h
        simp at h
        let x' := Classical.choose x.property
        let y' := Classical.choose y.property
        have hx: x.val = f x' := Classical.choose_spec x.property
        have hy: y.val = f y' := Classical.choose_spec y.property
        apply Subtype.val_inj
        rw [hx, hy]
        replace h : f' x' = f' y' := h
        have : Ordinal.rank (Ordinal.rel_succ relα) (f' x') = Ordinal.rank (Ordinal.rel_succ relα) (f' y') := by rw [h]
        rwa [←hf', ←hf'] at this
    }
  have card_eq_class : #(Set.range f) = #Cardinal := by
    apply card_range_emb ⟨f, ?_⟩
    assumption
  rw [card_eq_class] at card_le_ulift
  clear card_eq_class
  rw [←not_lt] at card_le_ulift
  apply card_le_ulift
  apply ulift_lt_card_cardinal

private def preAleph'_mem (o: Ordinal) : preAleph' o ∈ preAleph'_set o := by
  rw [preAleph']
  apply csInf_mem
  apply preAleph'_set_nonempty

private def preAleph'_strict_monotone : StrictMonotone preAleph' := by
  intro x y h
  apply preAleph'_mem y
  assumption

private def preAleph'_zero : preAleph' 0 = 0 := by
  rw [preAleph'_eq]
  apply le_antisymm _ (bot_le _)
  apply csInf_le
  apply Cardinal.BoundedBelow
  intro x hx
  rw [←not_le] at hx
  exfalso; apply hx
  apply bot_le

private noncomputable def preAleph'_init : (· < ·: Relation Ordinal ) ≼i (· < ·: Relation Cardinal) where
  toFun := preAleph'
  inj' := preAleph'_strict_monotone.Injective
  resp_rel := by
    intro a b
    simp
    simp [lt_iff_le_and_not_le, preAleph'_strict_monotone.le_iff_le]
  isInitial := by
    intro o c h
    simp at h
    induction o using Ordinal.rec with
    | ind o ih =>
    have : ∃ x, x < o ∧ c ≤ preAleph' x := by
      clear ih
      apply Classical.byContradiction
      intro g; simp [not_le] at g
      have : c ∈ preAleph'_set o := by apply g
      have := csInf_le (Cardinal.BoundedBelow _) this
      rw [←preAleph'_eq, ←not_lt] at this
      contradiction
    obtain ⟨x, hx, c_le⟩ := this
    rcases lt_or_eq_of_le c_le with g | g
    apply ih x hx g
    exists x

noncomputable def preAleph : Ordinal ≃o Cardinal := {
  preAleph'_init.antisymm initseg_ord with
  map_le a b := by
    rw [←not_lt, ←not_lt]
    simp;
    apply Iff.not_iff_not
    apply (preAleph'_init.antisymm initseg_ord).resp_rel
}

def preAlephSet (o: Ordinal) : Set Cardinal where
  Mem c := ∀x < o, preAleph x < c

def preAlephSet_nonempty (o: Ordinal) : (preAlephSet o).Nonempty := by
  apply preAleph'_set_nonempty

def apply_preAleph (o: Ordinal) : preAleph o = ⨅(preAlephSet o) := by
  show preAleph' o = _
  rw [preAleph'_eq]
  rfl

@[simp]
def preAleph_natCast (n: ℕ) : preAleph n = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero =>
    apply le_antisymm
    show preAleph' 0 ≤ 0
    erw [preAleph'_zero]
    apply bot_le
  | succ n =>
    rw [apply_preAleph]
    have : preAlephSet (n + 1 : ℕ) = Set.Ici ((n + 1: ℕ): Cardinal) := by
      ext x; apply Iff.intro
      intro h
      show (n + 1: ℕ) ≤ x
      rw [←not_lt]; intro g
      rw [Cardinal.lt_natCast] at g
      obtain ⟨m, hm, rfl⟩ := g
      have := h m ((Ordinal.natCast_lt_natCast_iff m (n + 1)).mpr hm)
      rw [ih] at this
      exact lt_irrefl this
      assumption
      intro h a ha
      replace h : (n + 1: ℕ) ≤ x := h
      apply lt_of_lt_of_le _ h
      rw [Ordinal.lt_natCast] at ha
      obtain ⟨m, hm, rfl⟩ := ha
      rw [ih]
      refine (lt_natCast (↑m) (n + 1)).mpr ?_
      exists m
      assumption
    rw [this]; clear this
    apply le_antisymm
    apply csInf_le
    apply Cardinal.BoundedBelow
    apply le_refl (α := Cardinal) (n + 1: ℕ)
    apply le_csInf
    exists (n + 1: ℕ)
    apply le_refl (α := Cardinal) (n + 1: ℕ)
    intro x h
    apply h

@[simp]
def preAleph_omega : preAleph ω = ℵ₀ := by
  rw [apply_preAleph]
  apply le_antisymm
  · apply (csInf_le_iff _ _).mpr
    · intro c h
      apply h
      intro x hx
      rw [Ordinal.lt_omega] at hx
      obtain ⟨n, rfl⟩ := hx
      rw [preAleph_natCast]
      apply natCast_lt_aleph₀
    · apply Cardinal.BoundedBelow
    · apply preAlephSet_nonempty
  · apply le_csInf
    apply preAlephSet_nonempty
    intro a ha
    rw [preAlephSet] at ha
    simp at ha
    replace ha : ∀n: ℕ, n < a := by
      intro n
      have := ha n (Ordinal.natCast_lt_omega _)
      simpa using this
    rw [←not_lt, lt_aleph₀]
    intro ⟨n, hn⟩
    have := ha n
    rw [hn] at this
    exact lt_irrefl this

-- the infinite cardinals indexed by the ordinals
-- if you want to include the finite cardinals use `preAleph`
noncomputable def aleph : Ordinal ↪o Cardinal :=
  (Ordinal.addLeft ω).trans preAleph.toEmbedding

def apply_aleph (o: Ordinal) : aleph o = preAleph (ω + o) := rfl

def aleph0_eq_aleph₀ : aleph 0 = ℵ₀ := by simp [apply_aleph]

end Cardinal
