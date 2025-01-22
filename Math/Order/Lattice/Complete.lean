import Math.Order.Lattice.ConditionallyComplete
import Math.Data.Set.Basic
import Math.Data.Set.TopBot

variable (α: Type*) [Sup α] [Inf α] [SupSet α] [InfSet α] [LE α] [LT α] [Top α] [Bot α]
variable {α₀: Type*} [Sup α₀] [Inf α₀] [SupSet α₀] [InfSet α₀] [LE α₀] [LT α₀] [Top α₀] [Bot α₀]

class IsCompleteSemiLatticeSup extends IsSemiLatticeSup α: Prop where
  le_sSup: ∀s: Set α, ∀x ∈ s, x ≤ sSup s
  sSup_le: ∀k: α, ∀s: Set α, (∀x ∈ s, x ≤ k) -> sSup s ≤ k

export IsCompleteSemiLatticeSup (le_sSup sSup_le)

class IsCompleteSemiLatticeInf extends IsSemiLatticeInf α: Prop where
  sInf_le: ∀s: Set α, ∀x ∈ s, sInf s ≤ x
  le_sInf: ∀k: α, ∀s: Set α, (∀x ∈ s, k ≤ x) -> k ≤ sInf s

export IsCompleteSemiLatticeInf (sInf_le le_sInf)

class IsCompleteLattice extends IsLattice α, IsCompleteSemiLatticeSup α, IsCompleteSemiLatticeInf α, IsLawfulBot α, IsLawfulTop α: Prop where

instance [IsCompleteSemiLatticeInf α] : IsCompleteSemiLatticeSup (Opposite α) where
  le_sSup := sInf_le (α := α)
  sSup_le := le_sInf (α := α)

instance [IsCompleteSemiLatticeSup α] : IsCompleteSemiLatticeInf (Opposite α) where
  sInf_le := le_sSup (α := α)
  le_sInf := sSup_le (α := α)

instance [IsCompleteLattice α] : IsCompleteLattice (Opposite α) where
  le_top := bot_le (α := α)
  bot_le := le_top (α := α)
  le_sSup := le_sSup
  sSup_le := sSup_le
  sInf_le := sInf_le
  le_sInf := le_sInf

instance [IsCompleteLattice α] : IsConditionallyCompleteLattice α where
  le_csInf _ := le_sInf _ _
  le_csSup _ := le_sSup _ _
  csSup_le _ := sSup_le _ _
  csInf_le _ := sInf_le _ _

section

variable [IsCompleteSemiLatticeSup α₀] {s t : Set α₀} {a b : α₀}

@[simp]
def sSup_le_iff : sSup s ≤ a ↔ ∀b ∈ s, b ≤ a := by
  apply Iff.intro
  intro h
  intro x x_in_s
  apply le_trans _ h
  apply le_sSup
  assumption
  intro h
  apply sSup_le
  assumption

@[simp]
def sSup_singleton : sSup ({ x }: Set α₀) = x := by
  apply le_antisymm
  apply sSup_le
  intro y mem
  rw [mem]
  apply le_sSup
  rfl

@[simp]
def sSup_union : sSup (s ∪ t) = sSup s ⊔ sSup t := by
  apply le_antisymm
  apply sSup_le
  intro k mem
  rcases Set.mem_union.mp mem with h | h
  apply le_trans _ (le_sup_left _ _)
  apply le_sSup
  assumption
  apply le_trans _ (le_sup_right _ _)
  apply le_sSup
  assumption
  apply sup_le
  apply sSup_le
  intro x mem
  apply le_sSup; apply Set.mem_union.mpr; left; assumption
  apply sSup_le
  intro x mem
  apply le_sSup; apply Set.mem_union.mpr; right; assumption

@[simp]
def sSup_insert : sSup (insert a s) = a ⊔ sSup s := by
  erw [sSup_union, sSup_singleton]

def sSup_le_sSup (h: s ⊆ t) : sSup s ≤ sSup t := by
  apply sSup_le
  intro x mem_s
  apply le_sSup
  apply h
  assumption

def sSup_empty_le : ∀x: α₀, sSup ∅ ≤ x := by
  intro x
  apply sSup_le
  intro x mem_s
  contradiction

def le_sSup_univ : ∀x: α₀, x ≤ sSup (Set.univ _) := by
  intro x
  apply le_sSup
  apply Set.mem_univ

end

section

variable [IsCompleteSemiLatticeInf α₀] {s t : Set α₀} {a b : α₀}

@[simp]
def le_sInf_iff : a ≤ sInf s ↔ ∀b ∈ s, a ≤ b :=
  sSup_le_iff (α₀ := Opposite α₀)

@[simp]
def sInf_singleton : sInf ({ x }: Set α₀) = x :=
  sSup_singleton (α₀ := Opposite α₀)

@[simp]
def sInf_union : sInf (s ∪ t) = sInf s ⊓ sInf t :=
  sSup_union (α₀ := Opposite α₀)

@[simp]
def sInf_insert : sInf (insert a s) = a ⊓ sInf s :=
  sSup_insert (α₀ := Opposite α₀)

def sInf_le_sInf (h: s ⊆ t) : sInf t ≤ sInf s :=
  sSup_le_sSup (α₀ := Opposite α₀) h

def le_sInf_empty : ∀x: α₀, x ≤ (sInf ∅) := by
  intro x
  apply le_sInf
  intros
  contradiction

def sInf_univ_le : ∀x: α₀, sInf (Set.univ _) ≤ x := by
  intro x
  apply sInf_le
  apply Set.mem_univ

end

section

variable [IsCompleteLattice α₀] {s t : Set α₀} {a b : α₀}

@[simp]
def sSup_empty [IsCompleteLattice α] : sSup ∅ = (⊥: α) := by
  apply le_antisymm
  apply sSup_empty_le
  apply bot_le

@[simp]
def sSup_univ [IsCompleteLattice α] : sSup (Set.univ α) = (⊤: α) := by
  apply le_antisymm
  apply le_top
  apply le_sSup_univ

@[simp]
def sInf_empty [IsCompleteLattice α] : sInf ∅ = (⊤: α) :=
  sSup_empty (α := Opposite α)

@[simp]
def sInf_univ [IsCompleteLattice α] : sInf (Set.univ α) = (⊥: α) :=
  sSup_univ (α := Opposite α)

def sInf_le_sSup (h: s.Nonempty) : sInf s ≤ sSup s := by
  obtain ⟨x, mem⟩ := h
  apply le_trans
  apply sInf_le
  assumption
  apply le_sSup
  assumption

@[simp]
def sSup_inter_le : sSup (s ∩ t) ≤ sSup s ⊓ sSup t := by
  apply sSup_le
  intro x mem
  have ⟨_, _⟩ := Set.mem_inter.mp mem
  apply le_inf
  apply le_sSup; assumption
  apply le_sSup; assumption

@[simp]
def le_sInf_inter : sInf s ⊔ sInf t ≤ sInf (s ∩ t) :=
  sSup_inter_le (α₀ := Opposite α₀)

@[simp]
def bot_sup : ⊥ ⊔ a = a := by
  apply le_antisymm
  apply sup_le
  apply bot_le
  rfl
  simp

@[simp]
def sup_bot : a ⊔ ⊥ = a := by
  simp [sup_comm a]

@[simp]
def top_sup : ⊤ ⊔ a = ⊤ := by
  apply le_antisymm
  apply sup_le
  rfl
  apply le_top
  simp

@[simp]
def sup_top : a ⊔ ⊤ = ⊤ := by
  simp [sup_comm a]

@[simp]
def bot_inf : ⊥ ⊓ a = ⊥ :=
  top_sup (α₀ := Opposite α₀)

@[simp]
def inf_bot : a ⊓ ⊥ = ⊥ :=
  sup_top (α₀ := Opposite α₀)

@[simp]
def top_inf : ⊤ ⊓ a = a :=
  bot_sup (α₀ := Opposite α₀)

@[simp]
def inf_top : a ⊓ ⊤ = a :=
  sup_bot (α₀ := Opposite α₀)

@[simp]
def sSup_insert_bot : sSup (insert ⊥ s) = sSup s := by
  simp

@[simp]
def sSup_insert_top : sSup (insert ⊤ s) = ⊤ := by
  simp

@[simp]
def sInf_insert_bot : sInf (insert ⊥ s) = ⊥ := by
  simp

@[simp]
def sInf_insert_top : sInf (insert ⊤ s) = sInf s := by
  simp

def sSup_eq_bot : sSup s = ⊥ ↔ ∀x ∈ s, x = ⊥ := by
  apply Iff.intro
  intro h x emm
  apply le_antisymm
  rw [←h]
  apply le_sSup
  assumption
  apply bot_le
  intro h
  apply le_antisymm
  apply sSup_le
  intro x g
  rw [h x]
  assumption
  apply bot_le

def sInf_eq_top : sInf s = ⊤ ↔ ∀x ∈ s, x = ⊤ :=
  sSup_eq_bot (α₀ := Opposite α₀)

end

namespace OrderIso

def instIsCompleteSemiLatticeSup
  {α}
  [LE α] [LT α] [Sup α] [SupSet α]
  [LE β] [LT β] [Sup β] [SupSet β]
  [IsCompleteSemiLatticeSup α]
  [IsSemiLatticeSup β]
  (h: β ≃o α)
  (hs: ∀s: Set β, sSup s = h.symm (sSup (s.preimage h.symm)))
  : IsCompleteSemiLatticeSup β where
  le_sSup := by
    intro s x mem
    rw [hs]
    apply h.resp_le.mpr
    rw [h.symm_coe]
    apply le_sSup
    show h.symm (h x) ∈ s
    rw [h.coe_symm]
    exact mem
  sSup_le := by
    intro k s g
    rw [hs]
    apply h.resp_le.mpr
    rw [h.symm_coe]
    apply sSup_le
    intro x mem
    apply h.symm.resp_le.mpr
    rw [h.coe_symm]
    exact g _ mem

def instIsCompleteSemiLatticeInf
  [LE β] [LT β] [Inf β] [InfSet β]
  [IsCompleteSemiLatticeInf α]
  [IsSemiLatticeInf β]
  (h: β ≃o α)
  (hs: ∀s: Set β, sInf s = h.symm (sInf (s.preimage h.symm)))
  : IsCompleteSemiLatticeInf β :=
  let h': Opposite β ≃o Opposite α := Opposite.orderIsoCongr h
  have := instIsCompleteSemiLatticeSup h' hs
  inferInstanceAs (
    IsCompleteSemiLatticeInf (Opposite (Opposite β))
  )

end OrderIso

instance
  {α} [LE α] [LT α] [SupSet α] [Sup α] [IsCompleteSemiLatticeSup α] : IsCompleteSemiLatticeSup (WithTop α) where
  sSup_le := by
    intro k s h
    simp [sSup]
    split <;> rename_i g
    rcases g with g | g
    exact h _ g
    have := not_exists.mp g
    cases k
    rfl
    rename_i k
    exfalso
    apply this k
    intro a mem
    replace mem := Set.mem_preimage.mp mem
    cases h _ mem
    assumption
    cases k
    apply WithTop.LE.top
    rename_i k
    apply WithTop.LE.of
    apply sSup_le
    intro x mem
    cases h x mem
    assumption
  le_sSup := by
    intro s x mem
    simp [sSup]
    cases x
    rw [if_pos (.inl mem)]
    split
    apply WithTop.LE.top
    apply WithTop.LE.of
    apply le_sSup
    exact mem

-- instance
--   {α} [LE α] [LT α] [InfSet α] [Inf α] [IsCompleteSemiLatticeInf α] : IsCompleteSemiLatticeInf (WithTop α) where
--   sInf_le := by
--     intro s x mem
--     simp [sInf]
--     split <;> rename_i h
--     rcases h with h | h
--     cases Set.mem_singleton.mp <| h _ mem
--     rfl
--     · cases x
--       rfl
--       rename_i x
--       exfalso

--       -- replace ⟨k, h⟩ := Classical.not_forall.mp <| not_exists.mp h x
--       -- have ⟨k_in_s, x_not_le_k⟩ := not_imp.mp h
--       sorry
--     cases x
--     apply WithTop.LE.top
--     apply WithTop.LE.of
--     apply sInf_le
--     exact mem
--   le_sInf := sorry
