import Math.Order.Lattice.ConditionallyComplete
import Math.Data.Set.Order.Bounds
import Math.Data.Set.TopBot

section

class CompleteLatticeOps (α: Type*) extends ConditionallyCompleteLatticeOps α, Top α, Bot α where

instance [LE α] [LT α] [Min α] [Max α] [SupSet α] [InfSet α] [Top α] [Bot α] : CompleteLatticeOps α where

variable (α: Type*) [Max α] [Min α] [SupSet α] [InfSet α] [LE α] [LT α] [Top α] [Bot α]
variable {α₀: Type*} [Max α₀] [Min α₀] [SupSet α₀] [InfSet α₀] [LE α₀] [LT α₀] [Top α₀] [Bot α₀]

class IsCompleteSemiLatticeSup : Prop extends IsLawfulSupSet α, IsSemiLatticeMax α where
  sSup_le: ∀k: α, ∀s: Set α, (∀x ∈ s, x ≤ k) -> ⨆ s ≤ k

export IsCompleteSemiLatticeSup (sSup_le)

class IsCompleteSemiLatticeMin : Prop extends IsLawfulInfSet α, IsSemiLatticeMin α where
  le_sInf: ∀k: α, ∀s: Set α, (∀x ∈ s, k ≤ x) -> k ≤ ⨅ s

export IsCompleteSemiLatticeMin (le_sInf)

class IsCompleteLattice : Prop extends IsLattice α, IsCompleteSemiLatticeSup α, IsCompleteSemiLatticeMin α, IsLawfulBot α, IsLawfulTop α where
  mk' ::

instance IsCompleteLattice.mk [IsLattice α] [IsCompleteSemiLatticeSup α] [IsCompleteSemiLatticeMin α] [IsLawfulBot α] [IsLawfulTop α] : IsCompleteLattice α where
  sSup_le := IsCompleteSemiLatticeSup.sSup_le
  le_sInf := IsCompleteSemiLatticeMin.le_sInf

class CompleteSemiLatticeSup extends LawfulSupSet α, SemiLatticeMax α where
  sSup_le: ∀k: α, ∀s: Set α, (∀x ∈ s, x ≤ k) -> ⨆ s ≤ k
class CompleteSemiLatticeMin extends LawfulInfSet α, SemiLatticeMin α where
  le_sInf: ∀k: α, ∀s: Set α, (∀x ∈ s, k ≤ x) -> k ≤ ⨅ s
class CompleteLattice extends CompleteSemiLatticeSup α, CompleteSemiLatticeMin α, LawfulTop α, LawfulBot α where
  mk' ::

end

variable (α: Type*) [LE α] [LT α] [IsPartialOrder α]

def CompleteLattice.mk [CompleteSemiLatticeSup α] [h: CompleteSemiLatticeMin α] [LawfulTop α] [LawfulBot α] : CompleteLattice α where
  le_min := h.le_min
  le_sInf := h.le_sInf

instance [Min α] [InfSet α] [IsCompleteSemiLatticeMin α] : IsCompleteSemiLatticeSup αᵒᵖ where
  sSup_le := le_sInf (α := α)

instance [Max α] [SupSet α] [IsCompleteSemiLatticeSup α] : IsCompleteSemiLatticeMin αᵒᵖ where
  le_sInf := sSup_le (α := α)

instance [Max α] [SupSet α] [Min α] [InfSet α] [Top α] [Bot α] [IsCompleteLattice α] : IsCompleteLattice αᵒᵖ where
  le_top := bot_le (α := α)
  bot_le := le_top (α := α)
  sSup_le := sSup_le
  le_sInf := le_sInf

instance [Max α] [SupSet α] [Min α] [InfSet α] [Top α] [Bot α] [IsCompleteLattice α] : IsConditionallyCompleteLattice α where
  le_csInf _ := le_sInf _ _
  le_csSup _ := le_sSup
  csSup_le _ := sSup_le _ _
  csInf_le _ := sInf_le

instance [h: CompleteSemiLatticeSup α] : IsCompleteSemiLatticeSup α where
  le_sSup := h.le_sSup
  sSup_le := h.sSup_le
instance [h: CompleteSemiLatticeMin α] : IsCompleteSemiLatticeMin α where
  le_sInf := h.le_sInf
  sInf_le := h.sInf_le
instance [h: CompleteLattice α] : IsCompleteLattice α where
  le_sSup := h.le_sSup
  sSup_le := h.sSup_le
  le_sInf := h.le_sInf
  sInf_le := h.sInf_le

instance [h: CompleteSemiLatticeMin α] : CompleteSemiLatticeSup αᵒᵖ where
  sSup_le := le_sInf (α := α)
instance [h: CompleteSemiLatticeSup α] : CompleteSemiLatticeMin αᵒᵖ where
  le_sInf := sSup_le (α := α)
instance [h: CompleteLattice α] : CompleteLattice αᵒᵖ := CompleteLattice.mk _

variable (α: Type*) [Max α] [Min α] [SupSet α] [InfSet α] [LE α] [LT α] [Top α] [Bot α]
variable {α₀: Type*} [Max α₀] [Min α₀] [SupSet α₀] [InfSet α₀] [LE α₀] [LT α₀] [Top α₀] [Bot α₀]

section

variable [IsCompleteSemiLatticeSup α₀] {s t : Set α₀} {a b : α₀}

@[simp]
def sSup_le_iff : ⨆ s ≤ a ↔ ∀b ∈ s, b ≤ a := by
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
def sSup_singleton : ⨆ ({ x }: Set α₀) = x := by
  apply le_antisymm
  apply sSup_le
  intro y mem
  rw [mem]
  apply le_sSup
  rfl

@[simp]
def sSup_union : ⨆ (s ∪ t) = (⨆ s) ⊔ ⨆ t := by
  apply le_antisymm
  apply sSup_le
  intro k mem
  rcases Set.mem_union.mp mem with h | h
  apply le_trans _ (le_max_left _ _)
  apply le_sSup
  assumption
  apply le_trans _ (le_max_right _ _)
  apply le_sSup
  assumption
  apply max_le
  apply sSup_le
  intro x mem
  apply le_sSup; apply Set.mem_union.mpr; left; assumption
  apply sSup_le
  intro x mem
  apply le_sSup; apply Set.mem_union.mpr; right; assumption

@[simp]
def sSup_insert : ⨆ (insert a s) = a ⊔ ⨆ s := by
  erw [sSup_union, sSup_singleton]

def sSup_le_sSup (h: s ⊆ t) : ⨆ s ≤ ⨆ t := by
  apply sSup_le
  intro x mem_s
  apply le_sSup
  apply h
  assumption

def sSup_empty_le : ∀x: α₀, ⨆ ∅ ≤ x := by
  intro x
  apply sSup_le
  intro x mem_s
  contradiction

def le_sSup_univ : ∀x: α₀, x ≤ ⨆ (Set.univ _) := by
  intro x
  apply le_sSup
  apply Set.mem_univ

@[simp]
def sSup_empty [IsLawfulBot α₀] : ⨆ ∅ = (⊥: α₀) := by
  apply le_antisymm
  apply sSup_empty_le
  apply bot_le

end

section

variable [IsCompleteSemiLatticeMin α₀] {s t : Set α₀} {a b : α₀}

@[simp]
def le_sInf_iff : a ≤ ⨅ s ↔ ∀b ∈ s, a ≤ b :=
  sSup_le_iff (α₀ := Opposite α₀)

@[simp]
def sInf_singleton : ⨅ ({ x }: Set α₀) = x :=
  sSup_singleton (α₀ := Opposite α₀)

@[simp]
def sInf_union : ⨅ (s ∪ t) = (⨅ s) ⊓ ⨅ t :=
  sSup_union (α₀ := Opposite α₀)

@[simp]
def sInf_insert : ⨅ (insert a s) = a ⊓ ⨅ s :=
  sSup_insert (α₀ := Opposite α₀)

def sInf_le_sInf (h: s ⊆ t) : ⨅ t ≤ ⨅ s :=
  sSup_le_sSup (α₀ := Opposite α₀) h

def le_sInf_empty : ∀x: α₀, x ≤ (⨅ ∅) := by
  intro x
  apply le_sInf
  intros
  contradiction

def sInf_univ_le : ∀x: α₀, ⨅ (Set.univ _) ≤ x := by
  intro x
  apply sInf_le
  apply Set.mem_univ

@[simp]
def sInf_empty [IsLawfulTop α₀] : ⨅ ∅ = (⊤: α₀) :=
  sSup_empty (α₀ := Opposite α₀)

end

section

variable [IsCompleteLattice α₀] {s t : Set α₀} {a b : α₀}

@[simp]
def sSup_univ [IsCompleteLattice α] : ⨆ (Set.univ α) = (⊤: α) := by
  apply le_antisymm
  apply le_top
  apply le_sSup_univ

@[simp]
def sInf_univ [IsCompleteLattice α] : ⨅ (Set.univ α) = (⊥: α) :=
  sSup_univ (α := Opposite α)

def sInf_le_sSup (h: s.Nonempty) : ⨅ s ≤ ⨆ s := by
  obtain ⟨x, mem⟩ := h
  apply le_trans
  apply sInf_le
  assumption
  apply le_sSup
  assumption

@[simp]
def sSup_inter_le : ⨆ (s ∩ t) ≤ (⨆ s) ⊓ ⨆ t := by
  apply sSup_le
  intro x mem
  have ⟨_, _⟩ := Set.mem_inter.mp mem
  apply le_min
  apply le_sSup; assumption
  apply le_sSup; assumption

@[simp]
def le_sInf_inter : (⨅ s) ⊔ ⨅ t ≤ ⨅ (s ∩ t) :=
  sSup_inter_le (α₀ := Opposite α₀)

@[simp]
def sSup_insert_bot : ⨆ (insert ⊥ s) = ⨆ s := by
  simp

@[simp]
def sSup_insert_top : ⨆ (insert ⊤ s) = ⊤ := by
  simp

@[simp]
def sInf_insert_bot : ⨅ (insert ⊥ s) = ⊥ := by
  simp

@[simp]
def sInf_insert_top : ⨅ (insert ⊤ s) = ⨅ s := by
  simp

def sSup_eq_bot : ⨆ s = ⊥ ↔ ∀x ∈ s, x = ⊥ := by
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

def sInf_eq_top : ⨅ s = ⊤ ↔ ∀x ∈ s, x = ⊤ :=
  sSup_eq_bot (α₀ := Opposite α₀)

def isLUB_sSup (s: Set α₀) : s.IsLUB (⨆ s) := by
  apply And.intro
  intro x hx
  apply le_sSup
  assumption
  intro x hx
  apply sSup_le
  intro y hy
  apply hx
  assumption

def isGLB_sInf (s: Set α₀) : s.IsGLB (⨅ s) :=
  isLUB_sSup (α₀ := α₀ᵒᵖ) s

end

namespace OrderEmbedding

def instIsCompleteSemiLatticeSup
  {α}
  [LE α] [LT α] [Max α] [SupSet α]
  [LE β] [LT β] [Max β] [SupSet β]
  [IsCompleteSemiLatticeSup α]
  [IsSemiLatticeMax β]
  (h: β ↪o α)
  (hs: ∀s: Set β, h (⨆ s) = ⨆ (s.image h))
  : IsCompleteSemiLatticeSup β where
  le_sSup := by
    intro s x mem
    apply h.resp_le.mpr
    rw [hs]
    apply le_sSup
    apply Set.mem_image'
    assumption
  sSup_le := by
    intro k s g
    apply h.resp_le.mpr
    rw [hs]
    apply sSup_le
    intro x ⟨x, _, eq⟩; subst eq
    apply h.resp_le.mp
    apply g
    assumption

def instIsCompleteSemiLatticeMin
  {α}
  [LE α] [LT α] [Min α] [InfSet α]
  [LE β] [LT β] [Min β] [InfSet β]
  [IsCompleteSemiLatticeMin α]
  [IsSemiLatticeMin β]
  (h: β ↪o α)
  (hs: ∀s: Set β, h (⨅ s) = ⨅ (s.image h))
  : IsCompleteSemiLatticeMin β :=
  let h': Opposite β ↪o Opposite α := Opposite.orderEmbeddingCongr h
  have := instIsCompleteSemiLatticeSup h' hs
  inferInstanceAs (
    IsCompleteSemiLatticeMin (Opposite (Opposite β))
  )

end OrderEmbedding

namespace OrderIso

def instIsCompleteSemiLatticeSup
  {α}
  [LE α] [LT α] [Max α] [SupSet α]
  [LE β] [LT β] [Max β] [SupSet β]
  [IsCompleteSemiLatticeSup α]
  [IsSemiLatticeMax β]
  (h: β ≃o α)
  (hs: ∀s: Set β, ⨆ s = h.symm (⨆ (s.preimage h.symm)))
  : IsCompleteSemiLatticeSup β :=
  h.toEmbedding.instIsCompleteSemiLatticeSup <| by
  intro s
  show h _ = ⨆ (Set.image _ h)
  rw [hs]
  rw [h.symm_coe]
  congr
  rw [←Set.image_preimage (s.image h) h.symm, Set.image_image, Set.image_id']
  intro; dsimp; rw [h.coe_symm]
  exact h.symm.inj

def instIsCompleteSemiLatticeMin
  {α}
  [LE α] [LT α] [Min α] [InfSet α]
  [LE β] [LT β] [Min β] [InfSet β]
  [IsCompleteSemiLatticeMin α]
  [IsSemiLatticeMin β]
  (h: β ≃o α)
  (hs: ∀s: Set β, ⨅ s = h.symm (⨅ (s.preimage h.symm)))
  : IsCompleteSemiLatticeMin β :=
  let h': Opposite β ≃o Opposite α := Opposite.orderIsoCongr h
  have := instIsCompleteSemiLatticeSup h' hs
  inferInstanceAs (
    IsCompleteSemiLatticeMin (Opposite (Opposite β))
  )

end OrderIso

instance
  {α} [LE α] [LT α] [SupSet α] [Max α] [IsCompleteSemiLatticeSup α] : IsCompleteSemiLatticeSup (WithTop α) where
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

def sInf_sdiff_top [IsCompleteSemiLatticeMin α₀] [IsLawfulTop α₀] (s: Set α₀) :
  ⨅ s = ⨅ (s \ {⊤}) := by
  apply le_antisymm
  apply sInf_le_sInf
  intro x; exact And.left
  apply le_sInf
  intro x mem
  if h:x = ⊤ then
    subst x
    apply le_top
  else
    apply sInf_le
    apply And.intro
    assumption
    assumption

def sSup_sdiff_bot [IsCompleteSemiLatticeSup α₀] [IsLawfulBot α₀] (s: Set α₀) :
  ⨆ s = ⨆ (s \ {⊥}) := sInf_sdiff_top (α₀ := Opposite α₀) s

instance {α} [LE α] [LT α] [InfSet α] [Min α] [IsCompleteSemiLatticeMin α] : IsCompleteSemiLatticeMin (WithTop α) where
  le_sInf := by
    intro k s h
    cases k
    suffices s ⊆ {⊤} by
      simp [sInf]
      rw [if_pos]
      left; assumption
    intro x mem
    apply le_antisymm
    apply le_top
    apply h
    assumption
    rename_i y
    apply le_trans
    apply WithTop.LE.of
    apply le_sInf _ (s.preimage WithTop.of)
    intro x mem
    cases h x mem
    assumption
    simp [sInf]
    split
    apply le_top
    rfl

instance {α} [LE α] [LT α] [SupSet α] [Max α] [IsCompleteSemiLatticeSup α] : IsCompleteSemiLatticeSup (WithTop α) where
  sSup_le := by
    intro k s h
    simp [sSup]
    split <;> rename_i g
    rcases g with g | g
    apply h
    assumption
    have := not_exists.mp g
    conv at this => {
      intro x; rw [Set.mem_upperBounds]
      conv => { arg 1; intro y; rw [Set.mem_preimage] }
      rw [Classical.not_forall]
      arg 1; intro y
      rw [not_imp]
    }
    cases k
    apply le_top
    rename_i x
    have ⟨x', x'_mem, not_le⟩ := this x
    cases h x' x'_mem
    contradiction
    cases k
    apply le_top
    apply WithTop.LE.of
    apply sSup_le
    intro x mem
    cases h _ mem
    assumption

instance {α} [LE α] [LT α] [InfSet α] [Min α] [IsCompleteSemiLatticeMin α] : IsCompleteSemiLatticeMin (WithBot α) :=
  WithBot.orderIsoWithTop.instIsCompleteSemiLatticeMin fun _ => rfl

instance {α} [LE α] [LT α] [SupSet α] [Max α] [IsCompleteSemiLatticeSup α] : IsCompleteSemiLatticeSup (WithBot α) :=
  WithBot.orderIsoWithTop.instIsCompleteSemiLatticeSup fun _ => rfl

instance Opposite.instCompleteLatticeMax {α} [LE α] [LT α] [InfSet α] [Min α] [IsCompleteSemiLatticeMin α] : IsCompleteSemiLatticeSup (Opposite α) where
  sSup_le := le_sInf (α := α)
instance Opposite.instCompleteLatticeMin {α} [LE α] [LT α] [SupSet α] [Max α] [IsCompleteSemiLatticeSup α] : IsCompleteSemiLatticeMin (Opposite α) where
  le_sInf := sSup_le (α := α)
instance Opposite.instCompleteLattice {α} [LE α] [LT α] [SupSet α] [Max α] [InfSet α] [Min α] [Top α] [Bot α] [inst: IsCompleteLattice α] : IsCompleteLattice (Opposite α) := {
    Opposite.instCompleteLatticeMax, Opposite.instCompleteLatticeMin with
}

def CompleteSemiLatticeSup.opposite (c: CompleteSemiLatticeSup α) : CompleteSemiLatticeMin αᵒᵖ := inferInstance
def CompleteSemiLatticeMin.opposite (c: CompleteSemiLatticeMin α) : CompleteSemiLatticeSup αᵒᵖ := inferInstance
def CompleteLattice.opposite (c: CompleteLattice α) : CompleteLattice αᵒᵖ := inferInstance
