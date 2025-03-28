import Math.Order.Lattice.ConditionallyComplete
import Math.Data.Set.Order.Bounds
import Math.Data.Set.TopBot

section

variable (α: Type*) [Sup α] [Inf α] [SupSet α] [InfSet α] [LE α] [LT α] [Top α] [Bot α]
variable {α₀: Type*} [Sup α₀] [Inf α₀] [SupSet α₀] [InfSet α₀] [LE α₀] [LT α₀] [Top α₀] [Bot α₀]

class IsCompleteSemiLatticeSup : Prop extends IsLawfulSupSet α, IsSemiLatticeSup α where
  sSup_le: ∀k: α, ∀s: Set α, (∀x ∈ s, x ≤ k) -> sSup s ≤ k

export IsCompleteSemiLatticeSup (sSup_le)

class IsCompleteSemiLatticeInf : Prop extends IsLawfulInfSet α, IsSemiLatticeInf α where
  le_sInf: ∀k: α, ∀s: Set α, (∀x ∈ s, k ≤ x) -> k ≤ sInf s

export IsCompleteSemiLatticeInf (le_sInf)

class IsCompleteLattice : Prop extends IsLattice α, IsCompleteSemiLatticeSup α, IsCompleteSemiLatticeInf α, IsLawfulBot α, IsLawfulTop α where
  mk' ::

instance IsCompleteLattice.mk [IsLattice α] [IsCompleteSemiLatticeSup α] [IsCompleteSemiLatticeInf α] [IsLawfulBot α] [IsLawfulTop α] : IsCompleteLattice α where
  sSup_le := IsCompleteSemiLatticeSup.sSup_le
  le_sInf := IsCompleteSemiLatticeInf.le_sInf

class CompleteSemiLatticeSup extends LawfulSupSet α, SemiLatticeSup α where
  sSup_le: ∀k: α, ∀s: Set α, (∀x ∈ s, x ≤ k) -> sSup s ≤ k
class CompleteSemiLatticeInf extends LawfulInfSet α, SemiLatticeInf α where
  le_sInf: ∀k: α, ∀s: Set α, (∀x ∈ s, k ≤ x) -> k ≤ sInf s
class CompleteLattice extends CompleteSemiLatticeSup α, CompleteSemiLatticeInf α, LawfulTop α, LawfulBot α where
  mk' ::

end

variable (α: Type*) [LE α] [LT α] [IsPartialOrder α]

def CompleteLattice.mk [CompleteSemiLatticeSup α] [h: CompleteSemiLatticeInf α] [LawfulTop α] [LawfulBot α] : CompleteLattice α where
  le_inf := h.le_inf
  le_sInf := h.le_sInf

instance [Inf α] [InfSet α] [IsCompleteSemiLatticeInf α] : IsCompleteSemiLatticeSup αᵒᵖ where
  sSup_le := le_sInf (α := α)

instance [Sup α] [SupSet α] [IsCompleteSemiLatticeSup α] : IsCompleteSemiLatticeInf αᵒᵖ where
  le_sInf := sSup_le (α := α)

instance [Sup α] [SupSet α] [Inf α] [InfSet α] [Top α] [Bot α] [IsCompleteLattice α] : IsCompleteLattice αᵒᵖ where
  le_top := bot_le (α := α)
  bot_le := le_top (α := α)
  sSup_le := sSup_le
  le_sInf := le_sInf

instance [Sup α] [SupSet α] [Inf α] [InfSet α] [Top α] [Bot α] [IsCompleteLattice α] : IsConditionallyCompleteLattice α where
  le_csInf _ := le_sInf _ _
  le_csSup _ := le_sSup
  csSup_le _ := sSup_le _ _
  csInf_le _ := sInf_le

instance [h: CompleteSemiLatticeSup α] : IsCompleteSemiLatticeSup α where
  le_sSup := h.le_sSup
  sSup_le := h.sSup_le
instance [h: CompleteSemiLatticeInf α] : IsCompleteSemiLatticeInf α where
  le_sInf := h.le_sInf
  sInf_le := h.sInf_le
instance [h: CompleteLattice α] : IsCompleteLattice α where
  le_sSup := h.le_sSup
  sSup_le := h.sSup_le
  le_sInf := h.le_sInf
  sInf_le := h.sInf_le

instance [h: CompleteSemiLatticeInf α] : CompleteSemiLatticeSup αᵒᵖ where
  sSup_le := le_sInf (α := α)
instance [h: CompleteSemiLatticeSup α] : CompleteSemiLatticeInf αᵒᵖ where
  le_sInf := sSup_le (α := α)
instance [h: CompleteLattice α] : CompleteLattice αᵒᵖ := CompleteLattice.mk _

variable (α: Type*) [Sup α] [Inf α] [SupSet α] [InfSet α] [LE α] [LT α] [Top α] [Bot α]
variable {α₀: Type*} [Sup α₀] [Inf α₀] [SupSet α₀] [InfSet α₀] [LE α₀] [LT α₀] [Top α₀] [Bot α₀]

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

@[simp]
def sSup_empty [IsLawfulBot α₀] : sSup ∅ = (⊥: α₀) := by
  apply le_antisymm
  apply sSup_empty_le
  apply bot_le

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

@[simp]
def sInf_empty [IsLawfulTop α₀] : sInf ∅ = (⊤: α₀) :=
  sSup_empty (α₀ := Opposite α₀)

end

section

variable [IsCompleteLattice α₀] {s t : Set α₀} {a b : α₀}

@[simp]
def sSup_univ [IsCompleteLattice α] : sSup (Set.univ α) = (⊤: α) := by
  apply le_antisymm
  apply le_top
  apply le_sSup_univ

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

def isLUB_sSup (s: Set α₀) : s.IsLUB (sSup s) := by
  apply And.intro
  intro x hx
  apply le_sSup
  assumption
  intro x hx
  apply sSup_le
  intro y hy
  apply hx
  assumption

def isGLB_sInf (s: Set α₀) : s.IsGLB (sInf s) :=
  isLUB_sSup (α₀ := α₀ᵒᵖ) s

end

namespace OrderEmbedding

def instIsCompleteSemiLatticeSup
  {α}
  [LE α] [LT α] [Sup α] [SupSet α]
  [LE β] [LT β] [Sup β] [SupSet β]
  [IsCompleteSemiLatticeSup α]
  [IsSemiLatticeSup β]
  (h: β ↪o α)
  (hs: ∀s: Set β, h (sSup s) = sSup (s.image h))
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

def instIsCompleteSemiLatticeInf
  {α}
  [LE α] [LT α] [Inf α] [InfSet α]
  [LE β] [LT β] [Inf β] [InfSet β]
  [IsCompleteSemiLatticeInf α]
  [IsSemiLatticeInf β]
  (h: β ↪o α)
  (hs: ∀s: Set β, h (sInf s) = sInf (s.image h))
  : IsCompleteSemiLatticeInf β :=
  let h': Opposite β ↪o Opposite α := Opposite.orderEmbeddingCongr h
  have := instIsCompleteSemiLatticeSup h' hs
  inferInstanceAs (
    IsCompleteSemiLatticeInf (Opposite (Opposite β))
  )

end OrderEmbedding

namespace OrderIso

def instIsCompleteSemiLatticeSup
  {α}
  [LE α] [LT α] [Sup α] [SupSet α]
  [LE β] [LT β] [Sup β] [SupSet β]
  [IsCompleteSemiLatticeSup α]
  [IsSemiLatticeSup β]
  (h: β ≃o α)
  (hs: ∀s: Set β, sSup s = h.symm (sSup (s.preimage h.symm)))
  : IsCompleteSemiLatticeSup β :=
  h.toEmbedding.instIsCompleteSemiLatticeSup <| by
  intro s
  show h _ = sSup (Set.image _ h)
  rw [hs]
  rw [h.symm_coe]
  congr
  rw [←Set.image_preimage (s.image h) h.symm, Set.image_image, Set.image_id']
  intro; dsimp; rw [h.coe_symm]
  exact h.symm.inj

def instIsCompleteSemiLatticeInf
  {α}
  [LE α] [LT α] [Inf α] [InfSet α]
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

def sInf_sdiff_top [IsCompleteSemiLatticeInf α₀] [IsLawfulTop α₀] (s: Set α₀) :
  sInf s = sInf (s \ {⊤}) := by
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
  sSup s = sSup (s \ {⊥}) := sInf_sdiff_top (α₀ := Opposite α₀) s

instance {α} [LE α] [LT α] [InfSet α] [Inf α] [IsCompleteSemiLatticeInf α] : IsCompleteSemiLatticeInf (WithTop α) where
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

instance {α} [LE α] [LT α] [SupSet α] [Sup α] [IsCompleteSemiLatticeSup α] : IsCompleteSemiLatticeSup (WithTop α) where
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

instance {α} [LE α] [LT α] [InfSet α] [Inf α] [IsCompleteSemiLatticeInf α] : IsCompleteSemiLatticeInf (WithBot α) :=
  WithBot.orderIsoWithTop.instIsCompleteSemiLatticeInf fun _ => rfl

instance {α} [LE α] [LT α] [SupSet α] [Sup α] [IsCompleteSemiLatticeSup α] : IsCompleteSemiLatticeSup (WithBot α) :=
  WithBot.orderIsoWithTop.instIsCompleteSemiLatticeSup fun _ => rfl

instance Opposite.instCompleteLatticeSup {α} [LE α] [LT α] [InfSet α] [Inf α] [IsCompleteSemiLatticeInf α] : IsCompleteSemiLatticeSup (Opposite α) where
  sSup_le := le_sInf (α := α)
instance Opposite.instCompleteLatticeInf {α} [LE α] [LT α] [SupSet α] [Sup α] [IsCompleteSemiLatticeSup α] : IsCompleteSemiLatticeInf (Opposite α) where
  le_sInf := sSup_le (α := α)
instance Opposite.instCompleteLattice {α} [LE α] [LT α] [SupSet α] [Sup α] [InfSet α] [Inf α] [Top α] [Bot α] [inst: IsCompleteLattice α] : IsCompleteLattice (Opposite α) := {
    Opposite.instCompleteLatticeSup, Opposite.instCompleteLatticeInf with
}

def CompleteSemiLatticeSup.opposite (c: CompleteSemiLatticeSup α) : CompleteSemiLatticeInf αᵒᵖ := inferInstance
def CompleteSemiLatticeInf.opposite (c: CompleteSemiLatticeInf α) : CompleteSemiLatticeSup αᵒᵖ := inferInstance
def CompleteLattice.opposite (c: CompleteLattice α) : CompleteLattice αᵒᵖ := inferInstance
