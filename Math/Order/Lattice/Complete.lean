import Math.Order.Lattice.Basic
import Math.Data.Set.Basic

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

class IsCompleteLattice extends IsLattice α, IsCompleteSemiLatticeSup α, IsCompleteSemiLatticeInf α: Prop where
  le_top: ∀x: α, x ≤ ⊤
  bot_le: ∀x: α, ⊥ ≤ x

export IsCompleteLattice (le_top bot_le)
attribute [simp] bot_le le_top

instance [IsCompleteSemiLatticeInf α] : IsCompleteSemiLatticeSup (OrderDual α) where
  le_sSup := sInf_le (α := α)
  sSup_le := le_sInf (α := α)

instance [IsCompleteSemiLatticeSup α] : IsCompleteSemiLatticeInf (OrderDual α) where
  sInf_le := le_sSup (α := α)
  le_sInf := sSup_le (α := α)

instance [IsCompleteLattice α] : IsCompleteLattice (OrderDual α) where
  le_top := bot_le (α := α)
  bot_le := le_top (α := α)
  le_sSup := le_sSup
  sSup_le := sSup_le
  sInf_le := sInf_le
  le_sInf := le_sInf

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
  sSup_le_iff (α₀ := OrderDual α₀)

@[simp]
def sInf_singleton : sInf ({ x }: Set α₀) = x :=
  sSup_singleton (α₀ := OrderDual α₀)

@[simp]
def sInf_union : sInf (s ∪ t) = sInf s ⊓ sInf t :=
  sSup_union (α₀ := OrderDual α₀)

@[simp]
def sInf_insert : sInf (insert a s) = a ⊓ sInf s :=
  sSup_insert (α₀ := OrderDual α₀)

def sInf_le_sInf (h: s ⊆ t) : sInf t ≤ sInf s :=
  sSup_le_sSup (α₀ := OrderDual α₀) h

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
  sSup_empty (α := OrderDual α)

@[simp]
def sInf_univ [IsCompleteLattice α] : sInf (Set.univ α) = (⊥: α) :=
  sSup_univ (α := OrderDual α)

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
  sSup_inter_le (α₀ := OrderDual α₀)

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
  top_sup (α₀ := OrderDual α₀)

@[simp]
def inf_bot : a ⊓ ⊥ = ⊥ :=
  sup_top (α₀ := OrderDual α₀)

@[simp]
def top_inf : ⊤ ⊓ a = a :=
  bot_sup (α₀ := OrderDual α₀)

@[simp]
def inf_top : a ⊓ ⊤ = a :=
  sup_bot (α₀ := OrderDual α₀)

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
  simp
  intro h
  apply le_antisymm
  apply sSup_le
  intro x g
  rw [h x]
  assumption
  simp

def sInf_eq_top : sInf s = ⊤ ↔ ∀x ∈ s, x = ⊤ :=
  sSup_eq_bot (α₀ := OrderDual α₀)

end
