import Math.Topology.Basic
import Math.Data.Set.Lattice

namespace Topology

instance : LE (Topology α) where
  le a b := b.OpenSets ⊆ a.OpenSets

instance : LT (Topology α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : IsLawfulBot (Topology α) where
  bot_le _ := Set.sub_univ _

instance : IsLawfulTop (Topology α) where
  le_top T := by
    intro s h
    cases h
    apply IsOpen.empty
    apply IsOpen.univ

def orderEmbedSet : Topology α ↪o Opposite (Set (Set α)) where
  toFun t := t.OpenSets
  inj' := Topology.OpenSets.inj
  map_le _ _ := Iff.rfl

instance : IsLawfulLT (Topology α) where
  lt_iff_le_and_not_le := Iff.rfl

instance : IsPreOrder (Topology α) :=
  orderEmbedSet.instIsPreOrder
instance : IsPartialOrder (Topology α) :=
  orderEmbedSet.instIsPartialOrder

def sSup' (Ts: Set (Topology α)) : Topology α where
  IsOpen x := x ∈ ⨅ (Ts.image Topology.OpenSets)
  univ_open := by
    apply Set.mem_sInter.mpr
    intro x h
    rw [Set.mem_image] at h
    obtain ⟨T, T_in_Ts, eq⟩ := h
    subst eq
    apply IsOpen.univ
  inter_open := by
    intro a b ha hb
    erw [Set.mem_sInter] at *
    intro s mem
    obtain ⟨T, T_in_Ts, eq⟩ := mem
    subst s
    apply IsOpen.inter
    exact ha T.OpenSets (Set.mem_image' T_in_Ts)
    exact hb T.OpenSets (Set.mem_image' T_in_Ts)
  sUnion_open := by
    intro s h
    erw [Set.mem_sInter]
    intro x ⟨T, T_in_Ts, _⟩
    subst x
    apply IsOpen.sUnion
    intro x x_in_s
    have := h x x_in_s
    erw [Set.mem_sInter] at this
    exact this T.OpenSets (Set.mem_image' T_in_Ts)

def max' (ta: Topology α) (tb: Topology α) : Topology α where
  IsOpen x := IsOpen[ta] x ∧ IsOpen[tb] x
  univ_open := by
    apply And.intro
    apply IsOpen.univ
    apply IsOpen.univ
  inter_open := by
    intro a b ⟨_, _⟩ ⟨_, _⟩
    apply And.intro
    apply IsOpen.inter <;> assumption
    apply IsOpen.inter <;> assumption
  sUnion_open := by
    intro s h
    apply And.intro
    apply IsOpen.sUnion
    intro x hx
    apply (h x hx).left
    apply IsOpen.sUnion
    intro x hx
    apply (h x hx).right

def sInf' (Ts: Set (Topology α)) : Topology α
  := generate (⋃(Ts.image Topology.OpenSets))

def min' (ta: Topology α) (tb: Topology α) : Topology α
  := generate (ta.OpenSets ∪ tb.OpenSets)

instance : SupSet (Topology α) where
  sSup := sSup'
instance : InfSet (Topology α) where
  sInf s := sInf' s

instance : Max (Topology α) where
  max := max'

instance : Min (Topology α) where
  min := min'

def max_eq (a b: Topology α) : a ⊔ b = ⨆ {a, b} := by
  show max' a b = sSup' {a, b}
  unfold max' sSup'
  ext s
  simp
  rfl

def min_eq (a b: Topology α) : a ⊓ b = ⨅ {a, b} := by
  show min' a b = sInf' {a, b}
  unfold min' sInf'
  ext s
  simp

private def sSup_le: ∀ (k : Topology α) (s : Set (Topology α)), (∀ (x : Topology α), x ∈ s → x ≤ k) → ⨆ s ≤ k := by
  intro k Ts h s s_open x ⟨T, T_in_Ts, eq⟩
  subst x
  apply h
  assumption
  assumption

private def le_sSup : ∀ (s : Set (Topology α)) (x : Topology α), x ∈ s → x ≤ ⨆ s := by
  intro Ts T T_in_Ts s s_in_sSup
  exact s_in_sSup T.OpenSets (Set.mem_image' T_in_Ts)

private def sInf_le : ∀ (s : Set (Topology α)) (x : Topology α), x ∈ s → ⨅ s ≤ x := by
  intro Ts T T_in_Ts x x_open
  apply Generate.IsOpen.of
  exists T.OpenSets
  apply And.intro
  apply Set.mem_image'
  assumption
  assumption

private def le_sInf : ∀ (k : Topology α) (s : Set (Topology α)), (∀ (x : Topology α), x ∈ s → k ≤ x) → k ≤ ⨅ s := by
  intro T Ts h x x_open
  induction x_open with
  | of g =>
    rename_i s
    obtain ⟨S, ⟨T', T'_in_Ts, _⟩, s_in_S⟩ := g
    subst S
    apply h
    assumption
    assumption
  | univ => apply IsOpen.univ
  | inter => apply IsOpen.inter <;> assumption
  | sUnion => apply IsOpen.sUnion <;> assumption

instance : IsCompleteLattice (Topology α) where
  sSup_le := sSup_le
  le_sSup := le_sSup _ _
  le_max_left a b := by
    rw [max_eq]
    apply le_sSup
    apply Set.mem_pair.mpr; left; rfl
  le_max_right a b := by
    rw [max_eq]
    apply le_sSup
    apply Set.mem_pair.mpr; right; rfl
  max_le := by
    intro a b k ak bk
    rw [max_eq]
    apply sSup_le
    intro x mem
    cases Set.mem_pair.mp mem <;> subst x <;> assumption
  sInf_le := sInf_le _ _
  le_sInf := le_sInf
  min_le_left := by
    intro a b
    rw [min_eq]
    apply sInf_le
    apply Set.mem_pair.mpr; left; rfl
  min_le_right := by
    intro a b
    rw [min_eq]
    apply sInf_le
    apply Set.mem_pair.mpr; right; rfl
  le_min := by
    intro a b k ka kb
    rw [min_eq]
    apply le_sInf
    intro x mem
    cases Set.mem_pair.mp mem <;> subst x <;> assumption

def induced_compose {tγ : Topology γ} {f : α → β} {g : β → γ} :
    (tγ.induced g).induced f = tγ.induced (g ∘ f) := by
  apply Topology.IsOpen.inj
  dsimp
  funext s
  apply propext
  apply Iff.intro
  exact fun ⟨_, ⟨s, hs, h₂⟩, h₁⟩ => h₁ ▸ h₂ ▸ ⟨s, hs, rfl⟩
  exact fun ⟨s, hs, h⟩ => ⟨Set.preimage s g, ⟨s, hs, rfl⟩, h ▸ rfl⟩

def coinduced_le_iff_le_induced {f : α → β} {tα : Topology α}
    {tβ : Topology β} : tα.coinduced f ≤ tβ ↔ tα ≤ tβ.induced f :=
  ⟨fun h _s ⟨_t, ht, hst⟩ => hst ▸ h _ ht, fun h s hs => h _ ⟨s, hs, rfl⟩⟩

def continuous_iff_coinduced_le {t₁ : Topology α} {t₂ : Topology β} :
    IsContinuous' t₁ t₂ f ↔ coinduced f t₁ ≤ t₂ := by
    apply Iff.intro
    intro h
    exact h.1
    exact IsContinuous.mk

def continuous_iff_le_induced {t₁ : Topology α} {t₂ : Topology β} :
    IsContinuous' t₁ t₂ f ↔ t₁ ≤ induced f t₂ := by
    apply Iff.trans _ coinduced_le_iff_le_induced
    exact continuous_iff_coinduced_le

def continuous_induced_rng {g : γ → α} {t₂ : Topology β} {t₁ : Topology γ} :
    IsContinuous' t₁ (induced f t₂) g ↔ IsContinuous' t₁ t₂ (f ∘ g) := by
  simp only [continuous_iff_le_induced, induced_compose]

def continuous_min_rng {t₁ : Topology α} {t₂ t₃ : Topology β} :
    IsContinuous' t₁  (t₂ ⊓ t₃) f ↔ IsContinuous' t₁ t₂ f ∧ IsContinuous' t₁ t₃ f := by
  simp only [continuous_iff_coinduced_le, le_min_iff]

def continuous_max_rng_left {t₁ : Topology α} {t₂ t₃ : Topology β} :
    IsContinuous' t₁ t₂ f -> IsContinuous' t₁  (t₂ ⊔ t₃) f := by
  simp only [continuous_iff_coinduced_le]
  intro h
  apply le_trans h
  apply le_max_left

def continuous_max_rng_right {t₁ : Topology α} {t₂ t₃ : Topology β} :
    IsContinuous' t₁ t₃ f -> IsContinuous' t₁  (t₂ ⊔ t₃) f := by
  simp only [continuous_iff_coinduced_le]
  intro h
  apply le_trans h
  apply le_max_right

def continuous_sSup_dom {T : Set (Topology α)} {t₂ : Topology β} :
    IsContinuous' (⨆ T) t₂ f ↔ ∀ t ∈ T, IsContinuous' t t₂ f := by
  simp only [continuous_iff_le_induced, sSup_le_iff]

instance [Subsingleton α] : Subsingleton (Topology α) where
  allEq := by
    intro a b
    let topT := inferInstanceAs (Topology.Trivial α)
    have bot_eq_top : ⊥ = (⊤: Topology α) := topT.eq_top
    rw [show a = ⊥ from ?_, show b = ⊥ from ?_]
    all_goals
      apply le_antisymm
      rw [bot_eq_top]
      apply le_top
      apply bot_le

end Topology
