import Math.Topology.Basic
import Math.Order.Partial
import Math.Data.Set.Lattice

namespace Topology

instance : LE (Topology α) where
  le a b := b.OpenSets ⊆ a.OpenSets

instance : LT (Topology α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : LawfulBot (Topology α) where
  bot_le _ := Set.sub_univ _

instance : LawfulTop (Topology α) where
  le_top T := by
    intro s h
    cases h
    apply IsOpen.empty
    apply IsOpen.univ

def orderEmbedSet : OrderEmbedding (Topology α) (OrderDual (Set (Set α))) where
  toFun t := t.OpenSets
  inj := Topology.OpenSets.inj
  resp_rel := Iff.rfl

instance : IsPreOrder (Topology α) :=
  orderEmbedSet.inducedIsPreOrder <| by
    intros
    rfl
instance : IsPartialOrder (Topology α) :=
  orderEmbedSet.inducedIsPartialOrder

def sSup' (Ts: Set (Topology α)) : Topology α where
  IsOpen x := x ∈ sInf (Ts.image Topology.OpenSets)
  univ_open := by
    dsimp
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
    dsimp at h
    erw [Set.mem_sInter]
    intro x ⟨T, T_in_Ts, _⟩
    subst x
    apply IsOpen.sUnion
    intro x x_in_s
    have := h x x_in_s
    erw [Set.mem_sInter] at this
    exact this T.OpenSets (Set.mem_image' T_in_Ts)

def sInf' (Ts: Set (Topology α)) : Topology α
  := generate (sSup (Ts.image Topology.OpenSets))

instance : SupSet (Topology α) where
  sSup := sSup'
instance : InfSet (Topology α) where
  sInf s := sInf' s

instance : Sup (Topology α) where
  sup a b := sSup {a, b}

instance : Inf (Topology α) where
  inf a b := sInf {a, b}

private def sSup_le: ∀ (k : Topology α) (s : Set (Topology α)), (∀ (x : Topology α), x ∈ s → x ≤ k) → sSup s ≤ k := by
  intro k Ts h s s_open x ⟨T, T_in_Ts, eq⟩
  subst x
  apply h
  assumption
  assumption

private def le_sSup : ∀ (s : Set (Topology α)) (x : Topology α), x ∈ s → x ≤ sSup s := by
  intro Ts T T_in_Ts s s_in_sSup
  exact s_in_sSup T.OpenSets (Set.mem_image' T_in_Ts)

private def sInf_le : ∀ (s : Set (Topology α)) (x : Topology α), x ∈ s → sInf s ≤ x := by
  intro Ts T T_in_Ts x x_open
  apply Generate.IsOpen.of
  exists T.OpenSets
  apply And.intro
  apply Set.mem_image'
  assumption
  assumption

private def le_sInf : ∀ (k : Topology α) (s : Set (Topology α)), (∀ (x : Topology α), x ∈ s → k ≤ x) → k ≤ sInf s := by
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
  le_sSup := le_sSup
  le_sup_left a b := by
    apply le_sSup
    apply Set.mem_pair.mpr; left; rfl
  le_sup_right a b := by
    apply le_sSup
    apply Set.mem_pair.mpr; right; rfl
  sup_le := by
    intro a b k ak bk
    apply sSup_le
    intro x mem
    cases Set.mem_pair.mp mem <;> subst x <;> assumption
  sInf_le := sInf_le
  le_sInf := le_sInf
  inf_le_left := by
    intro a b
    apply sInf_le
    apply Set.mem_pair.mpr; left; rfl
  inf_le_right := by
    intro a b
    apply sInf_le
    apply Set.mem_pair.mpr; right; rfl
  le_inf := by
    intro a b k ka kb
    apply le_sInf
    intro x mem
    cases Set.mem_pair.mp mem <;> subst x <;> assumption

end Topology
