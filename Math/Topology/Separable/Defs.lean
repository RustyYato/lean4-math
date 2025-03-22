import Math.Topology.Filter.Defs
import Math.Order.Disjoint

open FilterBase

namespace Topology

variable {X: Type*} [Topology X]

class T0 (X: Type*) [Topology X]: Prop where
  proof: ∀{a b: X}, Inseparable a b -> a = b

abbrev R0 (X: Type*) [Topology X]: Prop := Relation.IsSymmetric (Specializes : X → X → Prop)

class T1 (X: Type*) [Topology X]: Prop where
  proof: ∀x, IsClosed ({x} : Set X)

class R1 (X: Type*) [Topology X]: Prop where
  specializes_or_disjoint_nhds (x y: X): Specializes x y ∨ Disjoint (𝓝 x) (𝓝 y)

class T2 (X: Type*) [Topology X]: Prop where
  proof: Pairwise fun x y : X => Disjoint (𝓝 x) (𝓝 y)

def Inseparable.eq [T0 X] {a b: X} (h: Inseparable a b) : a = b := T0.proof h

def Specializes.symm [R0 X] {x y: X} (h: Specializes x y) : Specializes y x := Relation.symm h

def specializes_iff_inseparable [R0 X] {x y: X} : Specializes x y ↔ Inseparable x y := by
  apply Iff.intro
  intro h
  apply le_antisymm
  assumption
  apply Specializes.symm
  assumption
  intro h
  unfold Specializes
  rw [h]

def specializes_or_disjoint_nhds [R1 X] (x y: X): Specializes x y ∨ Disjoint (𝓝 x) (𝓝 y) :=
  R1.specializes_or_disjoint_nhds x y

instance [R1 X] : R0 X where
  symm := by
    intro a b hab s hs
    apply (specializes_or_disjoint_nhds b a).resolve_right
    intro h
    have nbhd_eq_bot := le_antisymm (h (𝓝 a) hab (le_refl _)) (bot_le _)
    suffices ∅ ∈ 𝓝 a by
      rw [mem_nhds] at this
      obtain ⟨_, h, _, _⟩ := this
      cases Set.sub_empty _ h
      contradiction
    rw [nbhd_eq_bot]
    trivial
    assumption

def r1Space_iff_inseparable_or_disjoint_nhds : R1 X ↔ ∀ x y : X, Inseparable x y ∨ Disjoint (𝓝 x) (𝓝 y) := by
    apply Iff.intro
    intro h
    intro x y
    rcases specializes_or_disjoint_nhds x y with h | h
    left; apply le_antisymm
    assumption
    exact h.symm
    right; assumption
    intro h
    refine ⟨fun x y => ?_⟩
    rcases h x y with h | h
    left
    unfold Specializes
    rw [h]
    right; assumption

@[simp]
def disjoint_nhds_nhds [T2 X] {x y : X} : Disjoint (𝓝 x) (𝓝 y) ↔ x ≠ y := by
  apply Iff.intro
  rintro h rfl
  rw [disjoint_self] at h
  revert h
  apply NeBot.ne
  apply T2.proof

instance [T2 X] : R1 X where
  specializes_or_disjoint_nhds := by
    intro x y
    by_cases h:x = y
    left; rw [h]
    right; rwa [disjoint_nhds_nhds]

instance T1Space.t0Space [T1 X] : T0 X where
  proof := by
    intro a b h
    have := IsOpen.inter (T1.proof a) (T1.proof b)

    sorry

instance [T2 X] : T1 X where
  proof := by
    intro a
    sorry

def Inseparable.of_nhds_neBot [R1 X] {x y : X} (h: NeBot (𝓝 x ⊓ 𝓝 y)) : Inseparable x y :=
  (r1Space_iff_inseparable_or_disjoint_nhds.mp inferInstance _ _).resolve_right fun h' => h.ne <| by
    apply flip le_antisymm
    apply bot_le
    apply h'
    apply LawfulInf.inf_le_left
    apply LawfulInf.inf_le_right

end Topology
