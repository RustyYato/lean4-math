import Math.Order.Filter.Basic
import Math.Order.Directed.Basic

namespace FilterBase

open scoped Classical
open Set

variable {α : Type*} [LE α] [LT α] [Min α] [Top α] [IsLawfulTop α] [InfSet α] [IsCompleteSemiLatticeMin α]

def eq_sInf_of_mem_iff_exists_mem {S : Set (Filter α)} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ f ∈ S, s ∈ f) : l = ⨅ S := by
  apply le_antisymm
  apply le_sInf
  intro f hf s hs
  apply h.mpr
  exists f
  intro x hx
  let ⟨_, hf, hs⟩ := h.mp hx
  apply sInf_le hf
  assumption

def eq_iInf_of_mem_iff_exists_mem {f : ι → Filter α} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ i, s ∈ f i) : l = ⨅i, f i := by
  apply eq_sInf_of_mem_iff_exists_mem
  intro s
  apply h.trans
  apply Iff.intro
  intro ⟨i, _⟩
  exists f i
  apply And.intro
  apply mem_range'
  assumption
  intro ⟨_, ⟨i, rfl⟩, _⟩
  exists i

def iInf_set_eq {f : ι → Filter α} (h : Directed (· ≥ ·) f) [ne : Nonempty ι] :
    (⨅i, f i).set =  ⨆i, (f i).set := by
  let ⟨i⟩ := ne
  let u: Filter α :=
    { set := ⨆i, (f i).set
      nonempty := by
        refine ⟨⊤, ?_⟩
        rw [mem_iSup]
        exists i
        apply top_mem
      closed_upward := by
        simp only [mem_iSup, exists_imp]
        exact fun i hx hxy => ⟨i, closed_upward _ hx hxy⟩
      closed_min := by
        simp only [mem_iSup, exists_imp]
        intro x y a hx b hy
        rcases h a b with ⟨c, ha, hb⟩
        exists c
        apply closed_min
        apply ha; assumption
        apply hb; assumption }
  have : u = ⨅i, f i := eq_iInf_of_mem_iff_exists_mem mem_iSup
  rw [←this]

def mem_iInf_of_directed {f : ι → Filter α} (h : Directed (· ≥ ·) f) [Nonempty ι] (s) :
    s ∈ ⨅i, f i ↔ ∃ i, s ∈ f i := by
  simp only [FilterBase.mem_set, iInf_set_eq h, mem_iSup]

def iInf_neBot_of_directed' {f : ι → Filter α} [Nonempty ι] (hd : Directed (· ≥ ·) f) :
    (∀ i, NeBot (f i)) → NeBot (⨅i, f i) :=
  Classical.contrapositive.mp <| by
    simpa only [Classical.not_forall, not_neBot, ←bot_mem_iff_bot, mem_iInf_of_directed hd] using id

def sInf_neBot_of_directed' {s : Set (Filter α)} (hne : s.Nonempty) (hd : s.DirectedOn (· ≥ ·))
    (hbot : ⊥ ∉ s) : NeBot (⨅ s) := by
  rw [sInf_eq_iInf]
  have : _root_.Nonempty s := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx⟩
  apply iInf_neBot_of_directed' (f := fun _ => _)
  exact (DirectedOn.iff_directed _).mp hd
  intro ⟨_, _⟩
  refine ⟨?_⟩
  dsimp; intro h; subst h
  contradiction

end FilterBase
