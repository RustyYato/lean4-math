import Math.Order.Linear
import Math.Order.Lattice.ConditionallyComplete

open Set hiding Nonempty

section

variable [SupSet α] [InfSet α] [Max α] [Min α] [LE α] [LT α]
variable [IsPartialOrder α] [@Relation.IsWellFounded α (· < ·)] [@Relation.IsConnected α (· < ·)]
variable {a b c: α} {s t: Set α} [IsConditionallyCompleteLattice α]

variable [IsConditionallyCompleteLattice α]

def sInf_eq_argmin_on (hs : s.Nonempty) :
  have : Nonempty s := by
    obtain ⟨x, h⟩ := hs
    exact ⟨x, h⟩
  ⨅ s = Relation.argMin (fun x: s => x.val) (· < ·) := by
  have : Nonempty s := by
    obtain ⟨x, h⟩ := hs
    exact ⟨x, h⟩
  apply IsLeast.csInf_eq
  apply And.intro
  apply Subtype.property
  intro a ha
  have ⟨h, spec⟩ := Classical.choose_spec (Relation.exists_min (fun x y: s => x.val < y.val) (P := fun _ => True) ⟨⟨a, ha⟩, True.intro⟩)
  dsimp at spec; clear h
  have := spec ⟨a, ha⟩
  conv at this => { rhs; rw [not_true] }
  exact le_of_not_lt this

def csInf_mem (hs : s.Nonempty) : ⨅ s ∈ s := by
  rw [sInf_eq_argmin_on]
  apply Subtype.property
  assumption

def ciInf_mem [Nonempty ι] (f : ι → α) : ⨅i, f i ∈ range f :=
  csInf_mem (nonempty_range f)

end
