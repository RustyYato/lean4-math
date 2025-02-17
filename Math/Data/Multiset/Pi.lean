import Math.Data.Multiset.Basic
import Math.Function.Basic

local notation "⟦" a "⟧" => (Multiset.mk (a: List _): Multiset _)

namespace Multiset.Pi

variable {α: Type u} {β: α -> Sort v} [DecidableEq α]

def empty : ∀x ∈ (∅: Multiset α), β x := by
  intro x mem
  replace mem : x ∈ ⟦[]⟧ := mem
  rw [mk_mem] at mem
  contradiction

def cons (ms: Multiset α) (f: ∀x ∈ ms, β x) (a: α) (b: β a) : ∀x ∈ a::ₘms, β x := fun x h =>
   if g:x = a
   then g ▸ b
   else f x (by
    induction ms using ind
    simp at *
    cases h
    contradiction
    assumption)

variable {a: α}

def cons_spec_eq {b: β a} {f: ∀x ∈ ms, β x} : cons ms f a b a (by simp) = b := by
  unfold cons
  rw [dif_pos rfl]

def cons_spec_ne {b: β a} {f: ∀x ∈ ms, β x} (h: a' ∈ a::ₘms) (g: a' ≠ a) : cons ms f a b a' h = f a' (by
  simp at h
  cases h
  contradiction
  assumption) := by
  unfold cons
  rw [dif_neg]
  assumption

def cons_spec_swap {a₀ a₁} {b₀: β a₀} {b₁: β a₁} {f: ∀x ∈ ms, β x} (a_ne: a₀ ≠ a₁) :
  HEq (cons _ (cons ms f a₁ b₁) a₀ b₀) (cons _ (cons ms f a₀ b₀) a₁ b₁) := by
  unfold cons
  apply Function.hfunext rfl
  intro a₀' _ eq
  cases eq
  apply Function.hfunext
  simp
  · apply Iff.intro
    iterate 2
      intro h; rcases h with h | h | h
      cases h; simp
      cases h; simp
      right; right; assumption
  intro mem₀ mem₁ mem_eq
  split <;> rename_i h
  subst a₀'
  split <;> rename_i h
  subst a₁
  contradiction
  simp
  simp

theorem cons_eta {m : Multiset α} {a : α} (f : ∀ a' ∈ a ::ₘ m, β a') :
    (cons m (fun a' ha' => f a' (by simp; right; assumption))) a (f _ (by simp)) = f := by
  ext a' h'
  by_cases h : a' = a
  · subst h
    rw [cons_spec_eq]
  · rw [cons_spec_ne _ h]

theorem cons_map (b : β a) (f : ∀ a' ∈ m, β a')
    {β' : α → Sort*} (φ : ∀ ⦃a'⦄, β a' → β' a') :
    Pi.cons _ (fun a' ha' ↦ φ (f a' ha')) _ (φ b) = (fun a' ha' ↦ φ ((cons _ f _ b) a' ha')) := by
  ext a' ha'
  unfold cons
  split
  subst a'
  rfl
  simp

theorem cons_injective {a : α} {b : β a} {s : Multiset α} (hs : a ∉ s) : Function.Injective (Pi.cons s · a b) := by
  intro f₁ f₂ eq
  dsimp at eq
  funext a' h'
  have := congrFun (congrFun eq a') (by simp; right; assumption)
  unfold cons at this
  split at this
  subst a'
  contradiction
  assumption

section
variable {α : Type*} [DecidableEq α] {β : α → Type*}

def pi (m : Multiset α) (t : ∀a, Multiset (β a)) : Multiset (∀a ∈ m, β a) := by
  apply m.rec
  case nil =>
    exact empty ::ₘ ∅
  case cons =>
    intro a aset as
    apply (t a).flatMap
    intro b
    apply as.map
    intro f a' mem
    exact Pi.cons aset f _ b _ mem
  case swap =>
    dsimp
    intro a a' as mas
    by_cases h:a = a'
    subst a'
    rfl
    simp only [flatMap_map, map_map]
    apply flatMap_hcongr





    sorry
end

end Multiset.Pi
