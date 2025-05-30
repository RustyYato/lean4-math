import Math.Data.LazyFinset.Defs

class LazyFinsetLike (S: Type*) (α: outParam Type*) where
  coe : S -> LazyFinset α
  coe_inj : Function.Injective coe

@[coe]
def LazyFinset.coe [LazyFinsetLike S α] : S -> LazyFinset α := LazyFinsetLike.coe
def LazyFinset.coe.inj [LazyFinsetLike S α] : Function.Injective (LazyFinset.coe (S := S)) := LazyFinsetLike.coe_inj

instance [LazyFinsetLike S α] : CoeTC S (LazyFinset α) where
  coe := LazyFinset.coe

namespace LazyFinset

variable [LazyFinsetLike S α]

scoped instance : Membership α S where
  mem s a := a ∈ (s: LazyFinset α)

scoped instance : HasSubset S where
  Subset a b := (a: LazyFinset α) ⊆ (b: LazyFinset α)

def coe_ext (a b: S) : (∀x: α, x ∈ (a: LazyFinset α) ↔ x ∈ (b: LazyFinset α)) -> a = b := by
  intro h
  apply coe.inj
  ext; apply h

instance : LazyFinsetLike (LazyFinset α) α where
  coe := id
  coe_inj _ _ := id

@[simp]
def coe_mem (s: S) (a: α) : a ∈ (s: LazyFinset α) ↔ a ∈ s := Iff.rfl

@[simp]
def coe_sub (a b: S) : (a: LazyFinset α) ⊆ (b: LazyFinset α) ↔ a ⊆ b := Iff.rfl

end LazyFinset

def Nat.toLazyFinset (n: ℕ) := LazyFinset.ofMultiset (Multiset.mk (List.ofFn (n := n) Fin.val))

def Nat.mem_toLazyFinset (n: ℕ) : ∀{x}, x ∈ n.toLazyFinset ↔ x < n := by
  intro x
  simp [toLazyFinset]
  apply Iff.intro
  rintro ⟨i, rfl⟩
  apply Fin.isLt
  intro h
  exists ⟨_, h⟩

instance : LazyFinsetLike Nat Nat where
  coe s := s.toLazyFinset
  coe_inj := by
    intro x y h
    simp at h
    rcases Nat.lt_trichotomy x y with g | g | g
    · rw [←Nat.mem_toLazyFinset, ←h, Nat.mem_toLazyFinset] at g
      exact (Nat.lt_irrefl _ g).elim
    · assumption
    · rw [←Nat.mem_toLazyFinset, h, Nat.mem_toLazyFinset] at g
      exact (Nat.lt_irrefl _ g).elim

open scoped LazyFinset in
def Nat.mem_iff_lt (n: ℕ) : ∀{x}, x ∈ n ↔ x < n := by
  apply Nat.mem_toLazyFinset
