import Math.Data.Multiset.Basic

def Finset (α: Type*) := { x: Multiset α // x.Nodup }

namespace Finset

instance : Membership α (Finset α) where
  mem s x := x ∈ s.val

instance [DecidableEq α] (as: Finset α) : Decidable (x ∈ as) :=
  inferInstanceAs (Decidable (x ∈ as.val))

@[ext]
def ext : ∀(a b: Finset α), (h: ∀{x: α}, x ∈ a ↔ x ∈ b) -> a = b := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  cases a with | mk a =>
  cases b with | mk b =>
  congr 1
  apply Quotient.sound
  apply List.ext_nodup <;> assumption

variable [DecidableEq α] [DecidableEq β]

def ofMultiset (a: Multiset α) : Finset α where
  val := a.dedup
  property := a.nodup_dedup

def mem_ofMultiset {as: Multiset α} : ∀{x}, x ∈ ofMultiset as ↔ x ∈ as := (Multiset.mem_dedup _ _).symm

def union (a b: Finset α) : Finset α := ofMultiset <| a.val ++ b.val
def inter (a b: Finset α) : Finset α where
  val := a.val.filter (· ∈ b)
  property := Multiset.nodup_filter _ _ a.property

instance : Union (Finset α) where
  union := union
instance : Inter (Finset α) where
  inter := inter

instance : EmptyCollection (Finset α) where
  emptyCollection := {
    val := ∅
    property := List.Pairwise.nil
  }

instance : Singleton α (Finset α) where
  singleton x := {
    val := {x}
    property := List.Pairwise.cons (fun _ => (nomatch ·)) List.Pairwise.nil
  }

instance : Insert α (Finset α) where
  insert x as := {x} ∪ as

def mem_union {a b: Finset α} : ∀{x: α}, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := by
  intro x
  show x ∈ ofMultiset (a.val ++ b.val) ↔ x ∈ a ∨ x ∈ b
  rw [mem_ofMultiset, Multiset.mem_append]
  rfl

def mem_inter {a b: Finset α} : ∀{x: α}, x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := by
  intro x
  show x ∈ (a.val.filter _) ↔ x ∈ a ∧ x ∈ b
  rw [Multiset.mem_filter, decide_eq_true_iff]
  rfl

def map (f: α -> β) (as: Finset α) : Finset β :=
  .ofMultiset <| as.val.map (fun x => f x)

def flatMap (f: α -> Finset β) (as: Finset α) : Finset β :=
  .ofMultiset <| as.val.flatMap (fun x => (f x).val)

def flatten (as: Finset (Finset α)) : Finset α :=
  .ofMultiset <| as.val.flatMap Subtype.val

def mem_map {f: α -> β} {as: Finset α} : ∀{x}, x ∈ as.map f ↔ ∃a, a ∈ as ∧ f a = x := by
  intro x
  unfold map
  rw [mem_ofMultiset, Multiset.mem_map]
  rfl

def mem_flatten {as: Finset (Finset α)} : ∀{x}, x ∈ as.flatten ↔ ∃a, a ∈ as ∧ x ∈ a := by
  intro x
  unfold flatten
  rw [mem_ofMultiset, Multiset.mem_flatMap]
  rfl

def mem_flatMap {f: α -> Finset β} {as: Finset α} : ∀{x}, x ∈ as.flatMap f ↔ ∃a, a ∈ as ∧ x ∈ f a := by
  intro x
  unfold flatMap
  rw [mem_ofMultiset, Multiset.mem_flatMap]
  rfl

end Finset
