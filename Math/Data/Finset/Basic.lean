import Math.Data.Multiset.Basic

def Finset (α: Type*) := { x: Multiset α // x.Nodup }

namespace Finset

instance : Membership α (Finset α) where
  mem s x := x ∈ s.val

instance : HasSubset (Finset α) where
  Subset a b := ∀x ∈ a, x ∈ b

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
def sdiff (a b: Finset α) : Finset α where
  val := a.val.filter (· ∉ b)
  property := Multiset.nodup_filter _ _ a.property
def filter (f: α -> Bool) (a: Finset α) : Finset α where
  val := a.val.filter f
  property := Multiset.nodup_filter _ _ a.property

instance : Union (Finset α) where
  union := union
instance : Inter (Finset α) where
  inter := inter
instance : SDiff (Finset α) where
  sdiff := sdiff

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

def mem_sdiff {a b: Finset α} : ∀{x: α}, x ∈ a \ b ↔ x ∈ a ∧ x ∉ b := by
  intro x
  show x ∈ (a.val.filter _) ↔ x ∈ a ∧ x ∉ b
  rw [Multiset.mem_filter, decide_eq_true_iff]
  rfl

def mem_filter {f: α -> Bool} {a: Finset α} : ∀{x: α}, x ∈ a.filter f ↔ x ∈ a ∧ f x := by
  intro x
  show x ∈ (a.val.filter _) ↔ _
  rw [Multiset.mem_filter]
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

def card (a: Finset α) : Nat := a.val.length

def card_le_of_sub {a b: Finset α} : a ⊆ b -> a.card ≤ b.card := by
  intro sub
  cases a with | mk a ha =>
  cases b with | mk b hb =>
  cases a with | mk a =>
  cases b with | mk b =>
  obtain sub: a ⊆ b := sub
  obtain ha: a.Nodup := ha
  obtain hb: b.Nodup := hb
  show a.length ≤ b.length
  clear hb
  induction a generalizing b with
  | nil => apply Nat.zero_le
  | cons a as ih =>
    have ⟨bs', perm⟩ := (List.mem_iff_exists_perm_cons _ _).mp (sub (List.Mem.head _))
    rw [perm.length_eq]
    apply Nat.succ_le_succ
    apply ih
    exact ha.tail
    intro x mem
    cases perm.mem_iff.mp (sub (List.Mem.tail _ mem))
    have := ha.head _ mem
    contradiction
    assumption

def eq_of_sub_of_card_eq {a b: Finset α} : a ⊆ b -> a.card = b.card -> a = b := by
  intro sub eq
  cases a with | mk a ha =>
  cases b with | mk b hb =>
  cases a with | mk a =>
  cases b with | mk b =>
  obtain sub: a ⊆ b := sub
  obtain ha: a.Nodup := ha
  obtain hb: b.Nodup := hb
  congr 1; apply Quotient.sound
  induction ha generalizing b with
  | nil =>
    cases b
    apply List.Perm.nil
    contradiction
  | cons ha has ih =>
    rename_i a as
    have ⟨bs', perm⟩ := (List.mem_iff_exists_perm_cons _ _).mp (sub (List.Mem.head _))
    apply List.Perm.trans _ perm.symm
    apply List.Perm.cons
    apply ih
    · intro x mem
      cases perm.mem_iff.mp (sub (List.Mem.tail _ mem))
      have := ha _ mem; contradiction
      assumption
    show as.length = bs'.length
    apply Nat.succ.inj
    apply Eq.trans _ perm.length_eq
    assumption
    exact (perm.nodup hb).tail

end Finset
