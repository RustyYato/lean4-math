import Math.Data.Multiset.Basic
import Math.Logic.Equiv.Defs

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

instance : Inhabited (Finset α) := ⟨∅⟩

def not_mem_empty (x: α) : x ∉ (∅: Finset α) := by
  intro h
  contradiction

instance : Singleton α (Finset α) where
  singleton x := {
    val := {x}
    property := List.Pairwise.cons (fun _ => (nomatch ·)) List.Pairwise.nil
  }

def mem_singleton {a: α} : ∀{x}, x ∈ ({a}: Finset α) ↔ x = a := by
  intro x
  apply Iff.intro
  intro h
  cases h
  rfl; contradiction
  rintro rfl
  apply List.Mem.head

instance : Insert α (Finset α) where
  insert x as := {x} ∪ as

def erase (a: α) (s: Finset α) : Finset α where
  val := s.val.erase a
  property := by
    cases s with | mk s h =>
    induction s using Quotient.ind
    apply List.Nodup.erase
    assumption

def mem_erase {a: α} {s: Finset α} : ∀{x}, x ∈ s.erase a ↔ x ∈ s ∧ x ≠ a := by
  intro x
  apply Iff.intro
  intro h
  have := Multiset.of_mem_erase _ _ _ h
  apply And.intro
  assumption
  clear this
  · cases s with | mk s g =>
    unfold erase at h
    replace h : x ∈ Multiset.erase _ _ := h
    induction s with
      | nil =>
        rw [Multiset.erase_nil] at h
        contradiction
      | cons a₀ as ih =>
        rw [Multiset.erase_cons] at h
        split at h
        subst a₀
        rintro rfl
        have := g.head
        contradiction
        simp at h
        cases h
        subst x
        symm; assumption
        apply ih
        dsimp
        assumption
        exact g.tail
  · intro ⟨mem, ne⟩
    cases s with | mk s h =>
    show x ∈ Multiset.erase _ _
    replace mem : x ∈ s := mem
    induction s with
    | nil => contradiction
    | cons a₀ as ih =>
      rw [Multiset.erase_cons]
      simp at mem
      split
      subst a₀
      cases mem
      subst x
      contradiction
      assumption
      simp
      cases mem
      left; assumption
      right
      apply ih
      exact h.tail
      assumption

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

def map_emb (f: α ↪ β) (as: Finset α) : Finset β where
  val := as.val.map f
  property := by
    cases as with | mk as ih =>
    cases as using Quotient.ind
    apply List.nodup_map
    exact f.inj
    assumption

def mem_map_emb {f: α ↪ β} {as: Finset α} : ∀{x}, x ∈ as.map_emb f ↔ ∃a, a ∈ as ∧ f a = x := by
  intro x
  unfold map_emb
  show x ∈ Multiset.map _ _ ↔ _
  rw [Multiset.mem_map]
  rfl

def map_emb_inj (f: α ↪ β) : Function.Injective (map_emb f) := by
  intro x y eq
  ext i
  apply Iff.intro
  intro h
  have : f i ∈ y.map_emb f := by
    rw [←eq, mem_map_emb]
    exists i
  rw [mem_map_emb] at this
  obtain ⟨j, j_in_y, eq⟩ := this
  cases f.inj eq
  assumption
  intro h
  have : f i ∈ x.map_emb f := by
    rw [eq, mem_map_emb]
    exists i
  rw [mem_map_emb] at this
  obtain ⟨j, j_in_y, eq⟩ := this
  cases f.inj eq
  assumption

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

def zip (as: Finset α) (bs: Finset β) : Finset (α × β) where
  val := as.val.flatMap fun a => bs.val.map fun b => (a, b)
  property := by
    cases as with | mk as ha =>
    cases bs with | mk bs hb =>
    induction as generalizing bs  with
    | nil => apply List.Pairwise.nil
    | cons a as ih =>
      rw [Multiset.flatMap_cons]
      apply Multiset.nodup_append
      apply Multiset.nodup_map
      assumption
      intro x y eq
      cases eq; rfl
      apply ih
      exact ha.tail
      intro (a₀, y)
      dsimp
      simp [Multiset.mem_map, Multiset.mem_flatMap]
      rintro _ rfl h
      have := ha.head
      contradiction

def mem_mk (as: Multiset α) (h: as.Nodup) : ∀{x: α},
  (Membership.mem (γ := Finset α) ({val := as, property := h}: Finset α) x) ↔ x ∈ as := Iff.rfl

def mem_zip (as: Finset α) (bs: Finset β) : ∀{x}, x ∈ zip as bs ↔ x.1 ∈ as ∧ x.2 ∈ bs := by
  intro x
  simp [zip, Multiset.mem_flatMap, Multiset.mem_map, mem_mk]
  apply Iff.intro
  rintro ⟨a, _, b, _, rfl⟩
  trivial
  intro ⟨_, _⟩
  refine ⟨x.fst, ?_, x.snd, ?_, rfl⟩
  assumption
  assumption

end Finset
