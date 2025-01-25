import Math.Data.Zf.Basic
import Math.Order.Linear
import Math.Order.OrderIso
import Math.Relation.RelIso

open ZfSet

structure ZfSet.IsOrdinal (set: ZfSet): Prop where
  trans: ∀{x}, x ∈ set -> x ⊆ set
  total: ∀{x y}, x ∈ set -> y ∈ set -> x ∈ y ∨ x = y ∨ y ∈ x

@[pp_with_univ]
structure Ordinal where
  ofZfSet ::
  set: ZfSet
  trans: ∀{x}, x ∈ set -> x ⊆ set
  total: ∀{x y}, x ∈ set -> y ∈ set -> x ∈ y ∨ x = y ∨ y ∈ x

namespace Ordinal

abbrev mk (h: ZfSet.IsOrdinal s): Ordinal where
  set := s
  trans := h.trans
  total := h.total

def toIsOrdinal (o: Ordinal): IsOrdinal o.set where
  trans := o.trans
  total := o.total

instance : LE Ordinal where
  le a b := a.set ⊆ b.set

instance : LT Ordinal where
  lt a b := a.set ∈ b.set

def embedZfSet : @RelEmbedding Ordinal ZfSet (· < ·) (· ∈ ·) where
  toFun x := x.set
  inj := by
    intro x y eq; cases x; cases y; congr
  resp_rel := Iff.rfl

attribute [coe] Ordinal.set

instance : Coe Ordinal ZfSet where
  coe := Ordinal.set

instance : @Relation.IsWellFounded Ordinal (· < ·) :=
  embedZfSet.toRelHom.wf

def succ (o: Ordinal) : Ordinal where
  set := insert o.set o.set
  trans := by
    intro x mem
    rw [mem_insert] at mem
    cases mem
    subst x
    intro x mem
    rw [mem_insert]
    right; assumption
    intro y mem
    rw [mem_insert]; right
    apply o.trans
    assumption
    assumption
  total := by
    intro x y hx hy
    rw [mem_insert] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    subst x; subst y
    right; left; rfl
    subst x; right; right; assumption
    subst y; left; assumption
    rcases o.total hx hy with xy | eq | yx
    left; assumption
    right; left; assumption
    right; right; assumption

def lt_succ_self (o: Ordinal) : o < o.succ := mem_insert.mpr (.inl rfl)

def min' (a b: Ordinal) : Ordinal where
  set := a.set ∩ b.set
  trans := by
    intro x h y yx
    rw [mem_inter] at *
    exact ⟨a.trans h.left _ yx, b.trans h.right _ yx⟩
  total := by
    intro x y hx hy
    rw [mem_inter] at hx hy
    apply a.total
    exact hx.left
    exact hy.left

instance : Min Ordinal := ⟨min'⟩

def min_le_left' (a b: Ordinal) : min a b ≤ a := by
  intro x mem
  exact (mem_inter.mp mem).left

def min_le_right' (a b: Ordinal) : min a b ≤ b := by
  intro x mem
  exact (mem_inter.mp mem).right

def mem_set {a: ZfSet} (b: Ordinal) (ha: a ∈ b.set) : a.IsOrdinal where
  trans := by
    intro x hxa y hy
    have hx := b.trans ha _ hxa
    have hyb := b.trans hx _ hy
    rcases b.total ha hyb with hay | eq | hyb
    have := Relation.irrefl (rel := Relation.TransGen (· ∈ ·)) (Relation.TransGen.tail (.tail (.single hxa) hay) hy)
    contradiction
    subst y
    have := Relation.asymm (rel := (· ∈ ·)) hxa hy
    contradiction
    assumption
  total := by
    intro x y hx hy
    apply b.total
    all_goals apply b.trans <;> assumption

def lt_of_le_of_not_le' (B A: Ordinal) : B ≤ A -> ¬A ≤ B -> B < A := by
  intro BA AB
  have ⟨x, h⟩ := Classical.not_forall.mp AB
  rw [not_imp] at h
  obtain ⟨hb, ha⟩ := h
  let S := A.set.toSet \ B.set.toSet
  have : S.Nonempty := ⟨_, hb, ha⟩
  clear hb ha x
  let x := Set.min (· ∈ ·) this
  let x_mem: x ∈ S := Set.min_mem (· ∈ ·) this
  obtain ⟨hxa, hnxb⟩ := x_mem
  let x_spec: ∀y ∈ S, ¬y ∈ x := Set.not_lt_min (· ∈ ·) this
  have x_sub_A: x ⊆ A := A.trans hxa
  have : ∅ = (A.set \ B) ∩ x -> x ⊆ B := by
    intro h
    have : toSet ∅ = toSet ((A.set \ B) ∩ x) := by rw [h]
    rw [
      toSet_inter,
      toSet_sdiff,
      Set.sdiff_eq_inter_compl, Set.inter_assoc, Set.inter_comm _ x.toSet,
      ←Set.inter_assoc,
      ←Set.sdiff_eq_inter_compl, Set.inter_of_sub_right,
      ←toSet_sdiff] at this
    replace this := toSet_inj this
    intro z hzx
    apply Classical.byContradiction
    intro hzb
    have hz : z ∈ x \ B := by
      rw [mem_sdiff]
      trivial
    rw [←this] at hz
    exact not_mem_empty _ hz
    assumption
  replace x_sub_B := this <| by
    ext z
    apply Iff.intro
    intro h; exact (not_mem_empty _ h).elim
    intro h
    rw [mem_inter, mem_sdiff] at h
    have := x_spec z ⟨h.left.left, h.left.right⟩ h.right
    contradiction
  have B_sub_x : B.set ⊆ x := by
    intro z hz
    have hza := BA _ hz
    rcases A.total hxa hza with hzx | eq | hxz
    have := B.trans hz _ hzx
    contradiction
    subst z
    contradiction
    assumption
  have := sub_antisym x_sub_B B_sub_x
  show B.set ∈ A.set
  rw [←this]
  assumption

instance : IsPartialOrder Ordinal where
  le_refl _ := ZfSet.sub_refl _
  le_trans := ZfSet.sub_trans
  le_antisymm := by
    intro a b ab ba
    apply embedZfSet.inj
    apply ZfSet.sub_antisym
    assumption
    assumption
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.intro
    intro h
    apply And.intro
    apply b.trans
    assumption
    intro g
    have := embedZfSet.inj <| ZfSet.sub_antisym (b.trans h) g
    rw [←this] at h
    exact Relation.IsIrrefl.irrefl h
    intro ⟨h, g⟩
    apply lt_of_le_of_not_le' <;> assumption

def le_total' (a b: Ordinal) : a ≤ b ∨ b ≤ a := by
  apply Classical.byContradiction
  rw [not_or]
  intro ⟨hab, hba⟩
  have ha : min a b ≤ a := min_le_left' a b
  have hb : min a b ≤ b := min_le_right' a b
  have min_lt_a  : min a b < a := lt_of_le_of_ne ha <| by
    intro h
    rw [h] at hb; contradiction
  have min_lt_b  : min a b < b := lt_of_le_of_ne hb <| by
    intro h
    rw [h] at ha; contradiction
  exact Relation.irrefl (rel := (· ∈ ·)) (mem_inter.mpr ⟨min_lt_a, min_lt_b⟩)

instance : IsLinearOrder Ordinal where
  le_antisymm := le_antisymm
  le_trans := le_trans
  lt_or_le := by
    intro a b
    rcases le_total' a b with h | h
    rcases lt_or_eq_of_le h with h | h
    left; assumption
    right; rw [h]
    right; assumption

def total' {a b: ZfSet} (ha: a.IsOrdinal) (hb: b.IsOrdinal) :
  a ∈ b ∨ a = b ∨ b ∈ a := by
  rcases lt_trichotomy (Ordinal.mk ha) (Ordinal.mk hb) with lt | eq | gt
  left; assumption
  right; left; apply Ordinal.ofZfSet.inj eq
  right; right; assumption

def max' (a b: Ordinal) : Ordinal where
  set := a.set ∪ b.set
  trans := by
    intro x h y yx
    rw [mem_union] at *
    cases h
    left
    apply a.trans
    assumption
    assumption
    right
    apply b.trans
    assumption
    assumption
  total := by
    intro x y hx hy
    rw [mem_union] at hx hy
    apply total'
    rcases hx with hx | hx
    apply a.mem_set
    assumption
    apply b.mem_set
    assumption
    rcases hy with hy | hy
    apply a.mem_set
    assumption
    apply b.mem_set
    assumption

instance : Max Ordinal := ⟨max'⟩

instance : IsLinearMinMaxOrder Ordinal where
  min_iff_le_left := by
    intro a b
    apply Iff.intro
    intro h
    apply embedZfSet.inj
    show a.set ∩ b.set = a.set
    apply toSet_inj
    rw [toSet_inter, Set.inter_of_sub_left]
    assumption
    intro h
    rw [←h]
    apply inter_sub_right
  min_iff_le_right := by
    intro a b
    apply Iff.intro
    intro h
    apply embedZfSet.inj
    show a.set ∩ b.set = b.set
    apply toSet_inj
    rw [toSet_inter, Set.inter_of_sub_right]
    assumption
    intro h
    rw [←h]
    apply inter_sub_left
  max_iff_le_left := by
    intro a b
    apply Iff.intro
    intro h
    apply embedZfSet.inj
    show a.set ∪ b.set = b.set
    apply toSet_inj
    rw [toSet_union, Set.union_of_sub_left]
    assumption
    intro h
    rw [←h]
    apply left_sub_union
  max_iff_le_right := by
    intro a b
    apply Iff.intro
    intro h
    apply embedZfSet.inj
    show a.set ∪ b.set = a.set
    apply toSet_inj
    rw [toSet_union, Set.union_of_sub_right]
    assumption
    intro h
    rw [←h]
    apply right_sub_union

end Ordinal
