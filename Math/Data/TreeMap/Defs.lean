import Math.Data.Setoid.Basic
import Math.Order.Defs

inductive TreeMap.Pre (K V: Type*) [LE K] [@Relation.IsLinearOrder K (· ≤ ·) (· = ·)] where
| leaf
| node (left: Pre K V) (key: K) (value: V) (right: Pre K V)

variable {K V: Type*} [LE K] [@Relation.IsLinearOrder K (· ≤ ·) (· = ·)]

instance : LT K where
  lt := Relation.strict (· ≤ ·)

instance : IsLawfulLT K where
instance : IsLinearOrder K := inferInstance
instance [DecidableLE K] : DecidableLT K := fun a b => inferInstanceAs (Decidable (a ≤ b ∧ ¬b ≤ a))

namespace TreeMap.Pre

def get [DecidableLE K] [DecidableEq K] (key: K) : TreeMap.Pre K V -> Option V
| .leaf => .none
| .node l k v r =>
  if key = k then
    v
  else if key ≤ k then
    l.get key
  else
    r.get key

inductive ContainsVal (key: K) (val: V) : TreeMap.Pre K V -> Prop where
| node : ContainsVal key val (.node l key val r)
| left : ContainsVal key val l -> ContainsVal key val (.node l k v r)
| right : ContainsVal key val r -> ContainsVal key val (.node l k v r)

inductive ContainsKey (key: K) : TreeMap.Pre K V -> Prop where
| node {l v r} : ContainsKey key (.node l key v r)
| left {l k v r} : ContainsKey key l -> ContainsKey key (.node l k v r)
| right {l k v r} : ContainsKey key r -> ContainsKey key (.node l k v r)

instance : Membership K (TreeMap.Pre K V) where
  mem t := t.ContainsKey

inductive IsWellFormed : TreeMap.Pre K V -> Prop where
| leaf : IsWellFormed .leaf
| node {l k v r} :
  (∀key ∈ l, key < k) -> (∀key ∈ r, k < key) ->
  IsWellFormed l ->
  IsWellFormed r ->
  IsWellFormed (.node l k v r)

instance : Setoid (TreeMap.Pre K V) where
  r a b := ∀k v, a.ContainsVal k v ↔ b.ContainsVal k v
  iseqv := {
    refl _ _ _ := Iff.rfl
    symm h k v := (h k v).symm
    trans h g k v := (h k v).trans (g k v)
  }

def mem_of_contains_val {t: TreeMap.Pre K V} {key: K} {val: V} : t.ContainsVal key val -> key ∈ t := by
  intro h
  induction h with
  | node => apply ContainsKey.node
  | left => apply ContainsKey.left; assumption
  | right => apply ContainsKey.right; assumption

def contains_val_of_mem {t: TreeMap.Pre K V} {key: K} : key ∈ t -> ∃val, t.ContainsVal key val := by
  intro h
  induction h with
  | @node l v r =>
    exists v
    apply ContainsVal.node
  | left _ ih  =>
    obtain ⟨v, ih⟩ := ih
    exists v
    apply ContainsVal.left; assumption
  | right _ ih  =>
    obtain ⟨v, ih⟩ := ih
    exists v
    apply ContainsVal.right; assumption

def get_eq_iff_contains_val [DecidableLE K] [DecidableEq K] {t: TreeMap.Pre K V} (ht: t.IsWellFormed) {key: K} {val: V} : t.get key = .some val ↔ t.ContainsVal key val := by
  induction ht with
  | leaf => exact Iff.intro nofun nofun
  | @node l k v r hl hr wfl wfr ihl ihr =>
    unfold get
    split <;> rename_i h
    · subst k
      apply Iff.intro
      rintro h; cases h
      apply ContainsVal.node
      intro h; cases h <;> rename_i h
      rfl
      have := lt_irrefl (hl _ (mem_of_contains_val h))
      contradiction
      have := lt_irrefl (hr _ (mem_of_contains_val h))
      contradiction
    split
    · apply Iff.trans ihl
      apply Iff.intro
      apply ContainsVal.left
      intro g
      cases g <;> rename_i g
      contradiction
      assumption
      have := not_le.mpr (hr _ (mem_of_contains_val g))
      contradiction
    · apply Iff.trans ihr
      apply Iff.intro
      apply ContainsVal.right
      intro g
      cases g <;> rename_i g
      contradiction
      have := le_of_lt (hl _ (mem_of_contains_val g))
      contradiction
      assumption

def get_issome_iff_mem [DecidableLE K] [DecidableEq K] {t: TreeMap.Pre K V} (ht: t.IsWellFormed) {key: K} : (t.get key).isSome ↔ key ∈ t := by
  induction ht with
  | leaf => exact Iff.intro nofun nofun
  | @node l k v r hl hr wfl wfr ihl ihr =>
    unfold get
    split <;> rename_i h
    · subst k
      apply Iff.intro
      rintro h; cases h
      apply ContainsKey.node
      intro h; cases h <;> rename_i h
      rfl
      have := lt_irrefl (hl _ h)
      contradiction
      have := lt_irrefl (hr _ h)
      contradiction
    split
    · apply Iff.trans ihl
      apply Iff.intro
      apply ContainsKey.left
      intro g
      cases g <;> rename_i g
      contradiction
      assumption
      have := not_le.mpr (hr _ g)
      contradiction
    · apply Iff.trans ihr
      apply Iff.intro
      apply ContainsKey.right
      intro g
      cases g <;> rename_i g
      contradiction
      have := le_of_lt (hl _ g)
      contradiction
      assumption

def insert [DecidableLE K] [DecidableEq K] (key: K) (val: V) : TreeMap.Pre K V -> TreeMap.Pre K V
| .leaf => .node .leaf key val .leaf
| .node l k v r =>
  if key = k then
    .node l k val r
  else if key ≤ k then
    .node (l.insert key val) k v r
  else
    .node l k v (r.insert key val)

end TreeMap.Pre

def TreeMap.Repr (K V: Type*) [LE K] [@Relation.IsLinearOrder K (· ≤ ·) (· = ·)] := { t: TreeMap.Pre K V // t.IsWellFormed }

instance : Setoid (TreeMap.Repr K V) := Setoid.subtypeSetoid _

def TreeMap (K V: Type*) [LE K] [@Relation.IsLinearOrder K (· ≤ ·) (· = ·)] := @Quotient (TreeMap.Repr K V) inferInstance

namespace TreeMap

variable [DecidableLE K] [DecidableEq K]

def get (key: K) : TreeMap K V -> Option V := by
  refine Quotient.lift ?_ ?_
  · intro r
    exact r.val.get key
  · intro a b h
    cases hb:b.val.get key
    have key_notin_b := Classical.not_iff_not.mp (Pre.get_issome_iff_mem b.property (key := key)) |>.mp (by rw [hb]; nofun)
    apply Classical.byContradiction
    intro g
    have key_in_a := Classical.not_not.mp <| (Classical.not_iff_not.mp Option.not_isSome_iff_eq_none).mpr g
    rw [Pre.get_issome_iff_mem] at key_in_a
    have ⟨v, ha⟩ := Pre.contains_val_of_mem key_in_a
    exact key_notin_b (Pre.mem_of_contains_val ((h _ _).mp ha))
    exact a.property
    rw [Pre.get_eq_iff_contains_val] at *
    apply (h _ _).mpr
    assumption
    exact b.property
    exact a.property

def insert (key: K) (val: V) : TreeMap K V -> TreeMap K V := by
  refine Quotient.lift ?_ ?_
  · intro r
    refine Quotient.mk _ ⟨?_, ?_⟩
    · exact r.val.insert key val
    · sorry
  · intro a b h
    apply Quotient.sound
    intro k v
    dsimp
    sorry

end TreeMap
