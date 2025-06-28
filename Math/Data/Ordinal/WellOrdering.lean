import Math.Order.Zorn

namespace WellOrdering

variable {α: Type*}

-- an initial seg rel is a relation which is ordered by normal relation implication
-- and is also required to be an initial segment of the larger relation
-- this second condition is needed to ensure that the chains of relations all
-- extensions of a single ordering, and don't allow inserting new elements into the
-- ordering before any already related element
private def init_seg_rel (α: Type*) := α -> α -> Prop

namespace init_seg_rel

-- does the relation define *some* relation for this object
private def defines (r: init_seg_rel α) (x: α) := (∃x', r x' x ∨ r x x')

@[ext]
private def ext (a b: init_seg_rel α) : (∀x y, a x y ↔ b x y) -> a = b := by
  simp [init_seg_rel] at *
  intro h
  ext
  apply h

-- insert a new element into the top of the relation
private def insert (R: init_seg_rel α) (a: α) : init_seg_rel α := fun x y => R.defines x ∧ y = a ∨ R x y

-- merge all relations in the set, if any relation relates two items, then they are related
-- in a chain, this the maximum element of the chain, since all smaller elements are
-- initial segments of the maximum element
private instance : SupSet (init_seg_rel α) where
  sSup S x y := ∃r ∈ S, r x y

private instance : LE (init_seg_rel α) where
  le a b := (∀{x y}, a x y -> b x y) ∧ ∀{x y}, a.defines y -> b x y -> a x y

private instance : LT (init_seg_rel α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

private def defines_of_le {r s: init_seg_rel α} : r ≤ s -> ∀{x}, r.defines x -> s.defines x := by
  intro le x ⟨x', h⟩
  exists x'
  rcases h with h | h
  left; apply le.left; assumption
  right; apply le.left; assumption

private instance : IsPartialOrder (init_seg_rel α) where
  lt_iff_le_and_not_le := Iff.rfl
  le_refl a := ⟨id, fun _ => id⟩
  le_antisymm := by
    intro a b ab ba
    ext x y
    apply Iff.intro
    apply ab.left
    apply ba.left
  le_trans := by
    intro a b c hab hbc
    apply And.intro
    intro x y h
    apply hbc.left
    apply hab.left
    assumption
    intro x y h r
    have g : b.defines y := defines_of_le hab h
    exact hab.right h (hbc.right g r)

end init_seg_rel

-- a locally well ordered relation is a well founded transitive relation
-- where the set of all defined objects is a chain
-- this is useful since the maximal elements of a locally well ordered relation
-- are precisely the well ordered relations (this is proven in `exists_wo`)
-- we only need to weaken the total ordering condition, since that is a global condition
-- but transitivity and well foundedness are both local conditions
private class IsLocallyWellOrdered (R: init_seg_rel α): Prop extends Relation.IsWellFounded R, Relation.IsTrans R where
  rel_defined_is_chain: (Set.mk R.defines).IsChain R

private def rel_insert_locally_wo {R: init_seg_rel α} [IsLocallyWellOrdered R] (ha: ¬R.defines A) : IsLocallyWellOrdered (init_seg_rel.insert R A) where
  trans := by
    intro a b c hab hbc
    rcases hab with ⟨h, rfl⟩ | h
    <;> rcases hbc with ⟨g, rfl⟩ | g
    right
    contradiction
    exfalso; apply ha
    exists c; right; assumption
    left; apply And.intro _ rfl
    exists b; right; assumption
    right; exact trans h g
  rel_defined_is_chain := {
    connected_by := by
      have : ∀a b: α, R.defines a -> R.defines b ->
        init_seg_rel.insert R A a b ∨ a = b ∨ init_seg_rel.insert R A b a := by
        intro a b ha hb
        rcases IsLocallyWellOrdered.rel_defined_is_chain.connected_by ⟨_, ha⟩ ⟨_, hb⟩ with h | h | h
        left; right; assumption
        right; left; cases h; rfl
        right; right; right; assumption
      intro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨a', ha⟩ := ha
      obtain ⟨b', hb⟩ := hb
      simp [Set.Induced]
      rcases ha with (⟨ha, rfl⟩ | ha) | (⟨ha, rfl⟩ | ha)
      <;> rcases hb with (⟨hb, rfl⟩ | hb) | (⟨hb, rfl⟩ | hb)
      any_goals
        right; left; rfl
      any_goals
        left; left
        apply And.intro _ rfl
      any_goals
        right; right; left
        apply And.intro _ rfl
      any_goals apply this
      any_goals assumption
      any_goals exists b'; left; assumption
      any_goals exists b'; right; assumption
      any_goals exists a'; left; assumption
      any_goals exists a'; right; assumption
  }
  wf := by
    have : ∀x: α, R.defines x -> Acc (init_seg_rel.insert R A) x := by
      intro x h
      induction x using Relation.wfInduction R with
      | h x ih =>
      apply Acc.intro
      intro y r
      rcases r with ⟨_, rfl⟩ | r
      contradiction
      apply ih
      assumption
      exists x; right; assumption
    apply WellFounded.intro
    intro x
    apply Acc.intro
    intro y r
    rcases r with ⟨r, rfl⟩ | r
    apply this
    assumption
    apply this
    exists x; right; assumption

private def ssup_locally_wo {S: Set (init_seg_rel α)} (h: ∀R ∈ S, IsLocallyWellOrdered R) (chain: S.IsChain (· ≤ ·)) : IsLocallyWellOrdered (⨆ S) where
  rel_defined_is_chain := {
    connected_by := by
      have mem_conn : ∀s ∈ S, ∀a b: α, s.defines a -> s.defines b -> (⨆ S) a b ∨ a = b ∨ (⨆ S) b a := by
        intro s hs a b ⟨a', ha⟩ ⟨b', hb⟩
        have := h s hs
        have adef : s.defines a := by exists a'
        have bdef : s.defines b := by exists b'
        rcases (IsLocallyWellOrdered.rel_defined_is_chain (R := s)).connected_by
          ⟨a, adef⟩ ⟨b, bdef⟩ with h | h | h
        left; exists s
        right; left; cases h; rfl
        right; right; exists s
      intro ⟨a, ⟨a', ha⟩⟩ ⟨b, ⟨b', hb⟩⟩
      have : Relation.IsTotal (Set.Induced (· ≤ ·) S) := inferInstance
      simp [Set.Induced]
      rcases ha with ⟨r, hr, ha⟩ | ⟨r, hr, ha⟩ <;>
      rcases hb with ⟨s, hs, hb⟩ | ⟨s, hs, hb⟩ <;>
      rcases this.total ⟨r, hr⟩ ⟨s, hs⟩ with h | h
      all_goals simp [Set.Induced] at h
      any_goals
        rename r ≤ s => h
        apply mem_conn _ hs
      any_goals
        rename s ≤ r => h
        apply mem_conn _ hr
      any_goals exists a'; left; assumption
      any_goals exists a'; right; assumption
      any_goals exists b'; left; assumption
      any_goals exists b'; right; assumption
      any_goals apply init_seg_rel.defines_of_le h
      any_goals exists a'; left; assumption
      any_goals exists a'; right; assumption
      any_goals exists b'; left; assumption
      any_goals exists b'; right; assumption
  }
  trans := by
    have : Relation.IsTotal (Set.Induced (· ≤ ·) S) := inferInstance
    intro a b c ⟨r, hr, rab⟩ ⟨s, hs, sbc⟩
    have _ := h s hs
    have _ := h r hr
    rcases this.total ⟨r, hr⟩ ⟨s, hs⟩ with h | h
    exists s
    apply And.intro hs
    exact Relation.trans' (h.left rab) sbc
    exists r
    apply And.intro hr
    exact Relation.trans' rab (h.left sbc)
  wf := by
    have total := (inferInstanceAs (Relation.IsTotal (S.Induced (· ≤ ·)))).total
    apply WellFounded.intro
    intro a
    by_cases h:(⨆ S).defines a
    · rcases h with ⟨a', h⟩
      rename_i h
      rcases h with ⟨s, hs, ha⟩ | ⟨s, hs, ha⟩
      · have := h s hs
        replace ha : s.defines a := ⟨a', .inl ha⟩
        clear a'
        induction a using Relation.wfInduction s with
        | h a ih =>
        apply Acc.intro
        intro x ⟨r, hr, hx⟩
        apply ih
        rcases total ⟨_, hr⟩ ⟨_, hs⟩  with h | h
        apply h.left
        assumption
        exact h.right ha hx
        rcases total ⟨_, hr⟩ ⟨_, hs⟩  with h | h
        apply init_seg_rel.defines_of_le
        assumption
        exists a; right; assumption
        exists a
        right; exact h.right ha hx
      · have := h s hs
        replace ha : s.defines a := ⟨a', .inr ha⟩
        clear a'
        induction a using Relation.wfInduction s with
        | h a ih =>
        apply Acc.intro
        intro x ⟨r, hr, hx⟩
        apply ih
        rcases total ⟨_, hr⟩ ⟨_, hs⟩  with h | h
        apply h.left
        assumption
        exact h.right ha hx
        rcases total ⟨_, hr⟩ ⟨_, hs⟩  with h | h
        apply init_seg_rel.defines_of_le
        assumption
        exists a; right; assumption
        exists a
        right; exact h.right ha hx
    · apply Acc.intro
      intro y g
      exfalso; apply h
      exists y
      left; assumption

-- we use Zorn's lemma to build up an well ordering by showing that any maximal local well ordering
-- must define the entire set, and that the upper bound of any chain of local well orderings
-- is the maximum element of the chain (as defined by `SupSet`)
def exists_wo (α: Type*) : ∃r: α -> α -> Prop, Relation.IsWellOrder r := by
  rcases subsingleton_or_nontrivial α with h | h
  · exists (fun _ _ => False)
    exact {
      trans := by
        intro a b c h
        contradiction
      wf := by
        apply WellFounded.intro
        intro a
        apply Acc.intro
        intro _ _; contradiction
      connected_by := by
        intro a b
        right; left
        apply Subsingleton.allEq
    }
  have ⟨R, hR, spec⟩ := Zorn.partialorder_in (α := init_seg_rel α) (Set.mk IsLocallyWellOrdered) ?_
  have : IsLocallyWellOrdered R := hR
  have defined_nonempty : (Set.mk R.defines).Nonempty := by
    apply Classical.byContradiction
    intro g
    simp at g
    have ⟨a, b, ne⟩ := h
    have := spec (fun x y => a = x ∧ b = y) {
      trans := by
        intro x y z ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
        trivial
      wf := by
        apply WellFounded.intro
        intro x
        apply Acc.intro
        rintro _ ⟨rfl, rfl⟩
        apply Acc.intro
        rintro _ ⟨rfl, rfl⟩
        contradiction
      rel_defined_is_chain := {
        connected_by := by
          intro ⟨x, hx⟩ ⟨y, hy⟩
          simp [Set.Induced]
          rcases hx with ⟨x', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
          <;> rcases hy with ⟨y', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
          right; left; rfl
          right; right; trivial
          left; trivial
          right; left; rfl
      }
    }
    replace this := this ⟨
      fun r => by
      rename_i x y
      have : x ∈ Set.mk R.defines := ⟨y, .inr r⟩
      rw [g] at this
      contradiction, by
      intro x y ydef ⟨rfl, rfl⟩
      replace ydef : b ∈ Set.mk R.defines := ydef
      rw [g] at ydef; contradiction
    ⟩
    have nrab : ¬R a b := by
      intro r
      have : a ∈ Set.mk R.defines := ⟨b, .inr r⟩
      rw [g] at this
      contradiction
    rw [←this] at nrab
    apply nrab
    trivial
  suffices Set.mk R.defines = ⊤ by
    refine ⟨R, { trans := hR.trans, wf := hR.wf, connected_by := ?_ }⟩
    intro a b
    have chain := hR.rel_defined_is_chain
    rw [this] at chain
    rcases chain.connected_by ⟨a, True.intro⟩ ⟨b, True.intro⟩ with h | h | h
    left; exact h
    cases h; right; left; rfl
    right; right; exact h
  · apply Set.ext_univ
    intro a
    apply Classical.byContradiction
    intro ha
    -- since a isn't in defined in R, we can just insert it as the greatest element
    -- which is still a locally well ordered relation
    have := spec (init_seg_rel.insert R a) (rel_insert_locally_wo ha)
    have R_eq_R' := this ⟨fun x => .inr x, by
      intro x y hy r
      rcases r with ⟨r, rfl⟩ | r
      contradiction
      assumption⟩
    have : (init_seg_rel.insert R a).defines a := by
      obtain ⟨x, hx⟩ := defined_nonempty
      exists x
      left; left; apply And.intro _ rfl
      assumption
    rw [R_eq_R'] at this
    contradiction
  · intro S mem_S_wo Schain
    refine ⟨sSup S, ?_, ?_⟩
    · apply ssup_locally_wo
      assumption
      assumption
    · intro R hR
      apply And.intro
      intro x y r
      exists R
      intro x y df ⟨R', hR', r⟩
      have := inferInstanceAs (Relation.IsTotal (S.Induced (· ≤ ·)))
      rcases this.total ⟨R, hR⟩ ⟨R', hR'⟩ with h | h
      exact h.right df r
      apply h.left
      assumption

def order (α: Type*): α -> α -> Prop := Classical.choose (exists_wo α)
instance : Relation.IsWellOrder (order α) := Classical.choose_spec (exists_wo α)

end WellOrdering
