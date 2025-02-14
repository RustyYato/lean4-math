import Math.Algebra.Ring
import Math.Algebra.Hom
import Math.Relation.RelIso

namespace Free.Group

-- a list of maybe inverted elemnts
abbrev Pre (α: Type*) := List (α × Bool)

inductive Reduction.Step : Pre α -> Pre α -> Prop where
| red (as bs: Pre α) (x: α) (b: Bool) : Reduction.Step (as ++ (x, b)::(x, !b)::bs) (as ++ bs)

abbrev Reduction : Pre α -> Pre α -> Prop :=
  Relation.ReflTransGen Reduction.Step

def Reduction.Step.iff_exists:
  Reduction.Step as bs ↔ ∃as' x b bs', as = as' ++ [(x, b), (x, !b)] ++ bs' ∧ bs = as' ++ bs' := by
  apply Iff.intro
  intro red
  cases red
  · rename_i as bs x hx
    exists as
    exists x
    exists hx
    exists bs
    simp
  intro ⟨_, _, _, _, ha, hb⟩
  subst ha; subst hb
  rw [List.append_assoc]
  apply Step.red

def Reduction.Step.diamond {as bs cs: Pre α} :
  Reduction.Step as bs -> Reduction.Step as cs ->
  bs = cs ∨ ∃ds, Reduction.Step bs ds ∧ Reduction.Step cs ds := by
  intro ab ac
  cases ab with
  | red as₀ bs₀ a₀ ha₀ =>
  rw [Reduction.Step.iff_exists] at ac
  obtain ⟨as₁, a₁, ha₁, bs₁, eq_left, eq_right⟩ := ac
  subst cs
  simp [List.append_eq_append_iff, List.cons_eq_append_iff] at eq_left
  · rcases eq_left with eq_left | eq_left
    obtain ⟨_, rfl, eq_left⟩ := eq_left
    rcases eq_left with eq_left | eq_left
    · obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := eq_left
      simp
    · obtain ⟨_, ⟨rfl, rfl⟩, eq_left⟩ := eq_left
      rcases eq_left with eq_left | eq_left
      obtain ⟨_, ⟨rfl, rfl⟩, rfl, ⟨_, rfl⟩, rfl, rfl⟩ := eq_left
      rename_i eq_left; subst eq_left
      simp
      obtain ⟨_, ⟨rfl, rfl⟩, rfl, ⟨_, rfl⟩, rfl, rfl⟩ := eq_left
      rename_i as₁
      right
      exists as₀ ++ as₁ ++ bs₁
      apply And.intro
      rw [←List.append_assoc]
      apply Step.red
      rw [List.append_assoc, List.cons_append, List.cons_append, List.append_assoc]
      apply Step.red
    · obtain ⟨_, ⟨rfl, rfl⟩, eq_left⟩ := eq_left
      rcases eq_left with eq_left | eq_left
      · obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := eq_left
        simp
      obtain ⟨_, rfl, eq_left⟩ := eq_left
      rcases eq_left with eq_left | eq_left
      obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := eq_left
      simp
      obtain ⟨_, rfl, rfl⟩ := eq_left
      rename_i bs₁
      right
      exists as₁ ++ bs₁ ++ bs₀
      apply And.intro
      simp only [List.append_assoc, List.cons_append]
      apply Step.red
      simp only [←List.append_assoc, List.cons_append]
      apply Step.red

def Reduction.strongly_normalizing {as bs cs: Pre α} :
  Reduction as bs -> Reduction as cs -> ∃ds: Pre α, Reduction bs ds ∧ Reduction cs ds := by
  intro ab ac
  induction ab generalizing cs with
  | refl => exists cs
  | cons hb ab ih =>
    rename_i as bs' bs
    cases ac with
    | refl =>
      exists bs
      apply And.intro
      rfl
      apply Relation.ReflTransGen.cons
      assumption
      assumption
    | cons hc ac =>
      rename_i cs'
      rcases Reduction.Step.diamond hb hc with rfl | ⟨ds, hbs', hcs'⟩
      exact ih ac
      have ⟨es, bes, des⟩  := ih (Relation.ReflTransGen.single hbs')
      sorry

end Free.Group
