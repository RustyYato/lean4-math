import Math.Data.Set.Finite
import Math.Order.Directed.Basic

def exists_ge_of_finite_set [Nonempty α] (r: α -> α -> Prop) [Relation.IsTrans r] [IsDirected α r] (S: Set α) (h: S.IsFinite): ∃m, ∀x ∈ S, r x m := by
  apply Set.IsFinite.induction S
  case nil =>
    rename_i ne _ _; obtain ⟨a⟩ := ne
    exists a
    exact nofun
  case cons =>
    intro a as ha as_finite ih
    have ⟨b, b_spec⟩ := ih
    have ⟨m, m_spec⟩ := isDirected r a b
    exists m
    intro x hx
    simp at hx; rcases hx with  rfl | hx
    exact m_spec.left
    apply Relation.trans' _ m_spec.right
    apply b_spec
    assumption
