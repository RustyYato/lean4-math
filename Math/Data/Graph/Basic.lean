import Math.Tactics.PPWithUniv
import Math.Order.Partial
import Math.Relation.Basic

@[pp_with_univ]
structure Graph.{u} where
  Node: Type u
  Edge: Node -> Node -> Prop

namespace Graph

instance : CoeSort Graph (Type u) := ⟨Graph.Node⟩
attribute [coe] Graph.Node

section

variable (G: Graph.{u})

inductive Path : G -> G -> Type u where
| refl : Path a a
| edge : G.Edge a b -> Path b c -> Path a c

structure NonemptyPath (a b: G) : Type u where
  mid: G
  first: G.Edge a mid
  path: G.Path mid b

end

variable {G: Graph}

def Path.single (a b: G) : G.Edge a b -> G.Path a b := (.edge · .refl)

instance : Coe (G.NonemptyPath a b) (G.Path a b) where
  coe p := .edge p.first p.path

private def Path.appendAux {a b c: G} (h: G.Path b c) : G.Path a b -> G.Path a c
| .refl => h
| .edge e g => .edge e (h.appendAux g)

def Path.append {a b c: G} (h: G.Path a b) (g: G.Path b c) : G.Path a c :=
  g.appendAux h

instance : HAppend (G.Path a b) (G.Path b c) (G.Path a c) where
  hAppend := Path.append

def Path.append_assoc {a b c d: G} (h: G.Path a b) (g: G.Path b c) (i: G.Path c d) :
  h ++ g ++ i = h ++ (g ++ i) := by
  induction h with
  | refl => rfl
  | edge e h ih =>
    show edge _ (h ++ g ++ i) = _
    rw [ih]
    rfl

-- LE is defined to be "is there a path between two nodes"
instance : LE G where
  le a b := Nonempty (G.Path a b)
-- LT is defined to be "is there a one-way path between two nodes"
-- where the empty path is considered a two-way path
instance : LT G where
  lt a b := a ≤ b ∧ ¬b ≤ a
instance : IsPreOrder G where
  lt_iff_le_and_not_le := Iff.rfl
  le_refl _ := ⟨Path.refl⟩
  le_trans | ⟨h⟩, ⟨g⟩ => ⟨h ++ g⟩

def le_of_edge : Edge G a b -> a ≤ b := fun h => ⟨Path.single _ _ h⟩

def le_iff_refltransgen_edge {a b: G} :
  a ≤ b ↔ Relation.ReflTransGen G.Edge a b := by
  apply Iff.intro
  · intro ⟨h⟩
    induction h with
    | refl => rfl
    | edge e p ih =>
      apply Relation.ReflTransGen.cons
      assumption
      assumption
  · intro h
    induction h with
    | refl => rfl
    | cons e h ih =>
      apply le_trans _ ih
      apply le_of_edge
      assumption

class IsCyclic (G: Graph) : Prop where
  cycle: ∃x: G, Nonempty (G.NonemptyPath x x)

class IsAcyclic (G: Graph) : Prop where
  -- a non-empty path from a node it itself is a cycle
  -- and acyclic graph has no cycles
  no_cycles: ∀x, G.NonemptyPath x x -> False

def IsCyclic.not_acyclic (G: Graph) [h: IsCyclic G] : ¬IsAcyclic G := by
  intro g
  obtain ⟨x, ⟨path⟩⟩ := h
  apply g.no_cycles x
  assumption

def IsAcyclic.not_cyclic (G: Graph) [h: IsAcyclic G] : ¬IsCyclic G := by
  intro g
  apply IsCyclic.not_acyclic G
  assumption

instance [IsAcyclic G] : IsPartialOrder G where
  le_antisymm := by
    intro a b ⟨ha⟩ ⟨hb⟩
    cases ha
    rfl
    rename_i edge ha
    have := IsAcyclic.no_cycles a ⟨_, edge, ha ++ hb⟩
    contradiction

-- two nodes are equivalent if they are in the same Strongly Connected Component
instance : Setoid G := le_setoid G

def condense_edge (a b: G) := ¬a ≈ b ∧ ∃x y: G, a ≈ x ∧ b ≈ y ∧ G.Edge x y

def Condense : Graph where
  Node := Quotient (le_setoid G)
  -- there is an edge between strongly connected components
  -- iff there is are nodes in the SCC which have an edge
  Edge := by
    apply Quotient.lift₂ condense_edge
    suffices ∀a b c d: G, a ≈ c -> b ≈ d -> condense_edge a b -> condense_edge c d by
      intro a b c d ac bd
      ext; apply Iff.intro
      apply this <;> assumption
      apply this <;> (apply Relation.symm; assumption)
    intro a b c d ac bd ⟨ne, x, y, xa, yb, e⟩
    refine ⟨?_, x, y, ?_, ?_, e⟩
    intro cd
    apply ne
    exact trans (trans ac cd) (Relation.symm bd)
    apply Relation.trans' (Relation.symm ac); assumption
    apply Relation.trans' (Relation.symm bd); assumption

def toScc (x: G) : G.Condense := Quotient.mk  _ x

def toScc_eq_iff {a b: G} : toScc a = toScc b ↔ a ≈ b := ⟨Quotient.exact, Quotient.sound⟩

@[cases_eliminator, induction_eliminator]
def condense_ind
  {motive: G.Condense -> Prop}
  (toScc: ∀x, motive (toScc x))
  (node: G.Condense):  motive node := by
  induction node using Quot.ind with | mk node =>
  apply toScc

def lt_of_condense_edge {a b: G} : Edge _ (toScc a) (toScc b) -> a < b := by
  intro ⟨ne, a', b', a_eqv_a', b_eqv_b', edge⟩
  suffices a ≤ b by
    apply And.intro
    assumption
    intro h
    apply ne
    apply And.intro <;> assumption
  apply le_trans a_eqv_a'.left
  apply le_trans _ b_eqv_b'.right
  apply le_of_edge
  assumption

def le_iff_condense_le {a b: G} : toScc a ≤ toScc b ↔ a ≤ b := by
  apply Iff.intro
  · generalize ha':toScc a = a'
    generalize hb':toScc b = b'
    intro ⟨path⟩
    induction path generalizing a b with
    | refl =>
      subst hb'
      exact (toScc_eq_iff.mp ha').left
    | edge e p ih =>
      rename_i a' b' c'
      induction b' with
      | toScc b' =>
      subst a'; subst c'
      apply flip le_trans
      apply ih
      rfl
      rfl
      exact le_of_lt (lt_of_condense_edge e)
  · intro ⟨path⟩
    induction path with
    | refl => rfl
    | edge e p ih =>
      apply le_trans _ ih; clear ih
      rename_i a b c
      by_cases h:b ≤ a
      apply le_of_eq
      apply toScc_eq_iff.mpr
      apply And.intro
      apply le_of_edge
      assumption
      assumption
      apply le_of_edge
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      intro g
      exact h g.right
      exact a
      exact b
      rfl
      rfl
      assumption

def lt_iff_condense_lt {a b: G} : toScc a < toScc b ↔ a < b := by
  show toScc a ≤ toScc b ∧ ¬toScc b ≤ toScc a ↔ _
  rw [le_iff_condense_le, le_iff_condense_le]
  rfl

instance condense_acyclic : IsAcyclic G.Condense where
  no_cycles := by
    intro x ⟨y, edge, path⟩
    induction x using Quot.ind with | mk x =>
    induction y using Quot.ind with | mk y =>
    have : x ≈ y := ⟨?_, le_iff_condense_le.mp ⟨path⟩⟩
    exact edge.1 this
    apply (lt_of_condense_edge _).left
    assumption

class IsUndirected (G: Graph) extends Relation.IsSymmetric G.Edge: Prop where

def toUndirected (G: Graph) : Graph where
  Node := G.Node
  Edge a b := G.Edge a b ∨ G.Edge b a

instance : IsUndirected G.toUndirected where
  symm := Or.symm

def symm_le [IsUndirected G] {a b: G} : a ≤ b -> b ≤ a := by
  rw [le_iff_refltransgen_edge, le_iff_refltransgen_edge]
  apply Relation.symm

def Path.symm [IsUndirected G] {a b: G} : G.Path a b -> G.Path b a
| .refl => .refl
| .edge e p => p.symm ++ single _ _ (Relation.symm e)

end Graph
