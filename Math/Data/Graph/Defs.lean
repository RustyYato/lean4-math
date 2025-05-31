import Math.Relation.Basic
import Math.Data.Set.Defs
import Math.Logic.Equiv.Like
import Math.Data.Set.Like

-- Graphs are represented by their edge relations. This allows us to easily implement new graphs
-- and a lattice struture on graphs.
structure Graph (α: Type*) where
  Edge: α -> α -> Prop

structure Subgraph (G: Graph α) where
  carrier: Set α
  Edge: ∀a b, a ∈ carrier -> b ∈ carrier -> Prop
  map_edge: ∀a b ha hb, Edge a b ha hb -> G.Edge a b

instance (G: Graph α) : Membership α (Subgraph G) where
  mem S a := a ∈ S.carrier

instance : CoeSort (Subgraph G) (Type _) where
  coe s := { x // x ∈ s }

@[coe]
def Subgraph.toGraph {G: Graph α} (S: Subgraph G) : Graph S where
  Edge a b := S.Edge a b a.property b.property

namespace Graph

section Path

protected inductive Path (G: Graph α) : α -> α -> Type _ where
| nil (a: α) : Graph.Path G a a
| cons (a b c: α) : Graph.Edge G a b -> Graph.Path G b c -> Graph.Path G a c

protected inductive Path.Nonempty {G: Graph α} : ∀{a b: α}, G.Path a b -> Prop where
| intro (a b c: α) (e: G.Edge a b) (p: G.Path b c) : Graph.Path.Nonempty (.cons a b c e p)

def Path.trans {G: Graph α} : G.Path a b -> G.Path b c -> G.Path a c
| .nil _, p => p
| .cons a _ c e p₀, p₁ => .cons _ _ _ e (p₀.trans p₁)

protected def HasPath (G: Graph α) (a b: α) := Nonempty (G.Path a b)

def Path.single {G: Graph α} (r: G.Edge a b) : G.Path a b := .cons _ _ _ r (.nil _)

instance (G: Graph α) : Trans G.Path G.Path G.Path where
  trans := .trans
instance (G: Graph α) : Trans G.Path G.Edge G.Path where
  trans h g := h.trans (.single g)
instance (G: Graph α) : Trans G.Edge G.Path G.Path where
  trans h g := trans (Path.single h) g
instance (G: Graph α) : Trans G.HasPath G.Edge G.HasPath where
  trans | ⟨h⟩, g => ⟨trans h g⟩
instance (G: Graph α) : Trans G.Edge G.HasPath G.HasPath where
  trans | h, ⟨g⟩ => ⟨trans h g⟩

@[refl]
def HasPath.refl {G: Graph α} (a: α) : G.HasPath a a := ⟨.nil _⟩
def HasPath.trans {G: Graph α} (h₀: G.HasPath a b) (h₁: G.HasPath b c) : G.HasPath a c :=
  have ⟨p₀⟩ := h₀
  have ⟨p₁⟩ := h₁
  ⟨p₀.trans p₁⟩

instance (G: Graph α) : Relation.IsRefl G.HasPath := ⟨.refl⟩
instance (G: Graph α) : Relation.IsTrans G.HasPath := ⟨.trans⟩

-- a graph is cyclic if it contains a node which has a non-trivial path back to itself
def IsCyclic (G: Graph α) : Prop := ∃(a: α) (p: G.Path a a), p.Nonempty

end Path

section Scc

def scc_setoid (G: Graph α) : Setoid α := Relation.setoid (Relation.SymmGen G.HasPath)

def Scc (G: Graph α) := Quotient G.scc_setoid

private def scc_edge_aux (G: Graph α) (a b: α) : Prop :=
  have := G.scc_setoid
  ∃a' b', a ≈ a' ∧ b ≈ b' ∧ ¬a' ≈ b' ∧ G.Edge a' b'

-- the condensation of the given graph, i.e. each node in the scc corrosponds to a subgraph
-- where every node has a path to every other node of the original. This is a naturally acyclic graph.
def scc (G: Graph α) : Graph G.Scc where
  Edge := by
    refine Quotient.lift₂ G.scc_edge_aux ?_
    intro a b c d ac bd
    simp; apply Iff.intro
    intro ⟨a', b', ha, hb, h⟩
    refine ⟨a', b', ?_, ?_, h⟩
    exact trans (Relation.symm ac) ha
    exact trans (Relation.symm bd) hb
    intro ⟨a', b', ha, hb, h⟩
    refine ⟨a', b', ?_, ?_, h⟩
    exact trans ac ha
    exact trans bd hb

def toScc (G: Graph α) : α -> G.Scc := Quotient.mk _

def toScc_eq (G: Graph α) : G.toScc a = G.toScc b ↔ Relation.SymmGen G.HasPath a b := by
  apply Iff.intro
  apply Quotient.exact
  apply Quotient.sound (s := G.scc_setoid)

@[induction_eliminator]
def scc_ind (G: Graph α) {motive: G.Scc -> Prop} : (toScc: ∀x, motive (G.toScc x)) -> ∀s, motive s := Quotient.ind

def toScc_surj (G: Graph α) : Function.Surjective G.toScc := by
  intro x
  induction x with | _ x =>
  exists x

def path_of_scc_edge (G: Graph α) : G.scc.Edge (G.toScc a) (G.toScc b) -> G.HasPath a b := by
  intro ⟨a', b', ha, hb, ne, h⟩
  exact trans ha.1 (trans h hb.2)

def scc_path_of_edge (G: Graph α) : G.Edge a b -> G.scc.HasPath (G.toScc a) (G.toScc b) := by
  intro e
  by_cases h:G.HasPath b a
  obtain ⟨h⟩ := h
  have : G.toScc a = G.toScc b := by
    apply G.toScc_eq.mpr
    apply Relation.SymmGen.intro
    exact ⟨Path.single e⟩
    exact ⟨h⟩
  rw [this]
  refine ⟨Path.single ?_⟩
  refine ⟨a, b, ?_, ?_, ?_, e⟩
  rfl; rfl
  intro g; apply h
  exact g.2

def scc_path_iff (G: Graph α) : G.HasPath a b ↔ G.scc.HasPath (G.toScc a) (G.toScc b) := by
  apply Iff.intro
  · intro ⟨h⟩
    induction h with
    | nil => rfl
    | cons a b c ab bc ih =>
      apply Relation.trans' _ ih
      clear ih
      apply scc_path_of_edge
      assumption
  · generalize ha:G.toScc a = a'
    generalize hb:G.toScc b = b'
    intro ⟨h⟩
    induction h generalizing a b with
    | nil =>
      subst hb
      rw [toScc_eq] at ha
      exact ha.1
    | cons a b c ab bc ih =>
      subst hb ha
      rename_i k
      induction k with | _ k =>
      apply Relation.trans' _ (ih rfl rfl)
      apply path_of_scc_edge
      assumption

def scc_acyclic (G: Graph α) : ¬G.scc.IsCyclic := by
  intro ⟨a, p, h⟩; cases h
  rename_i b e p
  induction a with | toScc a =>
  induction b with | toScc b =>
  obtain ⟨a', b', ha, hb, ne, h⟩:= e
  apply ne
  replace p: G.scc.HasPath _ _ := ⟨p⟩
  rw [←scc_path_iff] at p
  clear ne
  apply Relation.SymmGen.intro _ (trans (trans hb.right p) ha.left)
  exact ⟨Path.single h⟩

end Scc

section Equiv

protected class IsEmbedding (F: Type*) {α β: Type*} [EmbeddingLike F α β] (Ga: Graph α) (Gb: Graph β) : Prop where
  protected map_edge (f: F) (a b: α) : Ga.Edge a b -> Gb.Edge (f a) (f b) := by intro f; exact f.map_edge

protected structure Embedding (Ga: Graph α) (Gb: Graph β) extends α ↪ β where
  protected map_edge (a b: α) : Ga.Edge a b -> Gb.Edge (toFun a) (toFun b)

def map_edge {F α β: Type*} [EmbeddingLike F α β] (Ga: Graph α) (Gb: Graph β) [Graph.IsEmbedding F Ga Gb] (f: F) (a b: α) : Ga.Edge a b -> Gb.Edge (f a) (f b) :=
  Graph.IsEmbedding.map_edge f a b

infixr:25 " ↪g " => Graph.Embedding

instance (Ga: Graph α) (Gb: Graph β) : EmbeddingLike (Ga ↪g Gb) α β where
instance (Ga: Graph α) (Gb: Graph β) : Graph.IsEmbedding (Ga ↪g Gb) Ga Gb where

def ofSubgraph {G: Graph α} (S: Subgraph G) : S.toGraph ↪g G where
  toEmbedding := Embedding.subtypeVal
  map_edge _ _ := by apply S.map_edge

end Equiv

end Graph
