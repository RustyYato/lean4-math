import Math.Data.Zf.Basic
import Math.Function.Basic

def Class := Set ZfSet
deriving HasSubset, EmptyCollection, Nonempty, Union, Inter

namespace Class

def toSet (c: Class) : Set ZfSet := c

def Class.ofZfSet (x: ZfSet): Class := Set.mk fun y => y ∈ x

def Class.ofZfSet.inj : Function.Injective Class.ofZfSet := by
  intro a b eq
  replace eq := Set.mk.inj eq
  replace eq := congrFun eq
  ext
  rw [eq]

instance : Coe ZfSet Class where
  coe := Class.ofZfSet

def isZfSet (c: Class) : Prop := ∃z: ZfSet, c = z

instance : Membership Class Class where
  mem a b := ∃z ∈ a.toSet, b = z

instance : CoeFun Class (fun _ => ZfSet -> Prop) := ⟨(·.Mem)⟩

def zfmem (a: Class) (z: ZfSet) : a z ↔ ↑z ∈ a := by
  apply Iff.intro
  intro mem
  exists z
  intro ⟨w, w_in, eq⟩
  cases Class.ofZfSet.inj eq
  assumption

def univ : Class := Set.univ _

def not_mem_empty (a: Class) : ¬a ∈ (∅: Class) := by
  intro ⟨h, _, _⟩
  contradiction

def not_zfmem_empty (a: ZfSet) : ¬(∅: Class) a := False.elim

def mem_univ (a: Class) : a ∈ univ ↔ a.isZfSet := by
  apply Iff.intro
  intro ⟨h, _, _⟩
  exists h
  intro ⟨h, x⟩
  exists h

def zfmem_univ (a: ZfSet) : univ a := True.intro

def mem_union {a b: Class} : ∀{x}, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := by
  intro x
  apply Iff.intro
  intro ⟨z, mem, _⟩
  subst x
  cases Set.mem_union.mp mem
  left; exists z
  right; exists z
  intro h
  cases h <;> rename_i h
  all_goals
    obtain ⟨z, mem, eq⟩ := h
    subst eq
    exists z
    apply And.intro _ rfl
    apply Set.mem_union.mpr
  left; assumption
  right; assumption

def mem_inter {a b: Class} : ∀{x}, x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := by
  intro x
  apply Iff.intro
  intro ⟨z, mem, _⟩
  subst x
  cases Set.mem_inter.mp mem
  apply And.intro
  exists z
  exists z
  intro h
  cases h <;> rename_i h g
  obtain ⟨z, mem, eq⟩ := h
  obtain ⟨z, mem, eq⟩ := g
  subst eq; cases Class.ofZfSet.inj eq
  exists z

def sep (P: ZfSet -> Prop) (a: Class) : Class := Set.sep P a

def congToClass (x : Set Class) : Class := Set.mk fun y => ↑y ∈ x
def classToCong (x : Class) : Set Class := Set.mk fun y => y ∈ x

def powerset (a: Class) : Class := congToClass (Set.powerset a)

def sUnion (a: Class) : Class := ⋃ id (α := Set (Set _)) (classToCong a)

def sInter (a: Class) : Class := ⋂ id (α := Set (Set _)) (classToCong a)

instance : SUnion Class Class := ⟨Class.sUnion⟩
instance : SInter Class Class := ⟨Class.sInter⟩

end Class
