import Math.Type.Notation
import Math.Data.Setoid.Basic
import Math.AxiomBlame

def Erased (α: Type*) := Quot (fun _ _: α => True)

-- a version of funext which doesn't depend on Quot.sound
axiom funext' (f g: α -> β) : (∀x, f x = g x) -> f = g

axiom erased (a b: Erased α) : a = b

instance : Subsingleton (Erased α) where
  allEq := erased

structure Set (α: Type*) where
  Mem: α -> Prop

instance : Membership α (Set α) where
  mem s x := s.Mem x

@[ext]
def Set.ext (a b: Set α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := by
  intro h
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  congr
  apply funext'
  intro x
  apply propext
  apply h

@[simp]
def Set.mk_mem (a: α) (P: α -> Prop) : (a ∈ Set.mk P) = (P a) := rfl

namespace Erased

def mk : α -> Erased α := Quot.mk _
@[induction_eliminator]
def ind {motive: Erased α -> Prop} (mk: ∀x, motive (mk x)) (e: Erased α) : motive e := Quot.ind mk e
def rec (f: α -> β) (h: ∀x y: α, f x = f y) (e: Erased α) : β := Quot.lift f (fun _ _ _ => h _ _) e
def map (f: α -> β) (e: Erased α) : Erased β := by
  apply e.rec (mk ∘ f)
  intro x y; apply Subsingleton.allEq

end Erased

protected structure Set.Quotient (s: Setoid α) : Type _ where
  ofCarrier ::
  carrier: Set α
  rep: Erased (Σ'x: α, carrier = Set.mk (x ≈ ·))

namespace Set.Quotient

@[ext]
def ext {s: Setoid α} (a b: Set.Quotient s) : a.carrier = b.carrier -> a = b := by
  intro h
  cases a; cases b
  dsimp at h; cases h
  congr
  apply Subsingleton.allEq

def mk (s: Setoid α) (a: α) : Set.Quotient s where
  rep := .mk ⟨a, rfl⟩
  carrier := _

def sound {s: Setoid α} (a b: α) : a ≈ b -> mk s a = mk s b := by
  intro h
  ext x
  apply Iff.intro
  intro g
  exact s.iseqv.trans (s.iseqv.symm h) g
  intro g
  exact s.iseqv.trans h g

@[induction_eliminator]
def ind {s: Setoid α} {motive: Set.Quotient s -> Prop} (mk: ∀x, motive (mk s x)) (q: Set.Quotient s) : motive q := by
  obtain ⟨_, x, rfl⟩ := q
  apply mk

def map {sα: Setoid α} {sβ: Setoid β} (f: α -> β) (resp: ∀a b: α, a ≈ b -> f a ≈ f b) (q: Set.Quotient sα) : Set.Quotient sβ where
  carrier := { Mem b := ∃a ∈ q.carrier, f a ≈ b }
  rep := by
    obtain ⟨q, hq⟩ := q
    apply hq.map
    intro ⟨x, hx⟩
    exists f x
    ext b
    simp
    apply Iff.intro
    intro ⟨a', a'_mem, eqv⟩
    apply sβ.iseqv.trans _ eqv
    apply resp
    rw [hx] at a'_mem
    assumption
    intro h
    exists x
    apply And.intro
    rw [hx]; apply sα.iseqv.refl
    assumption

@[simp]
def mem_mk_carrier {s: Setoid α} (a b: α) : (b ∈ (mk s a).carrier) = (a ≈ b) := rfl

def exact {s: Setoid α} (a b: α) : mk s a = mk s b -> a ≈ b := by
  intro h
  have : b ∈ (mk s a).carrier := by rw [h]; simp; apply s.iseqv.refl
  assumption

@[simp]
def map_mk {sα: Setoid α} {sβ: Setoid β} (f: α -> β) (resp: ∀a b: α, a ≈ b -> f a ≈ f b) (a: α) : map f resp (mk sα a) = mk sβ (f a) := by
  ext b
  simp only [map, Set.mk_mem]
  apply Iff.intro
  intro h
  obtain ⟨a', ha', eqv⟩ := h
  apply sβ.iseqv.trans _ eqv
  apply resp
  assumption
  intro x
  exists a
  rw [mem_mk_carrier]
  apply And.intro
  apply sα.iseqv.refl
  assumption

def exists_rep {s: Setoid α} (q: Set.Quotient s) : ∃a: α, mk s a = q := by
  induction q with | mk x =>
  exists x

def lift {s: Setoid α} (f: α -> β) (resp: ∀a b, a ≈ b -> f a = f b) (q: Set.Quotient s) : β :=
  (q.map (sβ := Setoid.eqSetoid) f resp).rep.rec (fun x => x.1) <| by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    simp
    rw [hx] at hy
    replace hy : (Set.mk (x = ·)) = (Set.mk (y = ·)) := hy
    show y ∈ (Set.mk (x = ·))
    rw [hy]
    rfl

def lift_mk {s: Setoid α} (f: α -> β) (resp: ∀a b: α, a ≈ b -> f a = f b) (a: α) : lift f resp (mk s a) = f a := rfl

-- at this point we have replicated the api for Quotient, i.e. Quotient.mk, Quotient.lift, and Quotient.ind
-- where both mk and lift are computable! And with two new axioms which can both be proven from Quot.sound
-- 1. `funext'`, which is usually taken as an axiom in other theorem provers anyways
-- 2. `erased`, which just states that `Erased` is subsingleton, which is obviously true based on the definition
-- so Set.Quotient provides a model for Quotient and shows that Quotient is consistent with Lean

#print axioms Set.Quotient.mk
#print axioms Set.Quotient.ind
#print axioms Set.Quotient.lift

end Set.Quotient
