import Math.Algebra.Group.Theory.Basic
import Math.Algebra.Group.SetLike.Basic

class IsNormalSubgroup
  (S: Type*) {α: Type*} [SetLike S α] [GroupOps α] [IsGroup α] extends IsSubgroup S where
  mem_conj (s: S): ∀x: α, ∀{a}, a ∈ s -> Group.conj x a ∈ s

def mem_conj [SetLike S α] [GroupOps α] [IsGroup α] [IsNormalSubgroup S]
  (s: S): ∀x: α, ∀{a}, a ∈ s -> Group.conj x a ∈ s := IsNormalSubgroup.mem_conj _

structure NormalSubgroup (α: Type*) [GroupOps α] [IsGroup α] extends Subgroup α where
  mem_conj: ∀x: α, ∀{a}, a ∈ carrier -> Group.conj x a ∈ carrier

namespace NormalSubgroup

variable [GroupOps α] [IsGroup α] [GroupOps β] [IsGroup β]

instance : SetLike (NormalSubgroup α) α where
  coe s := s.carrier
  coe_inj := by
    intro a b eq
    cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsNormalSubgroup (NormalSubgroup α) where
  mem_one s := s.mem_one
  mem_inv s := s.mem_inv
  mem_mul s := s.mem_mul
  mem_conj s := s.mem_conj

inductive Generate (U: Set α) : α -> Prop where
| of (x: α) : x ∈ U -> Generate U x
| one : Generate U 1
| inv : Generate U a -> Generate U a⁻¹
| mul : Generate U a -> Generate U b -> Generate U (a * b)
| conj (x: α) {a: α} : Generate U a -> Generate U (Group.conj x a)

def generate (U: Set α) : NormalSubgroup α where
  carrier := Set.mk (Generate U)
  mem_one := Generate.one
  mem_inv := Generate.inv
  mem_mul := Generate.mul
  mem_conj := Generate.conj

instance [GroupOps α] [IsGroup α] : Bot (NormalSubgroup α) where
  bot := {
    toSubgroup := ⊥
    mem_conj := by
      rintro x a rfl
      rw [map_one]
      apply mem_one (⊥: Subgroup α)
  }

@[ext]
def ext (a b: NormalSubgroup α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

def preimage (f: α →* β) (s: NormalSubgroup β) : NormalSubgroup α where
  toSubgroup := Subgroup.preimage f s.toSubgroup
  mem_conj := by
    intro x a ha
    show f (x⁻¹ * a * x) ∈ s
    rw [map_mul,map_mul, map_inv]
    apply mem_conj
    assumption

def image (f: α →* β) (s: NormalSubgroup α) (h: Function.Surjective f) : NormalSubgroup β where
  toSubgroup := Subgroup.image f s.toSubgroup
  mem_conj := by
    rintro x _ ⟨a, ha, rfl⟩
    apply Set.mem_image.mpr
    obtain ⟨x, rfl⟩ := h x
    exists Group.conj x a
    apply And.intro
    apply mem_conj s
    assumption
    rw [Group.apply_conj, Group.apply_conj]
    simp [map_mul, map_inv]

def kernel (f: α →* β) : NormalSubgroup α := preimage f ⊥

end NormalSubgroup
