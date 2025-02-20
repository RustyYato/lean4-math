import Math.Algebra.Ring.Theory.Basic
import Math.Data.Set.Basic
import Math.Order.Lattice.Complete
import Math.Order.GaloisConnection
import Math.Data.Set.Lattice

namespace Ring

structure AddSubgroup (R: Ring α) where
  carrier: Set R
  mem_zero: 0 ∈ carrier
  mem_add: ∀{x y}, x ∈ carrier -> y ∈ carrier -> x + y ∈ carrier
  mem_neg: ∀{x}, x ∈ carrier -> -x ∈ carrier

structure LeftIdeal (R: Ring α) extends AddSubgroup R where
  mem_mul_left: ∀(r: R) {x}, x ∈ carrier -> r * x ∈ carrier

structure RightIdeal (R: Ring α) extends AddSubgroup R where
  mem_mul_right: ∀(r: R) {x}, x ∈ carrier -> x * r ∈ carrier

structure Ideal (R: Ring α) extends LeftIdeal R, RightIdeal R where

def Ideal.zero (R: Ring α) : Ideal R where
  carrier := {0}
  mem_zero := rfl
  mem_add := by
    rintro _ _ rfl rfl
    apply add_zero
  mem_neg := by
    rintro _ rfl
    apply neg_zero
  mem_mul_left := by
    rintro r _ rfl
    apply mul_zero
  mem_mul_right := by
    rintro r _ rfl
    apply zero_mul

def Ideal.univ (R: Ring α) : Ideal R where
  carrier := ⊤
  mem_zero := True.intro
  mem_add _ _ := True.intro
  mem_neg _ := True.intro
  mem_mul_left _ _ _ := True.intro
  mem_mul_right _ _ _ := True.intro

instance : LE (Ideal R) where
  le a b := a.carrier ⊆ b.carrier

instance : LT (Ideal R) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance (R: Ring α) : Inf (Ideal R) where
  inf a b := {
    carrier := a.carrier ∩ b.carrier
    mem_zero := ⟨a.mem_zero, b.mem_zero⟩
    mem_add | ⟨ha, hb⟩, ⟨ga, gb⟩ => ⟨a.mem_add ha ga, b.mem_add hb gb⟩
    mem_neg | ⟨ha, hb⟩ => ⟨a.mem_neg ha, b.mem_neg hb⟩
    mem_mul_left | r, ⟨ha, hb⟩ => ⟨a.mem_mul_left r ha, b.mem_mul_left r hb⟩
    mem_mul_right | r, ⟨ha, hb⟩ => ⟨a.mem_mul_right r ha, b.mem_mul_right r hb⟩
  }

instance (R: Ring α) : InfSet (Ideal R) where
  sInf U := {
    carrier := ⋂ U.image (fun x => x.carrier)
    mem_zero := by
      rintro x ⟨x, _, rfl⟩
      apply x.mem_zero
    mem_add := by
      rintro x y hx hy _ ⟨a, ha, rfl⟩
      apply a.mem_add
      apply hx; exists a
      apply hy; exists a
    mem_neg := by
      rintro x hx _ ⟨a, ha, rfl⟩
      apply a.mem_neg
      apply hx
      exists a
    mem_mul_left := by
      rintro r x hx _ ⟨a, ha, rfl⟩
      apply a.mem_mul_left
      apply hx; exists a
    mem_mul_right := by
      rintro r x hx _ ⟨a, ha, rfl⟩
      apply a.mem_mul_right
      apply hx; exists a
  }

def AddSubgroup.carrier_inj {a b: AddSubgroup R} : a.carrier = b.carrier ↔ a = b :=
  Function.Injective.eq_iff <| by
    intro a b eq
    cases a; congr

def LeftIdeal.carrier_inj {a b: LeftIdeal R} : a.carrier = b.carrier ↔ a = b :=
  Function.Injective.eq_iff (f₀ := fun a: LeftIdeal R => a.carrier) <| by
    intro a b eq
    cases a; congr
    apply AddSubgroup.carrier_inj.mp
    assumption

def RightIdeal.carrier_inj {a b: RightIdeal R} : a.carrier = b.carrier ↔ a = b :=
  Function.Injective.eq_iff (f₀ := fun a: RightIdeal R => a.carrier) <| by
    intro a b eq
    cases a; congr
    apply AddSubgroup.carrier_inj.mp
    assumption

def Ideal.carrier_inj {a b: Ideal R} : a.carrier = b.carrier ↔ a = b :=
  Function.Injective.eq_iff (f₀ := fun a: Ideal R => a.carrier) <| by
    intro a b eq
    cases a; congr
    apply LeftIdeal.carrier_inj.mp
    assumption

inductive Ideal.Generate (R: Ring α) (U: Set R) : R -> Prop where
| of (x: R) : x ∈ U -> Generate R U x
| zero : Generate R U 0
| add (a b: R) : Generate R U a -> Generate R U b -> Generate R U (a + b)
| neg (a: R) : Generate R U a -> Generate R U (-a)
| mul_left (r: R) (x: R) : Generate R U x -> Generate R U (r * x)
| mul_right (r: R) (x: R) : Generate R U x -> Generate R U (x * r)

def toIdeal (R: Ring α) (U: Set R) : Ideal R where
  carrier := Set.mk (Ideal.Generate R U)
  mem_zero := Ideal.Generate.zero
  mem_add := Ideal.Generate.add _ _
  mem_neg := Ideal.Generate.neg _
  mem_mul_left _ _ := Ideal.Generate.mul_left _ _
  mem_mul_right _ _ := Ideal.Generate.mul_right _ _

def Ideal.oemb : Ideal R ↪o Set R where
  toFun a := a.carrier
  resp_rel := Iff.rfl
  inj _ _ := Ideal.carrier_inj.mp

instance : IsLawfulLT (Ideal R) := ⟨Iff.rfl⟩

instance : IsPartialOrder (Ideal R) :=
  Ideal.oemb.inducedIsPartialOrder'

def Ideal.giGenerate (R: Ring α) : @GaloisInsertion (Set R) (Ideal R) _ _ R.toIdeal (fun x => x.carrier) where
  gc := by
    intro a b
    dsimp
    apply Iff.intro
    · intro h x x_in_a
      exact h x (Ideal.Generate.of _ x_in_a)
    · intro h x hx
      induction hx with
      | of =>
        apply h
        assumption
      | zero => apply b.mem_zero
      | add => apply b.mem_add <;> assumption
      | neg => apply b.mem_neg <;> assumption
      | mul_left => apply b.mem_mul_left <;> assumption
      | mul_right => apply b.mem_mul_right <;> assumption
  le_l_u := by
    intro x r hx
    apply Ideal.Generate.of
    assumption

instance (R: Ring α) : CompleteLattice (Ideal R) := {
  (Ideal.giGenerate R).liftCompleteLattice with
  bot := Ideal.zero R
  top := Ideal.univ R
  inf a b := a ⊓ b
  sInf := sInf
  bot_le := by
    rintro x h rfl
    apply x.mem_zero
  le_top := by
    intro x h _
    trivial
  inf_le_left := by
    intro a b x ⟨ha, hb⟩
    assumption
  inf_le_right := by
    intro a b x ⟨ha, hb⟩
    assumption
  le_inf := by
    intro a b x ha hb y hy
    apply And.intro
    apply ha <;> assumption
    apply hb <;> assumption
  sInf_le := by
    intro s x hs a ha
    apply ha
    exists x
  le_sInf := by
    rintro  k U h x hx _ ⟨a, ha, rfl⟩
    apply h
    assumption
    assumption
}

end Ring
