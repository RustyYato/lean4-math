import Math.Algebra.Ring.Theory.Ideal.TwoSided.Principal
import Math.Algebra.Ring.Theory.Ideal.TwoSided.Quotient

variable {α: Type*} [RingOps α] [IsRing α] [IsCommMagma α] [Dvd α] [IsLawfulDvd α]

def RMod (a: α): Type _ := (Ideal.of_dvd a).toRing

namespace RMod

variable {A: α}

instance instRingOps : RingOps (RMod A) := inferInstanceAs (RingOps (Ideal.toRing _))
instance instRing : IsRing (RMod A) := inferInstanceAs (IsRing (Ideal.toRing _))
instance instCommMagma : IsCommMagma (RMod A) := inferInstanceAs (IsCommMagma (Ideal.toRing _))
instance instAlgMap : AlgebraMap α (RMod A) where
  toRingHom := Ideal.mkQuot _
instance isntSMul : SMul α (RMod A) where
  smul a b := algebraMap a * b
instance instAlgebra : IsAlgebra α (RMod A) where
  commutes _ _ := by rw [mul_comm]
  smul_def _ _ := rfl

def map_eq_zero : (algebraMap A: RMod A) = 0 := by
  apply Quotient.sound
  show _ ∣ _
  rw [sub_zero]

end RMod
