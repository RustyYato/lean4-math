import Math.Algebra.Hom.Defs
import Math.Algebra.Monoid.Associate.Dvd
import Math.Algebra.Group.Units.Defs

section

class NormalizationMonoid (α: Type*) [MonoidOps α] [IsMonoid α] [IsCommMagma α] where
  protected normUnit: α -> Units α
  normUnit_mul (a b: α) : normUnit (a * b) = normUnit a * normUnit b
  normUnit_unit (a: Units α) : normUnit a.val = a⁻¹
  -- all absorbing elements get mapped to one
  normUnit_absorbing (x: α) (h: ∀a: α, x * a = x) : normUnit x = 1

variable [MonoidOps α] [IsMonoid α] [IsCommMagma α] [NormalizationMonoid α]

def normUnit : α →* Units α where
  toFun a := NormalizationMonoid.normUnit a
  map_one := NormalizationMonoid.normUnit_unit 1
  map_mul := NormalizationMonoid.normUnit_mul _ _

def apply_normUnit (a: α) : normUnit a = NormalizationMonoid.normUnit a := rfl

def normalize : α →* α where
  toFun a := a * (normUnit a: α)
  map_one := by rw [map_one, one_mul]; rfl
  map_mul {x y} := by rw [map_mul, Units.val_mul, mul_assoc, mul_left_comm y, ←mul_assoc x]

@[simp] def apply_normalize (a: α) : normalize a = a * normUnit a := rfl

def normalize₀ [Zero α] [IsMulZeroClass α] : α →*₀ α := {
  normalize with
  map_zero := by
    show (0: α) * NormalizationMonoid.normUnit (0: α) = 0
    rw [zero_mul]
}

@[simp] def apply_normalize₀ [Zero α] [IsMulZeroClass α] (a: α) : normalize₀ a = a * normUnit a := rfl

def normalize_unit (a: Units α) : normalize a.val = 1 := by
  simp [apply_normalize, apply_normUnit, NormalizationMonoid.normUnit_unit a, ←Units.val_mul]

def normalize_isassoc (a: α) : IsAssociated (normalize a) a := by
  exists (normUnit a)⁻¹
  simp [mul_assoc, ←Units.val_mul]

def normalize_eq_of_isassoc (a b: α) (h: IsAssociated a b) : normalize a = normalize b := by
  obtain ⟨u, rfl⟩ := h
  rw [map_mul, normalize_unit, mul_one]

protected def Associates.normalize : Associates α →* α := by
  refine (Associates.Con α).liftGroupHom normalize ?_
  intro a b h
  apply normalize_eq_of_isassoc
  assumption

protected def Associates.normalize₀ [Zero α] [IsMulZeroClass α] : Associates α →*₀ α := by
  refine (Associates.Con α).liftGroupWithZeroHom normalize₀ ?_
  intro a b h
  apply normalize_eq_of_isassoc
  assumption

def Associates.apply_mk_normalize (a: α) : (Associates.mk a).normalize = normalize a := rfl
def Associates.apply_mk_normalize₀ [Zero α] [IsMulZeroClass α] (a: α) : (Associates.mk a).normalize₀ = normalize₀ a := rfl

variable [Dvd α] [IsLawfulDvd α]

def normalize_eq_of_dvd_antisymm [IsMulCancel α] {a b : α} (hab : a ∣ b) (hba : b ∣ a) :
  normalize a = normalize b := by
  apply normalize_eq_of_isassoc
  apply dvd_antisymm
  assumption
  assumption

end

class GcdMonoidOps (α: Type*) extends MonoidOps α, Dvd α where
  protected gcd: α -> α -> α
  protected lcm: α -> α -> α

def gcd [GcdMonoidOps α] : α -> α -> α := GcdMonoidOps.gcd
def lcm [GcdMonoidOps α] : α -> α -> α := GcdMonoidOps.lcm

class IsGcdMonoid (α: Type*) [GcdMonoidOps α] extends IsMonoid α, IsCommMagma α, IsLawfulDvd α where
  gcd_dvd_left (a b: α): gcd a b ∣ a
  gcd_dvd_right (a b: α): gcd a b ∣ b
  dvd_gcd (k a b: α): k ∣ a -> k ∣ b -> k ∣ gcd a b
  -- of_dvd_gcd (k a b: α) : k ∣ gcd a b -> k ∣ a ∧ k ∣ b
  gcd_mul_lcm (a b: α): gcd a b * lcm a b = a * b

  -- we specify zero via absorbing elemnts, so we don't need to require `[Zero α]`
  lcm_absorb (a b: α) (h: IsAbsorbing b) : lcm a b = b
  absorb_lcm (a b: α) (h: IsAbsorbing a) : lcm a b = a

variable [GcdMonoidOps α] [IsGcdMonoid α] [IsMulCancel α]
   [Zero α] [IsMulZeroClass α]

def gcd_dvd_left (a b: α): gcd a b ∣ a := IsGcdMonoid.gcd_dvd_left _ _
def gcd_dvd_right (a b: α): gcd a b ∣ b := IsGcdMonoid.gcd_dvd_right _ _
def dvd_gcd (k a b: α): k ∣ a -> k ∣ b -> k ∣ gcd a b := IsGcdMonoid.dvd_gcd _ _ _
def lcm_absorb (a b: α) (h: IsAbsorbing b) : lcm a b = b := IsGcdMonoid.lcm_absorb _ _ h
def absorb_lcm (a b: α) (h: IsAbsorbing a) : lcm a b = a := IsGcdMonoid.absorb_lcm _ _ h
def gcd_mul_lcm (a b: α): gcd a b * lcm a b = a * b := IsGcdMonoid.gcd_mul_lcm _ _

@[simp] def lcm_zero (a: α) : lcm a 0 = 0 := lcm_absorb _ _ inferInstance
@[simp] def zero_lcm (a: α) : lcm 0 a = 0 := absorb_lcm _ _ inferInstance

def IsAssociated.gcd_comm (a b: α) : IsAssociated (gcd a b) (gcd b a) := by
  apply dvd_antisymm
  apply dvd_gcd
  apply gcd_dvd_right
  apply gcd_dvd_left
  apply dvd_gcd
  apply gcd_dvd_right
  apply gcd_dvd_left

def IsAssociated.gcd_assoc (a b c: α) : IsAssociated (gcd a (gcd b c)) (gcd (gcd a b) c) := by
  apply dvd_antisymm
  apply dvd_gcd
  apply dvd_gcd
  apply gcd_dvd_left
  apply dvd_trans
  apply gcd_dvd_right
  apply gcd_dvd_left
  apply dvd_trans
  apply gcd_dvd_right
  apply gcd_dvd_right
  apply dvd_gcd
  apply dvd_trans
  apply gcd_dvd_left
  apply gcd_dvd_left
  apply dvd_gcd
  apply dvd_trans
  apply gcd_dvd_left
  apply gcd_dvd_right
  apply gcd_dvd_right

def IsAssociated.gcd_zero (a: α) : IsAssociated (gcd a 0) a := by
  apply dvd_antisymm
  apply gcd_dvd_left
  apply dvd_gcd
  rfl
  apply dvd_zero

def IsAssociated.zero_gcd (a: α) : IsAssociated (gcd 0 a) a := by
  apply Relation.trans'
  apply gcd_comm
  apply gcd_zero

def IsAssociated.gcd_congr (a b c d: α) (ac: IsAssociated a c) (bd: IsAssociated b d) : IsAssociated (gcd a b) (gcd c d) := by
  apply dvd_antisymm
  apply dvd_gcd
  apply dvd_trans
  apply gcd_dvd_left
  apply dvd_of_is_associated
  assumption
  apply dvd_trans
  apply gcd_dvd_right
  apply dvd_of_is_associated
  assumption

  apply dvd_gcd
  apply dvd_trans
  apply gcd_dvd_left
  apply dvd_of_is_associated
  apply Relation.symm; assumption
  apply dvd_trans
  apply gcd_dvd_right
  apply dvd_of_is_associated
  apply Relation.symm; assumption

def dvd_gcd_iff {k a b: α} : k ∣ gcd a b ↔ k ∣ a ∧ k ∣ b := by
  apply Iff.intro
  intro h
  apply And.intro
  apply dvd_trans h
  apply gcd_dvd_left
  apply dvd_trans h
  apply gcd_dvd_right
  intro ⟨hb, hc⟩
  apply dvd_gcd
  assumption
  assumption

-- def IsAssociated.gcd_mul (a b k: α) : IsAssociated (gcd a b * k) (gcd (a * k) (b * k)) := by
--   apply dvd_antisymm
--   apply dvd_gcd
--   apply mul_dvd_mul_right
--   apply gcd_dvd_left
--   apply mul_dvd_mul_right
--   apply gcd_dvd_right
--   have ⟨x, hx⟩ := dvd_iff.mp (gcd_dvd_left (a * k) (b * k))
--   apply of_mul_dvd_mul_right
--   rw [←hx, mul_comm_right _ k]
--   apply mul_dvd_mul_right




--   sorry

-- def dvd_lcm_left (a b: α) : a ∣ lcm a b := by
--   apply of_mul_dvd_mul_left
--   rw [gcd_mul_lcm, mul_comm]
--   apply mul_dvd_mul_left
--   apply gcd_dvd_right

-- def dvd_lcm_right (a b: α) : b ∣ lcm a b := by
--   apply of_mul_dvd_mul_left
--   rw [gcd_mul_lcm]
--   apply mul_dvd_mul_right
--   apply gcd_dvd_left

-- def lcm_dvd (a b k: α) : a ∣ k -> b ∣ k -> lcm a b ∣ k := by
--   rw [dvd_iff, dvd_iff]
--   intro ha hb
--   apply of_mul_dvd_mul_left
--   rw [gcd_mul_lcm]
--   obtain ⟨a₀, rfl⟩ := ha
--   obtain ⟨b₀, h⟩ := hb
--   rw [mul_comm (gcd _ _), mul_assoc]
--   apply mul_dvd_mul_left
--   rw [mul_comm]


--   sorry

-- def lcm_dvd_iff (a b k: α) : lcm a b ∣ k ↔ a ∣ k ∧ b ∣ k := by
--   by_cases hz:a = 0 ∨ b = 0
--   · rcases hz with rfl | rfl
--     simp
--     intro h
--     cases zero_dvd _ h
--     apply dvd_zero
--     simp
--     intro h
--     cases zero_dvd _ h
--     apply dvd_zero
--   · replace ⟨ha, hb⟩ := not_or.mp hz
--     clear hz
--     apply Iff.intro
--     · intro h
--       apply And.intro
--       apply dvd_trans _ h
--       apply dvd_lcm_left
--       apply dvd_trans _ h
--       clear h
--       apply dvd_lcm_right
--     · intro ⟨ha, hb⟩

--       sorry


-- def dvd_lcm_left (a b: α) : a ∣ lcm a b := by

--   sorry

-- protected def Associates.gcd : Associates α -> Associates α -> Associates α := by
--   refine Quotient.lift₂ (fun a b => Associates.mk (gcd a b)) ?_
--   intro a b c d h g
--   apply Associates.mk_rel
--   apply IsAssociated.gcd_congr
--   assumption
--   assumption
