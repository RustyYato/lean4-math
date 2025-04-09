import Math.Algebra.Monoid.Con
import Math.Algebra.Con.Lattice
import Math.Algebra.Monoid.SetLike.Basic
import Math.Algebra.Monoid.Impls.Prod

namespace Localization

variable {M: Type*} [MonoidOps M] [IsMonoid M] [IsCommMagma M]
   (S: Submonoid M)

-- the smallest congruence class such that one is related to the formal expression (a / a)
def con : MulCon (M × S) :=
  ⨅ (Set.mk fun r => ∀a: S, r 1 (a.val, a))

-- a more direct definition of the same congruence class as `con`
def con' : MulCon (M × S) where
  r := (fun a b : M × S => ∃ c : S, c.val * (b.2.val * a.1) = c.val * (a.2.val * b.1))
  iseqv := {
    refl _ := by exists 1
    symm h := by
      obtain ⟨c, h⟩ := h
      exists c
      symm; assumption
    trans := by
      intro x y z ⟨a, h⟩ ⟨b, g⟩
      exists a * b * y.snd
      show a.val * b.val * y.snd.val * _ = a.val * b.val * y.snd.val * _
      rw [mul_comm a.val, mul_assoc b.val, mul_assoc _ (_ * _), mul_left_comm _ z.snd.val,
        mul_assoc a.val, h, mul_left_comm a.val,  mul_left_comm z.snd.val, ← mul_left_comm a.val,
        mul_left_comm, mul_left_comm b.val, g]
      ac_rfl
  }
  resp_mul := by
    intro a b c d ⟨x, h⟩ ⟨y, g⟩
    exists x * y
    show x.val * y.val * ((c.snd.val * d.snd.val) * (a.fst * b.fst)) =
      x.val * y.val * ((a.snd.val * b.snd.val) * (c.fst * d.fst))
    rw [show x.val * y.val * ((c.snd.val * d.snd.val) * (a.fst * b.fst)) =
      (x.val * (c.snd.val * a.fst)) * (y.val * (d.snd.val * b.fst)) by ac_rfl]
    rw [h, g]; ac_rfl

def con'_one (a: S) : con' S 1 (a.val, a) := by
  exists 1
  show 1 * (a.val * 1) = 1 * (1 * a.val)
  simp

def con_eq_con' : con S = con' S := by
  apply le_antisymm
  apply sInf_le
  intro s
  apply con'_one
  apply le_sInf
  intro m hm; simp at hm
  intro ⟨a₀, a₁⟩ ⟨b₀, b₁⟩ ⟨c, h⟩
  simp at h
  rw [←one_mul (a₀, a₁), ←one_mul (b₀, b₁)]
  apply m.trans
  apply resp_mul m
  apply hm (c * b₁)
  rfl
  apply flip m.trans
  apply m.symm
  apply resp_mul m
  apply hm (c * a₁)
  rfl
  show m (c.val * b₁.val * a₀, c * b₁ * a₁) (c.val * a₁.val * b₀, c * a₁ * b₁)
  rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, h, mul_comm b₁ a₁]

def con_iff_exists {x y : M × S} : con S x y ↔ ∃ c : S, c.val * (y.2.val * x.1) = c.val * (x.2.val * y.1) := by rw [con_eq_con']; rfl

def _root_.Localization := IsCon.Quotient (con S)

instance : MonoidOps (Localization S) := inferInstanceAs (MonoidOps (IsCon.Quotient (con S)))
instance : IsMonoid (Localization S) := inferInstanceAs (IsMonoid (IsCon.Quotient (con S)))
instance : IsCommMagma (Localization S) := inferInstanceAs (IsCommMagma (IsCon.Quotient (con S)))

def mkHom : (M × S) →* Localization S := IsMulCon.mkQuot (con S)
def mk (a: M) (b: S) : Localization S := mkHom S (a, b)
def mk_one : 1 = mk S 1 1 := rfl
def mk_mul (a₀ a₁: M) (b₀ b₁: S) : mk S a₀ b₀ * mk S a₁ b₁ = mk S (a₀ * a₁) (b₀ * b₁) := rfl
def mk_npow (a: M) (b: S) (n: ℕ) : (mk S a b) ^ n = mk S (a ^ n) (b ^ n) := rfl

def mk_eq_mkHom (a: M) (b: S) : mk S a b = mkHom S (a, b) := rfl

@[induction_eliminator]
def ind {motive: Localization S -> Prop} (mk: ∀a b, motive (mk S a b)) : ∀l, motive l := by
  intro l
  induction l using Quot.ind
  apply mk

def lift : (f: M -> S -> α) -> (resp: ∀(a₀ a₁: M) (b₀ b₁: S), con S (a₀, b₀) (a₁, b₁) -> f a₀ b₀ = f a₁ b₁) -> Localization S -> α := by
  intro f h
  refine Quotient.lift ?_ ?_
  intro x; exact f x.1 x.2
  intro a b g; apply h
  assumption

def lift₂ : (f: M -> S -> M -> S -> α) -> (resp: ∀(a₀ a₁ a₂ a₃: M) (b₀ b₁ b₂ b₃: S), con S (a₀, b₀) (a₁, b₁) -> con S (a₂, b₂) (a₃, b₃) -> f a₀ b₀ a₂ b₂ = f a₁ b₁ a₃ b₃) -> Localization S -> Localization S -> α := by
  intro f h
  refine Quotient.lift₂ ?_ ?_
  intro x y; exact f x.1 x.2 y.1 y.2
  intros
  apply h
  assumption
  assumption

def hrec {motive: Localization S -> Sort*} (mk: ∀a b, motive (mk S a b)) (resp: ∀(a₀ a₁: M) (b₀ b₁: S), con S (a₀, b₀) (a₁, b₁) -> HEq (mk a₀ b₀) (mk a₁ b₁)) : ∀l, motive l := by
  intro l
  refine Quotient.hrecOn (motive := motive) l ?_ ?_
  intro
  apply mk
  intro _ _
  apply resp

def sound : con S (a₀, b₀) (a₁, b₁) -> mk S a₀ b₀ = mk S a₁ b₁ := Quotient.sound
def exact : mk S a₀ b₀ = mk S a₁ b₁ -> con S (a₀, b₀) (a₁, b₁) := Quotient.exact
def rel_iff : mk S a₀ b₀ = mk S a₁ b₁ ↔ con S (a₀, b₀) (a₁, b₁) := ⟨exact S, sound S⟩

def mk_self (a: S) : mk S a.val a = 1 := by
  symm; apply sound
  rw [con_iff_exists]
  apply con'_one

def mk_mul_cancel_left (a: M) (b k: S) : mk S (k.val * a) (k * b) = mk S a b := by
  rw [←mk_mul, mk_self, one_mul]
def mk_mul_cancel_right (a: M) (b k: S) : mk S (a * k.val) (b * k) = mk S a b := by
  rw [←mk_mul, mk_self, mul_one]

end Localization
