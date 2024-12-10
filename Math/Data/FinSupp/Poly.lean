import Math.Data.FinSupp.Basic
import Math.Data.Set.Like.Nat

def PolyWith (default: α) := FinSupp Nat α Nat default
def Poly α [Zero α] := PolyWith (0: α)

instance [DecidableEq α] (default: α) : DecidableEq (PolyWith default) := by
  intro a b
  cases a with | mk a aspec =>
  cases b with | mk b bspec =>
  apply @decidable_of_iff _ (a = b) _ (?_)
  apply Iff.intro
  intro h
  cases h
  congr
  apply Subsingleton.allEq
  intro h
  cases h
  rfl
  apply aspec.recOnSubsingleton (motive := fun _ => Decidable (a = b))
  intro aspec
  apply bspec.recOnSubsingleton (motive := fun _ => Decidable (a = b))
  intro bspec
  suffices a = b ↔ ∀x < max aspec.val bspec.val, a x = b x by
    rw [this]
    exact inferInstance
  apply Iff.intro
  intro h x _
  rw [h]
  intro h
  ext x
  cases aspec.property.spec x
  rw [h]
  apply Nat.lt_of_lt_of_le
  assumption
  apply Nat.le_max_left
  cases bspec.property.spec x
  rw [h]
  apply Nat.lt_of_lt_of_le
  assumption
  apply Nat.le_max_right
  rename_i h₀ g₀
  rw [h₀, g₀]

instance [DecidableEq α] [Zero α] : DecidableEq (Poly α) := inferInstanceAs (DecidableEq (PolyWith (0: α)))

def PolyWith.coeff {default: α} (p: PolyWith default) : Nat -> α := p.coeffs
def PolyWith.degree [DecidableEq α] {default: α} (p: PolyWith default) : Nat := by
  apply Quot.lift _ _ p.support
  · intro ⟨deg_limit, _, prf⟩
    have : ∃deg, ∀x, deg < x -> p.coeff x = default := by
      exists deg_limit
      intro x gt_lim
      cases prf x <;> rename_i h
      have := (Nat.lt_asymm h gt_lim)
      contradiction
      assumption
    have dec : ∀deg, (Decidable (∀x, deg < x -> p.coeff x = default)) := by
      intro deg
      apply decidable_of_iff (∀x < deg_limit, deg < x -> p.coeff x = default)
      apply Iff.intro
      · intro h x lt
        cases prf x <;> rename_i g
        apply h
        repeat assumption
      · intro h x _
        apply h
    exact Nat.findP this
  · intro ⟨alim, _, aprf⟩ ⟨blim, _, bprf⟩ ⟨⟩
    dsimp; congr

def PolyWith.ofList (coeffs: List α) (default: α) : PolyWith default := by
  apply FinSupp.mk _ (Squash.mk ⟨_, _⟩)
  exact (coeffs.getD · default)
  exact coeffs.length
  apply FinSupp.IsFiniteSupport.mk inferInstance
  intro x
  if x < coeffs.length then
    left; assumption
  else
    right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    rfl
    apply Nat.le_of_not_lt
    assumption

def Poly.ofList [Zero α] (coeffs: List α) : Poly α := PolyWith.ofList coeffs _
