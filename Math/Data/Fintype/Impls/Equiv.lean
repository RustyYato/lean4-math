import Math.Data.Nat.Factorial
import Math.Data.Fintype.Defs
import Math.Data.Nat.Basic

namespace Fintype

private def mod_m (i: Fin ((n + 1) !)) : Fin (n + 1) := Fin.ofNat' (n + 1) i

private def div_m (i: Fin ((n + 1) !)) : Fin (n !) where
  val := i.val / (n + 1)
  isLt := by
    have hi := i.isLt
    simp [npr] at *
    rwa [Nat.div_lt_iff_lt_mul, Nat.mul_comm]
    apply Nat.zero_lt_succ

private def decode (i: Fin (n !)) : Fin n ≃ Fin n :=
  match n with
  | 0 => Equiv.empty
  | _ + 1 =>
    have f := decode (div_m i)
    Equiv.congrEquiv (Equiv.fin_equiv_option _).symm (Equiv.fin_erase (mod_m i)).symm (Equiv.congrOption f)

private def encode (f: Fin n ≃ Fin n) : Fin (n !) :=
  match n with
  | 0 => ⟨0, Nat.zero_lt_succ _⟩
  | n + 1 =>
    let f₀' := Equiv.congrEquiv (Equiv.fin_equiv_option _) (Equiv.fin_erase (f (Fin.last _))) f
    have f₀'_none : f₀' .none = .none := by simp [f₀']
    have f₀'_some (x: Fin n) : (f₀' x ).isSome := by
      rw [Option.isSome_iff_ne_none]
      intro h
      rw [←f₀'_none, f₀'.inj.eq_iff] at h
      contradiction
    have symm_f₀'_some (x: Fin n) : (f₀'.symm x ).isSome := by
      rw [Option.isSome_iff_ne_none]
      intro h
      replace h := Equiv.eq_symm_of_coe_eq _ h
      simp at h
      rw [f₀'_none] at h
      contradiction
    have f₀ : Fin n ≃ Fin n := {
      toFun x := (f₀' x).get (f₀'_some _)
      invFun x := (f₀'.symm x).get (symm_f₀'_some _)
      leftInv x := by simp
      rightInv x := by simp
    }
    have f₁ := f (Fin.last _)
    {
      val := (n + 1) * encode f₀ + f₁.val
      isLt := by
        rw [fact_succ]
        rw (occs := [2]) [Nat.mul_comm (n + 1), ←Nat.sub_add_cancel (n := n !) (m := 1)]
        rw [Nat.succ_mul _ (n + 1)]
        apply Nat.add_lt_add_of_le_of_lt
        · rw [Nat.mul_comm]
          apply Nat.mul_le_mul
          apply (Nat.le_pred_iff_lt _).mpr
          simp
          apply fact_pos
          apply Nat.le_refl
        · apply Fin.isLt
        · rw [Nat.succ_le]
          apply fact_pos
    }

def decode_inj : Function.Injective (decode (n := n)) := by
  intro x y h
  induction n with
  | zero => apply Subsingleton.allEq (α := Fin 1)
  | succ n ih =>
    suffices mod_m x = mod_m y by
      simp [decode, this, Equiv.congrOption.inj.eq_iff] at h
      ext
      rw [←Nat.div_add_mod x.val (n + 1), ←Nat.div_add_mod y.val (n + 1)]
      show (n + 1) * (div_m x).val + (mod_m x).val = (n + 1) * (div_m y).val + (mod_m y).val
      rw [this, ih h]
    simp [decode] at h
    simpa [Equiv.symm_apply_fin_erase_none] using Equiv.congr h .none

def encode_inj : Function.Injective (encode (n := n)) := by
  induction n with
  | zero =>
    intro x y h
    apply Subsingleton.allEq
  | succ n ih =>
    intro x y h
    unfold encode at h
    simp at h
    replace ⟨h, h₀⟩ := Nat.of_mul_add_lt (by simp) (by simp) h
    simp [Fin.val_inj, ih.eq_iff] at h
    obtain ⟨h₁, h₂⟩ := h
    replace h₁ := congrFun h₁
    replace h₂ := congrFun h₂
    rw [Fin.val_inj] at h₀
    simp [h₀, Option.get_inj, ((Equiv.fin_erase _).inj.eq_iff)] at h₁
    clear h₂
    ext i
    cases i using Fin.lastCases
    rw [h₀]
    rw [h₁]

def encode_decode (i: Fin (n !)) : encode (decode i) = i := by
  induction n with
  | zero => apply Subsingleton.allEq (α := Fin 1)
  | succ n ih =>
    rw [←Fin.val_inj, ←Nat.div_add_mod i.val (n + 1)]
    unfold decode encode
    simp; congr
    simp [Equiv.symm_apply_fin_erase_none]
    show (Fintype.encode (Fintype.decode _)).val = _
    rw [ih]
    rfl

def decode_encode (f: Fin n ≃ Fin n)  : decode (encode f) = f := by
  apply encode_inj
  rw [encode_decode]

instance [DecidableEq α] [DecidableEq β] [fα: Fintype α] [fβ: Fintype β] : Fintype (α ≃ β) :=
  if h:card α = card β then
    {
    card_thunk := Thunk.mk fun _ => ((card α) !)
    toRepr :=
        fα.toRepr.bind fun rα: Repr (card α) _ =>
        fβ.toRepr.map (β := Repr ((card α) !) _) fun rβ: Repr (card β) _ =>
        {
          encode := Thunk.mk fun _ => .none
          decode x := Equiv.congrEquiv rα.toEquiv rβ.toEquiv ((Fintype.decode x).trans (Equiv.fin h))
          bij := by
            apply And.intro
            · intro x y h
              simp at h
              exact decode_inj h
            · intro f
              exists encode <| (Equiv.congrEquiv rα.toEquiv.symm rβ.toEquiv.symm f).trans (Equiv.fin h.symm)
              ext x; simp [decode_encode]
        }
    }
  else
    have : IsEmpty (α ≃ β) := { elim f := h (Fintype.card_eq_of_equiv f) }
    inferInstance

end Fintype
