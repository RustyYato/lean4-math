import Math.Data.Cardinal.Order
import Math.Data.Fin.Basic
import Math.Data.Fintype.Card
import Math.Algebra.Semiring.Char
import Math.Algebra.Algebra.Defs

namespace Cardinal

instance : SMul ℕ Cardinal where
  smul n x := n * x

instance : NatCast Cardinal where
  natCast n := OfNat.ofNat n

def natCast_add (n m: ℕ) : ((n + m: ℕ): Cardinal) = n + m := by
  apply sound
  apply Equiv.trans
  apply Equiv.ulift
  apply flip Equiv.trans; symm
  apply Equiv.congrSum
  apply Equiv.ulift
  apply Equiv.ulift
  exact Equiv.finSum.symm

def natCast_mul (n m: ℕ) : ((n * m: ℕ): Cardinal) = n * m := by
  apply sound
  apply Equiv.trans
  apply Equiv.ulift
  apply flip Equiv.trans; symm
  apply Equiv.congrProd
  apply Equiv.ulift
  apply Equiv.ulift
  exact Equiv.finProd.symm

def natCast_pow (n m: ℕ) : ((n ^ m: ℕ): Cardinal) = (n: Cardinal) ^ (m: Cardinal) := by
  have := Fintype.equivFin (Fin m -> Fin n)
  simp [Fintype.card_function, Fintype.card_fin] at this
  induction this with | _ this =>
  apply sound
  apply Equiv.trans
  apply Equiv.ulift
  apply flip Equiv.trans; symm
  apply Equiv.congrFunction
  apply Equiv.ulift
  apply Equiv.ulift
  symm; assumption

instance : IsAddCommMagma Cardinal where
  add_comm (a b: Cardinal) := by
    cases a, b with | mk a b =>
    apply sound
    apply Equiv.commSum

instance : IsCommMagma Cardinal where
  mul_comm (a b: Cardinal) := by
    cases a, b with | mk a b =>
    apply sound
    apply Equiv.commProd

instance : IsAddZeroClass Cardinal := by
  apply IsAddZeroClass.ofAddCommMagma
  intro a
  cases a with | mk a =>
  simp [HAdd.hAdd, Add.add]
  show (ulift (ofNat _)).add _ = _
  rw [lift_add]
  apply sound
  apply Equiv.trans
  apply Equiv.ulift
  apply Equiv.mk _ _ _ _
  intro h
  match h with
  | .inl h => exact h.elim0
  | .inr h => exact h
  exact .inr
  intro h
  cases h <;> rename_i h
  exact h.elim0
  rfl
  intro
  rfl

instance : IsMulZeroClass Cardinal := by
  apply IsMulZeroClass.ofCommMagma
  intro a
  cases a with | mk a =>
  show (ulift (ofNat _)).mul _ = _
  rw [lift_mul]
  apply sound
  apply flip Equiv.trans; symm
  apply Equiv.ulift
  apply Equiv.mk _ _ _ _
  intro ⟨h, _⟩
  exact h
  intro h
  exact h.elim0
  intro ⟨h, _⟩
  exact h.elim0
  intro h
  exact h.elim0

instance : IsMulOneClass Cardinal := by
  apply IsMulOneClass.ofCommMagma
  intro a
  cases a with | mk a =>
  show (ulift (ofNat _)).mul _ = _
  rw [lift_mul]
  apply sound
  apply Equiv.mk _ _ _ _
  intro ⟨_, x⟩
  exact x
  intro x
  exact ⟨0, x⟩
  intro ⟨_, x⟩
  dsimp
  congr
  apply Subsingleton.allEq
  intro
  rfl

instance : IsLeftDistrib Cardinal where
  mul_add k a b := by
    cases a, b, k with | mk A B K =>
    apply sound
    apply Equiv.mk _ _ _ _
    intro ⟨k, x⟩
    match x with
    | .inl x => exact .inl ⟨k, x⟩
    | .inr x => exact .inr ⟨k, x⟩
    intro x
    match x with
    | .inl ⟨k, x⟩ => exact ⟨k, .inl x⟩
    | .inr ⟨k, x⟩ => exact ⟨k, .inr x⟩
    intro ⟨k, x⟩
    cases x <;> rfl
    intro x
    cases x <;> rfl

instance : IsAddMonoid Cardinal where
  add_assoc a b c := by
    cases a, b, c with | mk A B C =>
    apply sound
    apply Equiv.mk _ _ _ _
    intro h
    match h with
    | .inl (.inl x) => exact .inl x
    | .inl (.inr x) => exact .inr <| .inl x
    | .inr x => exact .inr <| .inr x
    intro h
    match h with
    | .inl x => exact .inl <| .inl x
    | .inr (.inl x) => exact .inl <| .inr x
    | .inr (.inr x) => exact .inr x
    intro x
    rcases x with (_ | _) | _ <;> rfl
    intro x
    rcases x with _ | _ | _ <;> rfl
  zero_nsmul := by
    intro x
    show 0 * _ = 0
    rw [zero_mul x]
  succ_nsmul n a := by
    show (n + 1: ℕ) * a = _
    erw [natCast_add, add_mul, one_mul]
    rfl

instance : IsMonoid Cardinal where
  mul_assoc a b c := by
    cases a, b, c with | mk A B C =>
    apply sound
    apply Equiv.mk _ _ _ _
    intro ⟨⟨a, b⟩, c⟩
    exact ⟨a, b, c⟩
    intro ⟨a, b, c⟩
    exact ⟨⟨a, b⟩, c⟩
    intro ⟨⟨a, b⟩, c⟩
    rfl
    intro ⟨a, b, c⟩
    rfl
  npow_zero a := by
    cases a with | mk A =>
    apply sound
    apply Equiv.mk _ _ _ _
    intro h
    exact ⟨0⟩
    intro x y
    exact y.down.elim0
    intro x
    apply Subsingleton.allEq
    intro x
    apply Subsingleton.allEq
  npow_succ n a := by
    cases a with | mk A =>
    apply sound
    apply Equiv.trans
    apply Equiv.congrFunction
    apply Equiv.ulift
    rfl
    apply flip Equiv.trans; symm
    apply Equiv.congrProd
    apply Equiv.congrFunction (Equiv.ulift _) (by rfl)
    rfl
    apply Equiv.mk _ _ _ _
    intro f
    constructor
    intro x
    exact f x.succ
    exact f 0
    intro ⟨f, a⟩ x
    if h:x = 0 then
      exact a
    else
      exact f (x.pred h)
    intro f
    funext x
    dsimp
    split <;> rename_i h
    rw [h]
    rw [Fin.succ_pred]
    intro ⟨f, a⟩
    congr

instance : IsAddMonoidWithOne Cardinal where
  natCast_zero := rfl
  natCast_succ x := natCast_add x 1

instance : IsSemiring Cardinal where
  npow_succ := npow_succ
  npow_zero := npow_zero

def natCast_strictmonotone : StrictMonotone (fun n: ℕ => (n: Cardinal)) := by
  intro n m h
  simp
  rw [←not_le]
  intro ⟨h⟩
  replace h := Equiv.congrEmbed (Equiv.ulift _) (Equiv.ulift _) h
  have := Fin.le_of_emebd h
  rw [←not_lt] at this
  apply this
  assumption

def ord_natCast.{u} (n: ℕ) : ord.{u} n = n := by
  rcases lt_trichotomy (n: Ordinal) (ord n) with h | h | h
  · have := lt_irrefl (ord_is_min n n h)
    contradiction
  · symm; assumption
  · exfalso
    induction n using Nat.strongRecOn with
    | _ n ih =>
    rw [Ordinal.lt_natCast] at h
    obtain ⟨m, hm, eq⟩ := h
    apply ih m hm
    rw [←eq, ←not_le, ←map_le ord, not_le]
    apply natCast_strictmonotone
    assumption

instance : HasChar Cardinal 0 := HasChar.of_ring_emb {
  algebraMap (R := ℕ) (α := Cardinal) with
  inj' x y h := by
    replace h : Nat.cast x = Nat.cast y := h
    obtain ⟨h⟩ := exact h
    replace h := Equiv.congrEquiv (Equiv.ulift _) (Equiv.ulift _) h
    exact Fin.eq_of_equiv h
}

end Cardinal
