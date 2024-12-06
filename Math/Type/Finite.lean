import Math.Type.Basic
import Math.Order.Fin
import Math.Data.Fin.Basic

class inductive IsFinite (α: Sort*): Prop where
| intro (limit: Nat) : (α ↪ Fin limit) -> IsFinite α

def IsFinite.existsEquiv (α: Sort*) [h: IsFinite α] : ∃card, _root_.Nonempty (α ≃ Fin card) := by
  obtain ⟨ limit, emb ⟩ := h
  induction limit with
  | zero =>
    exists 0
    apply Nonempty.intro
    apply Equiv.mk emb Fin.elim0
    intro x
    exact (emb x).elim0
    intro x
    exact x.elim0
  | succ limit ih =>
    if h:Function.Surjective emb then
      exists limit.succ
      have ⟨x, _⟩  := Equiv.ofBij ⟨emb.inj, h⟩
      exact ⟨x⟩
    else
      replace ⟨missing, not_in_range⟩ := Classical.not_forall.mp h
      replace not_in_range := not_exists.mp not_in_range
      apply ih
      apply Embedding.mk
      case toFun =>
        intro elem
        let out := emb elem
        if g:out ≤ missing then
          have : out < missing := lt_of_le_of_ne g (not_in_range _)
          apply Fin.mk out.val
          apply lt_of_lt_of_le
          exact this
          apply Nat.le_of_lt_succ
          exact missing.isLt
        else
          replace g := lt_of_not_le g
          apply out.pred
          intro h
          rw [h] at g
          contradiction
      case inj =>
        intro x y eq
        dsimp at eq
        split at eq <;> split at eq
        exact emb.inj (Fin.val_inj.mp (Fin.mk.inj eq))
        · rename_i h g
          unfold Fin.pred Fin.subNat at eq
          replace eq := Fin.mk.inj eq
          have : emb x < missing := (lt_of_le_of_ne h (not_in_range x))
          replace := Fin.lt_def.mp this
          rw [eq] at this
          replace this := Nat.succ_lt_succ this
          rw [←Nat.add_one, Nat.sub_add_cancel] at this
          have := lt_of_lt_of_le this (Nat.succ_le_of_lt (lt_of_not_le g))
          have := lt_irrefl this
          contradiction
          apply Nat.succ_le_of_lt
          apply Nat.zero_lt_of_lt
          apply lt_of_not_le
          assumption
        · rename_i g h
          unfold Fin.pred Fin.subNat at eq
          replace eq := Fin.mk.inj eq
          have : emb y < missing := (lt_of_le_of_ne h (not_in_range y))
          replace := Fin.lt_def.mp this
          rw [←eq] at this
          replace this := Nat.succ_lt_succ this
          rw [←Nat.add_one, Nat.sub_add_cancel] at this
          have := lt_of_lt_of_le this (Nat.succ_le_of_lt (lt_of_not_le g))
          have := lt_irrefl this
          contradiction
          apply Nat.succ_le_of_lt
          apply Nat.zero_lt_of_lt
          apply lt_of_not_le
          assumption
        · exact emb.inj (Fin.pred_inj.mp eq)

noncomputable
def IsFinite.card α [IsFinite α] : Nat :=
  Classical.choose (existsEquiv α)
noncomputable
def IsFinite.toEquiv α [IsFinite α] : α ≃ Fin (card α) :=
  Classical.choice (Classical.choose_spec (existsEquiv α))

instance IsFinite.ofFin : IsFinite (Fin n) := by
  apply IsFinite.intro n
  apply Embedding.mk id
  intro ⟨x,_⟩ ⟨y, _⟩ eq
  exact eq

instance IsFinite.ofSum {α β: Type*} [ha: IsFinite α] [hb: IsFinite β] : IsFinite (α ⊕ β) := by
  obtain ⟨alim, aemb⟩ := ha
  obtain ⟨blim, bemb⟩ := hb
  apply IsFinite.intro (alim + blim)
  apply Embedding.mk
  case toFun =>
    intro x
    match x with
    | .inr b =>
      apply Fin.castLE
      apply Nat.le_add_left
      apply bemb b
    | .inl a =>
      apply Fin.addNat
      apply aemb a
  case inj =>
    intro x y eq
    dsimp at eq
    split at eq <;> split at eq
    · have := bemb.inj (Fin.val_inj.mp (Fin.mk.inj eq))
      congr
    · have := Fin.castLE_ne_addNat _ _ eq
      contradiction
    · have := Fin.castLE_ne_addNat _ _ eq.symm
      contradiction
    · have := aemb.inj <| Fin.val_inj.mp (Nat.add_right_cancel_iff.mp (Fin.mk.inj eq))
      congr

instance IsFinite.ofPSum {α β: Sort*} [ha: IsFinite α] [hb: IsFinite β] : IsFinite (α ⊕' β) := by
  obtain ⟨alim, aemb⟩ := ha
  obtain ⟨blim, bemb⟩ := hb
  apply IsFinite.intro (alim + blim)
  apply Embedding.mk
  case toFun =>
    intro x
    match x with
    | .inr b =>
      apply Fin.castLE
      apply Nat.le_add_left
      apply bemb b
    | .inl a =>
      apply Fin.addNat
      apply aemb a
  case inj =>
    intro x y eq
    dsimp at eq
    split at eq <;> split at eq
    · have := bemb.inj (Fin.val_inj.mp (Fin.mk.inj eq))
      congr
    · have := Fin.castLE_ne_addNat _ _ eq
      contradiction
    · have := Fin.castLE_ne_addNat _ _ eq.symm
      contradiction
    · have := aemb.inj <| Fin.val_inj.mp (Nat.add_right_cancel_iff.mp (Fin.mk.inj eq))
      congr

instance IsFinite.ofProd {α β: Type*} [ha: IsFinite α] [hb: IsFinite β] : IsFinite (α × β) := by
  obtain ⟨alim, aemb⟩ := ha
  obtain ⟨blim, bemb⟩ := hb
  apply IsFinite.intro (alim * blim)
  apply Embedding.mk
  case toFun =>
    intro x
    apply Fin.pair
    exact aemb x.1
    exact bemb x.2
  case inj =>
    intro x y eq
    dsimp at eq
    cases x; cases y
    have ⟨aeq, beq⟩   := Fin.pair.inj eq
    congr
    exact aemb.inj aeq
    exact bemb.inj beq

instance IsFinite.ofPProd {α β: Sort*} [ha: IsFinite α] [hb: IsFinite β] : IsFinite (α ×' β) := by
  obtain ⟨alim, aemb⟩ := ha
  obtain ⟨blim, bemb⟩ := hb
  apply IsFinite.intro (alim * blim)
  apply Embedding.mk
  case toFun =>
    intro x
    apply Fin.pair
    exact aemb x.1
    exact bemb x.2
  case inj =>
    intro x y eq
    dsimp at eq
    cases x; cases y
    have ⟨aeq, beq⟩   := Fin.pair.inj eq
    congr
    exact aemb.inj aeq
    exact bemb.inj beq

instance IsFinite.ofSigma {α: Type*} {β: α -> Type*} [ha: IsFinite α] [hb: ∀x, IsFinite (β x)] : IsFinite ((x: α) × β x) := by
  have equiv := toEquiv α
  have βequiv : {x: α} -> β x ≃ Fin (card (β x)) := fun {x} => toEquiv _
  apply IsFinite.intro <| Fin.sum fun x => card (β (equiv.invFun x))
  apply Embedding.mk
  case toFun =>
    intro ⟨a, b⟩
    apply Fin.mk _ _
    apply _ + Fin.sum_to (equiv a) fun x => card (β (equiv.invFun x))
    exact (βequiv b).val
    simp
    rw [←Nat.sub_add_cancel (n := Fin.sum _) (m := (βequiv b).val), Nat.add_comm]
    apply Nat.add_lt_add_right
    show _ < _ - (βequiv.toFun b).val
    apply Nat.lt_sub_of_add_lt
    have := Fin.sum_to_lt_sum (x := equiv a) (f := fun x => card (β (equiv.invFun x))) (y := by
      dsimp
      show Fin (card (β (equiv.invFun (equiv.toFun _))))
      apply Fin.mk
      rw [equiv.leftInv]
      exact (βequiv.toFun b).isLt)
    dsimp at this
    apply this
    apply Nat.le_trans
    apply Nat.le_of_lt
    apply Fin.isLt
    have : card (β (equiv.invFun (equiv.toFun _))) ≤ _ := Fin.le_sum (equiv a) (fun x => card (β (equiv.invFun x)))
    rw [equiv.leftInv] at this
    assumption
  case inj =>
    dsimp
    intro ⟨xa, xb⟩ ⟨ya, yb⟩ eq
    dsimp at eq
    replace eq := Fin.mk.inj eq
    have ⟨xa_eq_ya, xb_eq_yb⟩ := Fin.lt_add_sum_to_inj (fun x => card (β (equiv.invFun x)))
      (equiv xa) (equiv ya) (by
        apply Fin.mk (βequiv xb).val
        simp [DFunLike.coe, IsEquivLike.coe]
        have := equiv.leftInv xa
        apply Nat.lt_of_lt_of_le
        apply Fin.isLt
        apply Nat.le_of_eq
        congr
        symm; assumption) (by
        apply Fin.mk (βequiv yb).val
        simp [DFunLike.coe, IsEquivLike.coe]
        have := equiv.leftInv ya
        apply Nat.lt_of_lt_of_le
        apply Fin.isLt
        apply Nat.le_of_eq
        congr
        symm; assumption) eq
    clear eq
    cases equiv.toFun_inj xa_eq_ya
    congr
    simp at xb_eq_yb
    replace xb_eq_yb := Fin.val_inj.mp xb_eq_yb
    cases βequiv.toFun_inj xb_eq_yb
    rfl

instance IsFinite.ofPSigma {α: Sort*} {β: α -> Sort*} [ha: IsFinite α] [hb: ∀x, IsFinite (β x)] : IsFinite ((x: α) ×' β x) := by
  have equiv := toEquiv α
  have βequiv : {x: α} -> β x ≃ Fin (card (β x)) := fun {x} => toEquiv _
  apply IsFinite.intro <| Fin.sum fun x => card (β (equiv.invFun x))
  apply Embedding.mk
  case toFun =>
    intro ⟨a, b⟩
    apply Fin.mk _ _
    apply _ + Fin.sum_to (equiv a) fun x => card (β (equiv.invFun x))
    exact (βequiv b).val
    simp
    rw [←Nat.sub_add_cancel (n := Fin.sum _) (m := (βequiv b).val), Nat.add_comm]
    apply Nat.add_lt_add_right
    show _ < _ - (βequiv.toFun b).val
    apply Nat.lt_sub_of_add_lt
    have := Fin.sum_to_lt_sum (x := equiv a) (f := fun x => card (β (equiv.invFun x))) (y := by
      dsimp
      show Fin (card (β (equiv.invFun (equiv.toFun _))))
      apply Fin.mk
      rw [equiv.leftInv]
      exact (βequiv.toFun b).isLt)
    dsimp at this
    apply this
    apply Nat.le_trans
    apply Nat.le_of_lt
    apply Fin.isLt
    have : card (β (equiv.invFun (equiv.toFun _))) ≤ _ := Fin.le_sum (equiv a) (fun x => card (β (equiv.invFun x)))
    rw [equiv.leftInv] at this
    assumption
  case inj =>
    dsimp
    intro ⟨xa, xb⟩ ⟨ya, yb⟩ eq
    dsimp at eq
    replace eq := Fin.mk.inj eq
    have ⟨xa_eq_ya, xb_eq_yb⟩ := Fin.lt_add_sum_to_inj (fun x => card (β (equiv.invFun x)))
      (equiv xa) (equiv ya) (by
        apply Fin.mk (βequiv xb).val
        simp [DFunLike.coe, IsEquivLike.coe]
        have := equiv.leftInv xa
        apply Nat.lt_of_lt_of_le
        apply Fin.isLt
        apply Nat.le_of_eq
        congr
        symm; assumption) (by
        apply Fin.mk (βequiv yb).val
        simp [DFunLike.coe, IsEquivLike.coe]
        have := equiv.leftInv ya
        apply Nat.lt_of_lt_of_le
        apply Fin.isLt
        apply Nat.le_of_eq
        congr
        symm; assumption) eq
    clear eq
    cases equiv.toFun_inj xa_eq_ya
    congr
    simp at xb_eq_yb
    replace xb_eq_yb := Fin.val_inj.mp xb_eq_yb
    cases βequiv.toFun_inj xb_eq_yb
    rfl
