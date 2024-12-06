import Math.Type.Basic
import Math.Order.Fin
import Math.Data.Fin.Basic

class inductive IsFinite (α: Sort*): Prop where
| intro (limit: Nat) : (α ↪ Fin limit) -> IsFinite α

def Type.IsFinite.existsIso (α: Sort*) [h: IsFinite α] : ∃card, _root_.Nonempty (α ≃ Fin card) := by
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
