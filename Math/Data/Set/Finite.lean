import Math.Data.Set.Basic
import Math.Order.Fin

namespace Set
-- a set is finite if there exists an embedding from elements of the set to Fin n for some n
class inductive IsFinite (a: Set α): Prop where
| intro (limit: Nat) : (a.Elem ↪ Fin limit) -> IsFinite a

def IsFinite.existsIso {a: Set α} (h: a.IsFinite) : ∃card, _root_.Nonempty (a.Elem ≃ Fin card) := by
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

instance IsFinite.ofFin (x: Set (Fin n)) : x.IsFinite := by
  apply IsFinite.intro n
  apply Embedding.mk Subtype.val
  intro ⟨x,_⟩ ⟨y, _⟩  eq
  cases eq
  rfl

def Fin.castLE_ne_addNat (x: Fin n) (y: Fin m) : x.castLE (Nat.le_add_left _ _) ≠ y.addNat n := by
  intro h
  cases x with | mk x xLt =>
  cases y with | mk y yLt =>
  unfold Fin.castLE Fin.addNat at h
  dsimp at h
  have := Fin.mk.inj h
  subst x
  exact Nat.not_lt_of_le (Nat.le_add_left _ _) xLt

instance [ha: IsFinite a] [hb: IsFinite b] : IsFinite (a ∪ b) := by
  obtain ⟨alim, aemb⟩ := ha
  obtain ⟨blim, bemb⟩ := hb
  apply IsFinite.intro (alim + blim)
  apply Embedding.mk
  case toFun =>
    intro x
    match Classical.propDecidable (x.val ∈ b) with
    | .isTrue h =>
      apply (bemb ⟨x.val, h⟩).castLE
      apply Nat.le_add_left
    | .isFalse h =>
      apply Fin.addNat
      apply aemb.toFun
      exists x.val
      cases x.property
      assumption
      contradiction
  case inj =>
    intro x y eq
    dsimp at eq
    split at eq <;> split at eq
    · have := bemb.inj (Fin.val_inj.mp (Fin.mk.inj eq))
      cases x; cases y
      congr
      cases this
      rfl
    · have := Fin.castLE_ne_addNat _ _ eq
      contradiction
    · have := Fin.castLE_ne_addNat _ _ eq.symm
      contradiction
    · have := aemb.inj <| Fin.val_inj.mp (Nat.add_right_cancel_iff.mp (Fin.mk.inj eq))
      cases x; cases y; cases this
      rfl

instance [ha: IsFinite a] : IsFinite (a ∩ b) := by
  obtain ⟨lim, emb⟩ := ha
  apply IsFinite.intro lim
  apply Embedding.mk
  case toFun =>
    intro x
    apply emb.toFun
    apply Subtype.mk x.val
    exact x.property.left
  case inj =>
    intro x y eq
    dsimp at eq
    cases x; cases y; cases (emb.inj eq)
    rfl

instance [hb: IsFinite b] : IsFinite (a ∩ b) := by
  obtain ⟨lim, emb⟩ := hb
  apply IsFinite.intro lim
  apply Embedding.mk
  case toFun =>
    intro x
    apply emb.toFun
    apply Subtype.mk x.val
    exact x.property.right
  case inj =>
    intro x y eq
    dsimp at eq
    cases x; cases y; cases (emb.inj eq)
    rfl

end Set
