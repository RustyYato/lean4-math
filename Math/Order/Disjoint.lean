import Math.Order.Defs

variable [LE α] [LT α] [Bot α] {a b: α} [IsLawfulBot α]

def Disjoint (a b: α) : Prop := ∀x: α, x ≤ a -> x ≤ b -> x ≤ ⊥

@[simp]
def disjoint_of_subsingleton [IsPreOrder α] [Subsingleton α] : Disjoint a b :=
  fun x _ _ ↦ le_of_eq (Subsingleton.elim x ⊥)

def disjoint_comm : Disjoint a b ↔ Disjoint b a := by
  unfold Disjoint
  apply Iff.intro
  intro h x hb ha
  apply h <;> assumption
  intro h x hb ha
  apply h <;> assumption

instance : Relation.IsSymmetric (Disjoint (α := α)) where
  symm := by simp [disjoint_comm]

@[simp] def disjoint_bot_left : Disjoint ⊥ a := fun _ hbot _ => hbot
@[simp] def disjoint_bot_right : Disjoint a ⊥ := fun _ _ hbot => hbot

@[simp]
def disjoint_self [IsPartialOrder α] : Disjoint a a ↔ a = ⊥ := by
  apply Iff.intro
  intro h
  apply le_antisymm
  apply h <;> rfl
  apply bot_le
  intro h
  rw [h]
  simp

def Disjoint.ne [IsPartialOrder α] (ha : a ≠ ⊥) (hab : Disjoint a b) : a ≠ b :=
  fun h ↦ ha <| disjoint_self.1 <| by rwa [← h] at hab

def Disjoint.eq_bot_of_le [IsPartialOrder α] (hab : Disjoint a b) (h : a ≤ b) : a = ⊥ := by
  symm; apply le_antisymm; apply bot_le
  apply hab
  rfl; assumption

def Disjoint.eq_bot_of_ge [IsPartialOrder α] (hab : Disjoint a b) (h : b ≤ a): b = ⊥ := by
  symm; apply le_antisymm; apply bot_le
  apply hab
  assumption; rfl
