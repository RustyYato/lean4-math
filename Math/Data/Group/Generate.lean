import Math.Data.Group.Basic

inductive Group.GenerateFrom (src: Group) (s: Set src.ty) : src.ty -> Prop where
| one : GenerateFrom src s 1
| of : x ∈ s -> GenerateFrom src s x
| mul : GenerateFrom src s x -> GenerateFrom src s y -> GenerateFrom src s (x * y)
| inv : GenerateFrom src s x -> GenerateFrom src s x⁻¹

def Group.Generate (src: Group) (s: Set src.ty) : Group where
  ty := { x: src.ty // Group.GenerateFrom src s x }
  one' := ⟨1, Group.GenerateFrom.one⟩
  mul' a b := ⟨_, Group.GenerateFrom.mul a.property b.property⟩
  inv' a := ⟨_, Group.GenerateFrom.inv a.property⟩
  one_mul' := by
    intro ⟨a, aprop⟩
    dsimp; congr; rw [one_mul]
  mul_assoc' := by
    intro ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩
    dsimp; congr 1
    rw [mul_assoc]
  inv_mul' := by
    intro ⟨a, aprop⟩
    dsimp; congr; rw [inv_mul_cancel]

def Group.Generate.spec (a b: Group) (s₀: Set a.ty) (s₁: Set b.ty)
  (h: Isomorphsism a b) (g: ∀x, x ∈ s₀ ↔ h x ∈ s₁) :
  Isomorphsism (Group.Generate a s₀) (Group.Generate b s₁) where
  toEquiv := Subtype.congrEquiv h.toEquiv <| by
    intro x
    apply Iff.intro
    intro g
    show b.GenerateFrom s₁ (h.toFun x)
    induction g
    show b.GenerateFrom _ (h 1)
    rw [h.resp_one]
    apply GenerateFrom.one
    apply GenerateFrom.of
    apply (g _).mp
    assumption
    rw [h.resp_mul']
    apply GenerateFrom.mul <;> assumption
    rw [h.resp_inv']
    apply GenerateFrom.inv <;> assumption
    intro g
    rw [←h.leftInv x]
    generalize hx:h.toFun x = x
    rw [hx] at g; clear hx
    induction g
    show a.GenerateFrom _ (h.symm 1)
    rw [h.symm.resp_one]
    apply GenerateFrom.one
    apply GenerateFrom.of
    apply (g _).mpr
    rename_i x _
    show h.toFun _ ∈ _
    rw [h.rightInv x]
    assumption
    show a.GenerateFrom _ (h.symm _)
    rw [h.symm.resp_mul]
    apply GenerateFrom.mul <;> assumption
    show a.GenerateFrom _ (h.symm _)
    rw [h.symm.resp_inv]
    apply GenerateFrom.inv <;> assumption
  resp_mul' := by
    intro ⟨a, _⟩ ⟨b, _⟩
    show Subtype.mk _ _ = ⟨_, _⟩
    congr
    show h _ = _
    rw [h.resp_mul]
    rfl
  resp_inv' := by
    intro x
    show Subtype.mk _ _ = ⟨_, _⟩
    congr
    show h _ = _
    rw [h.resp_inv]
    rfl
