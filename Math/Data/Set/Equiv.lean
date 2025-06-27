import Math.Data.Set.Defs
import Math.Logic.Equiv.Defs

def Surjection.range (f: α -> β) : α ↠ Set.range f where
  toFun x := {
    val := f x
    property := Set.mem_range'
  }
  surj' := by
    intro ⟨_, _,  rfl⟩
    exact ⟨_, rfl⟩

def Bijection.range (f: α ↪ β) : α ⇔ Set.range f where
  toSurjection := Surjection.range f
  inj' := by
    intro x y h
    exact f.inj (Subtype.mk.inj h)
