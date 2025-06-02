import Math.Type.Notation
import Math.Logic.Basic

protected structure Array.Vector (α: Type*) (n: ℕ) where
  ofArray ::
  toArray : Array α
  size_eq: toArray.size = n

namespace Array.Vector

def cast (h: n = m) : Array.Vector α n -> Array.Vector α m
| .ofArray array size_eq => .ofArray array (h ▸ size_eq)

def nil : Array.Vector α 0 where
  toArray := #[]
  size_eq := rfl

def push (v: Array.Vector α n) (x: α) : Array.Vector α (n + 1) where
  toArray := v.toArray.push x
  size_eq := by rw [Array.size_push, v.size_eq]

instance : GetElem (Array.Vector α n) ℕ α (fun _ i => i < n) where
  getElem a i h := a.toArray[i]'(by rwa [a.size_eq])

@[ext]
def ext (a b: Array.Vector α n) (h: ∀x: Fin n, a[x] = b[x]) : a = b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  congr
  ext
  rw [ha, hb]
  apply h ⟨_, _⟩
  rwa [ha] at *

def last (v: Array.Vector α (n + 1)) : α := v[Fin.last n]
def pop (v: Array.Vector α n) : Array.Vector α (n - 1) where
  toArray := v.toArray.pop
  size_eq := by rw [Array.size_pop, v.size_eq]

@[simp]
def getElem_mk (array: Array α) (h: array.size = n) (x: ℕ) (hx: x < n) : (Array.Vector.ofArray array h)[x] = array[x] := by rfl

@[simp]
def push_getElem_last (v: Array.Vector α n) (x: α) : (v.push x)[n] = x := by
  simp [push]
  rw [Array.getElem_push, dif_neg]
  rw [v.size_eq]
  omega

@[simp]
def push_getElem_castSucc (v: Array.Vector α n) (x: α) (i: ℕ) (h: i < n) : (v.push x)[i] = v[i] := by
  simp [push]
  rw [Array.getElem_push, dif_pos]
  rfl

@[simp]
def getElem_pop (v: Array.Vector α n) (i: ℕ) (h: i < n - 1) : v.pop[i] = v[i] := by
  simp [pop]
  rfl

@[simp]
def pop_push_last (v: Array.Vector α (n + 1)) : v.pop.push v.last = v := by
  ext i
  dsimp at i
  cases i using Fin.lastCases
  simp
  rfl; simp
  apply getElem_pop

instance : Subsingleton (Array.Vector α 0) where
  allEq := by
    intro ⟨⟨[]⟩, ha⟩ ⟨⟨[]⟩, hb⟩
    rfl

@[simp]
def push_pop (v: Array.Vector α n) (x: α) : (v.push x).pop = v := by
  ext i
  dsimp at i
  simp
  erw [getElem_pop (v.push x) i i.isLt, getElem_push_lt]
  rfl
@[simp]
def push_last (v: Array.Vector α n) (x: α) : (v.push x).last = x := by
unfold last
simp

@[simp] def toArray_nil (v: Array.Vector α 0) : v.toArray = #[] := by
  rw [Subsingleton.allEq v .nil]
  rfl
@[simp] def toArray_push (v: Array.Vector α n) (x: α) : (v.push x).toArray = v.toArray.push x := rfl

section Induction

variable {motive : ∀n, Array.Vector α n -> Sort*}
  (nil: motive 0 Array.Vector.nil)
  (push: ∀n v x, motive n v -> motive (n + 1) (v.push x))

@[induction_eliminator]
def rec' {n} (v: Array.Vector α n) : motive n v :=
  Nat.rec (motive := fun len => ∀(v: Array.Vector α len), motive len v)
    (fun v => Subsingleton.allEq v _ ▸ nil)
    (fun n ih v => by
      have := (push _ v.pop v.last (ih _))
      simpa using this)
    n
    v

private def rec_congr (h: v₀ = v₁): HEq (rec' nil push v₀) (rec' nil push v₁) := by
subst h; rfl

@[simp]
def rec'_nil : rec' nil push .nil = nil := rfl
@[simp]
def rec'_push (v: Array.Vector α n) (x: α) : rec' nil push (v.push x) = push _ v x (rec' nil push v) := by
  rw [rec']
  simp
  apply cast_eq_of_heq
  congr
  rw [push_pop]
  rw [push_last]
  unfold rec'
  simp
  apply rec_congr
  simp

end Induction

section Cases

variable {motive : ∀n, Array.Vector α n -> Sort*}
  (nil: motive 0 Array.Vector.nil)
  (push: ∀n (v: Array.Vector α n) x, motive (n + 1) (v.push x))

@[cases_eliminator]
def cases {n} (v: Array.Vector α n) : motive n v :=
  match n with
  | 0 => Subsingleton.allEq v _ ▸ nil
  | n + 1 => by
      have := (push _ v.pop v.last)
      simpa using this

private def cases_congr (h: v₀ = v₁): HEq (cases nil push v₀) (cases nil push v₁) := by
subst h; rfl

@[simp]
def cases_nil : cases nil push .nil = nil := rfl
@[simp]
def cases_push (v: Array.Vector α n) (x: α) : cases nil push (v.push x) = push _ v x := by
  rw [cases]
  simp
  apply cast_eq_of_heq
  congr
  rw [push_pop]
  rw [push_last]

end Cases

def append (v₀: Array.Vector α n) (v₁: Array.Vector α m) : Array.Vector α (n + m) where
  toArray := v₀.toArray ++ v₁.toArray
  size_eq := by rw [Array.size_append, v₀.size_eq, v₁.size_eq]

def map (f: α -> β) (v: Array.Vector α n) : Array.Vector β n where
  toArray := v.toArray.map f
  size_eq := by simp [v.size_eq]

def flatten (v: Array.Vector (Array.Vector α m) n) : Array.Vector α (n * m) where
  toArray := v.toArray.flatMap toArray
  size_eq := by
    induction v with
    | nil => simp
    | push _ v x ih =>
      rw [toArray_push, Array.flatMap_push, Array.size_append, ih, x.size_eq, Nat.succ_mul]

def flatMap (f: α -> Array.Vector β m) (v: Array.Vector α n) : Array.Vector β (n * m) := (v.map f).flatten

def set (v: Array.Vector α n) (i: Fin n) (x: α) : Array.Vector α n where
  toArray := v.toArray.set i x (v.size_eq.symm ▸ i.isLt)
  size_eq := by rw [Array.size_set, v.size_eq]


end Array.Vector
