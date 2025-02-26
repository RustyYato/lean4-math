import Math.Logic.Equiv.Basic
import Math.Function.Basic
import Math.Data.Fin.Pairing

def List.Vector (α: Type*) (n: Nat) := { v: List α // v.length = n }

namespace List.Vector

variable {α: Type*}

def toList: Vector α n -> List α := Subtype.val

instance : CoeTC (Vector α n) (List α) := ⟨toList⟩
attribute [coe] toList

def coe_length (as: Vector α n) : (as: List α).length = n := as.property
def coe_inj : Function.Injective (toList (α := α) (n := n)) := by
  intro a b eq; cases a; congr

def length_comp_toList : length ∘ (toList (α := α) (n := n)) = fun _ => n := by
  ext x
  dsimp
  rw [coe_length]

def nil (α: Type*) : Vector α 0 := ⟨[], rfl⟩
abbrev cons (a: α) (as: Vector α n) : Vector α (n+1) := ⟨a::as, by rw [List.length_cons, coe_length]⟩

scoped infix:67 "::ᵥ" => cons

def cast (as: Vector α n) (h: n = m) : Vector α m where
  val := as
  property := by rw [coe_length, h]

@[cases_eliminator]
def cases
  {motive: ∀{n}, Vector α n -> Sort*}
  (nil: motive (.nil α))
  (cons: ∀{n: Nat} (a: α) (as: Vector α n), motive (a::ᵥas))
  : ∀{n: Nat} (v: Vector α n), motive v
| 0, .mk [] _ => nil
| _ + 1, .mk (_::as) ha => cons _ ⟨as, Nat.succ.inj ha⟩

def casesNil
  {motive: Vector α 0 -> Sort*}
  (nil: motive (.nil α))
  : ∀(v: Vector α 0), motive v
| .mk [] _ => nil

def casesCons
  {motive: ∀{n}, Vector α (n + 1) -> Sort*}
  (cons: ∀{n: Nat} (a: α) (as: Vector α n), motive (a::ᵥas))
  : ∀{n} (v: Vector α (n + 1)), motive v
| _, .mk (_::as) ha => cons _ ⟨as, Nat.succ.inj ha⟩

@[induction_eliminator]
def rec
  {motive: ∀{n}, Vector α n -> Sort*}
  (nil: motive (.nil α))
  (cons: ∀{n: Nat} (a: α) (as: Vector α n), motive as -> motive (a::ᵥas))
  : ∀{n: Nat} (v: Vector α n), motive v
| 0, .mk [] _ => nil
| _ + 1, .mk (_::as) ha => cons _ _ (rec nil cons ⟨as, Nat.succ.inj ha⟩)

instance : Subsingleton (List.Vector α 0) where
  allEq a b := by cases a; cases b; rfl

instance : GetElem (Vector α n) (Fin m) α (fun _ _ => m ≤ n) where
  getElem
  | ⟨as, ha⟩, ⟨i, hi⟩, h => as[i]

instance : GetElem (Vector α n) Nat α (fun _ i => i < n) where
  getElem
  | ⟨as, ha⟩, i, h => as[i]

instance : HAppend (Vector α n) (Vector α m) (Vector α (n + m)) where
  hAppend as bs := {
    val := as ++ bs
    property := by rw [List.length_append, coe_length, coe_length]
  }

abbrev mk : ∀as: List α, as.length = n -> Vector α n := Subtype.mk

@[simp]
def getElem_cons_zero (a: α) (as: Vector α n) :  (a::ᵥas)[0] = a := rfl
@[simp]
def getElem_cons_succ (a: α) (as: Vector α n) (i: Fin n) :  (a::ᵥas)[i.succ] = as[i] := rfl
def mk_getElem (as: List α) (h: as.length = n) (i: Fin m) (g: m ≤ n) :  (mk as h)[i] = as[i.val] := rfl

def tail (as: Vector α n) : Vector α (n - 1) :=
  match n, as with
  | 0, .nil _ => .nil _
  | _+1, .mk (_::as) h => .mk as (Nat.succ.inj h)

def head (as: Vector α (n + 1)) : α :=
  match as with
  | .mk (a::_) _ => a

@[simp]
def getElem_zero_head (as: Vector α (n + 1)) {m: Nat} (h: m ≤ n) : as[(0: Fin (m+1))] = as.head := by
  cases as
  rfl

@[simp]
def getElem_succ_tail (as: Vector α n) (i: Fin m) (h: m < n) : as[i.succ] = as.tail[i] := by
  cases as
  contradiction
  rfl

@[simp]
def getElem_cons_tail (a: α) (as: Vector α n) : (a::ᵥas).tail = as := rfl
@[simp]
def getElem_cons_head (a: α) (as: Vector α n) : (a::ᵥas).head = a := rfl
@[simp]
def getElem_cast (as: Vector α n) (g: n = n') (i: Fin m) (h: m ≤ n) : (as.cast g)[i] = as[i] := rfl

def getElem_eq_index (as: Vector α n) (i: Fin ki) (j: Fin kj) (hi: ki ≤ n) (hj: kj ≤ n) (eq: i.val = j.val) : as[i] = as[j] := by
  cases i with | mk i =>
  cases j with | mk j =>
  cases eq
  rfl

def getElem_append (as: Vector α n) (bs: Vector α m) (i: Fin k) (h: k ≤ n + m) :
  (as ++ bs)[i] = if h:i.val < n then as[Fin.mk i h] else bs[Fin.mk (i.val - n) (by
    show i.val - n < k - n
    refine Nat.sub_lt_sub_right ?_ ?_
    apply Nat.le_of_not_lt; assumption
    apply Fin.isLt)] := by
  show (as.toList ++ bs.toList)[i.val]'_ = _
  rw [List.getElem_append]
  split <;> rename_i g
  rw [coe_length] at g
  rw [dif_pos g]
  rfl
  rw [dif_neg]
  congr; rw [coe_length]
  rw [coe_length] at g
  assumption

@[ext]
def ext (a b: Vector α n) : (∀i: Fin n, a[i] = b[i]) -> a = b := by
  intro h
  induction a with
  | nil => apply Subsingleton.allEq
  | cons a as ih =>
    cases b with | cons b bs =>
    have := h 0
    simp at this
    cases this
    rw [ih bs]
    intro i
    have := h i.succ
    simp at this
    assumption

def replicate (n: Nat) (a: α) : Vector α n where
  val := List.replicate n a
  property := by rw [List.length_replicate]

@[simp]
def getElem_replicate (i: Fin n) :  (replicate n a)[i] = a := by
  rw [replicate, mk_getElem, List.getElem_replicate]

def flatten (v: Vector (Vector α n) m) : Vector α (m * n) where
  val := v.toList.flatMap toList
  property := by
    rw [List.length_flatMap, ←Function.comp_def, length_comp_toList, map_const']
    rw [coe_length]
    clear v
    induction m with
    | zero => rw [Nat.zero_mul]; rfl
    | succ m ih => rw [List.replicate, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]

def flatten_cons (a: Vector α n) (as: Vector (Vector α n) m) :
  (a::ᵥas).flatten = (a ++ as.flatten).cast (by rw [Nat.succ_mul, Nat.add_comm]) := by
  apply coe_inj
  rfl

def getElem_flatten (v: Vector (Vector α n) m) (i: Fin (m * n)) :
  v.flatten[i] = v[i.pair_left][i.pair_right] := by
  induction v with
  | nil =>
    rw [Nat.zero_mul] at i
    exact i.elim0
  | cons v vs ih =>
    rename_i m
    rw [flatten_cons, getElem_cast, getElem_append]
    split <;> rename_i h
    unfold Fin.pair_left Fin.pair_right
    conv in i.val / n => { rw [Nat.div_eq_of_lt h] }
    conv in i.val % n => { rw [Nat.mod_eq_of_lt h] }
    simp
    rw [getElem_eq_index (i := Fin.mk (i.val - n) _) (j := Fin.mk (n := m * n) (i.val - n) ?_),
      ih]
    · unfold Fin.pair_left Fin.pair_right
      simp
      conv in i.val / n => { rw [Nat.div_eq, if_pos (by
        apply And.intro
        apply Nat.zero_lt_of_ne_zero
        rintro rfl
        rw [Nat.mul_zero] at i
        exact i.elim0
        apply Nat.le_of_not_lt
        assumption)] }
      conv in i.val % n => { rw [Nat.mod_eq, if_pos (by
        apply And.intro
        apply Nat.zero_lt_of_ne_zero
        rintro rfl
        rw [Nat.mul_zero] at i
        exact i.elim0
        apply Nat.le_of_not_lt
        assumption)] }
      rfl
    · rfl
    · apply Nat.lt_of_lt_of_le
      apply Nat.sub_lt_sub_right
      apply Nat.le_of_not_lt
      assumption
      apply Fin.isLt
      rw [Nat.succ_mul, Nat.add_sub_cancel]; apply Nat.le_refl
    · rw [Nat.succ_mul, Nat.add_comm]; apply Nat.le_refl

def map (f: α -> β) (v: Vector α n) : Vector β n where
  val := v.toList.map f
  property := by rw [List.length_map, coe_length]

@[simp]
def getElem_map (v: Vector α n) (i: Fin m) (h: m ≤ n) : (v.map f)[i] = f v[i] := by
  show (v.toList.map f)[i.val]'_ = _
  rw [List.getElem_map]
  rfl

def flatMap (f: α -> Vector β m) (v: Vector α n) : Vector β (n * m) := (v.map f).flatten

def zip (a: Vector α n) (b: Vector β n) : Vector (α × β) n where
  val := a.toList.zip b
  property := by  rw [List.length_zip, coe_length, coe_length, Nat.min_self]

@[simp]
def getElem_zip (a: Vector α n) (b: Vector β n) (i: Fin m) (h: m ≤ n) : (a.zip b)[i] = (a[i], b[i]) := by
  show (a.toList.zip b.toList)[i.val]'_ = _
  rw [List.getElem_zip]
  rfl

def ofFn (f: Fin n -> α) : Vector α n where
  val := List.ofFn f
  property := by rw [List.length_ofFn]

@[simp]
def getElem_ofFn (f: Fin n -> α) (i: Fin n) : (ofFn f)[i] = f i := by
  show (List.ofFn f)[i.val]'_ = _
  rw [List.getElem_ofFn]

def equivFinFunc (α: Type*) (n: Nat) : Vector α n ≃ (Fin n -> α) where
  toFun x n := x[n]
  invFun := ofFn
  leftInv := by
    intro x
    ext i
    simp
  rightInv := by
    intro x
    simp

end List.Vector
