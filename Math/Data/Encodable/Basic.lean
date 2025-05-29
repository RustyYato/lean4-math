import Math.Logic.Equiv.Basic
import Math.Data.Nat.Find
import Math.Data.Nat.Pairing
import Math.Function.Basic

class Encodable (α: Type*) where
  encode: α -> Nat
  decode': Nat -> Option α
  spec: ∀x, decode' (encode x) = x

export Encodable (encode decode')

def decode (repr: Nat) [Encodable α]: Option α :=
  match decode' repr with
  | .some x => if encode x = repr then .some x else .none
  | .none => .none

def decode'_spec (x: α) [Encodable α] : decode' (encode x) = .some x := Encodable.spec _
def decode_spec (repr: Nat) [Encodable α] : (decode repr: Option α).isSome ↔ ∃x: α, encode x = repr := by
  unfold decode
  split; split
  all_goals
    try rename α => x
    try rename decode' _ = _ => hd
    try rename encode _ = _ => he
    try rename ¬encode _ = _ => he
  apply Iff.intro
  intro h
  exists x
  intro ⟨y, h⟩
  rfl
  apply Iff.intro
  intro
  contradiction
  intro ⟨y, h⟩
  rw [←h] at hd
  rw [decode'_spec] at hd
  cases hd
  contradiction
  apply Iff.intro
  intro h
  contradiction
  intro ⟨y, h⟩
  rw [←h] at hd
  rw [decode'_spec] at hd
  contradiction

def encode_inj [Encodable α] : Function.Injective (encode (α := α)) := by
  intro x y eq
  have := decode'_spec y
  rw [←eq, decode'_spec] at this
  cases this
  rfl

namespace Encodable

instance (priority := 100) [Encodable α] : DecidableEq α :=
  fun a b =>
  if h:encode a = encode b then
    .isTrue (encode_inj h)
  else
    .isFalse fun g => h (g ▸ rfl)

-- the type of natural numbers which are in the range of `encode`
def Encoding (α: Type*) [Encodable α] := { x: Nat // ∃a: α, encode a = x }

def equivEncoding (α: Type*) [Encodable α] : α ≃ Encoding α where
  toFun x := {
    val := encode x
    property := ⟨_, rfl⟩
  }
  invFun x :=
    match h:decode' x.val with
    | .none => False.elim <| by
      have ⟨i, g⟩ := x.property
      rw [←g] at h
      rw [spec] at h
      contradiction
    | .some x => x
  leftInv x := by
    dsimp; split <;> rename_i h
    simp [spec] at h
    simp [spec] at h
    symm; assumption
  rightInv x := by
    simp
    apply Subtype.val_inj
    simp
    split
    contradiction
    obtain ⟨x, hx⟩ := x
    rename_i a h
    dsimp at *
    obtain ⟨x, rfl⟩ := hx
    simp [spec] at h
    rw [h]

def Embedding [Encodable α] : α ↪ Nat where
  toFun := encode
  inj' := encode_inj

def ofEquiv' [Encodable α] (h: α ≃ β) : Encodable β where
  encode x := encode (h.symm x)
  decode' x := (decode' x).map h
  spec x := by simp [spec]

def ofEquiv [Encodable β] (h: α ≃ β) : Encodable α := ofEquiv' h.symm

instance : Encodable Nat where
  encode := id
  decode' := .some
  spec _ := rfl

instance : Encodable (Fin n) where
  encode := Fin.val
  decode' x := if h:x < n then  .some ⟨x, h⟩ else .none
  spec x := by
    dsimp
    rw [if_pos x.isLt]

instance {P: α -> Prop} [DecidablePred P] [Encodable α] : Encodable (Subtype P) where
  encode x := encode x.val
  decode' x :=
    match decode' x with
    | .none => .none
    | .some x =>
    if h:P x then
      .some ⟨x, h⟩
    else
      .none
  spec x := by
    split
    rename_i h
    erw [decode'_spec] at h
    contradiction
    rename_i x h
    split <;> rename_i hx
    congr
    apply Option.some.inj
    symm
    rw [←decode'_spec]
    assumption
    erw [decode'_spec] at h
    cases h
    have := hx x.property
    contradiction

instance : Encodable Bool where
  encode
  | false => 0
  | true => 1
  decode'
  | 0 => .some false
  | 1 => .some true
  | _ => .none
  spec
  | false => rfl
  | true => rfl

instance [Encodable α] : Encodable (Option α) where
  encode
  | .none => 0
  | .some x => encode x + 1
  decode'
  | 0 => .some .none
  | x+1 => (decode' x).map .some
  spec
  | .none => rfl
  | .some x => by
    dsimp
    rw [decode'_spec]
    rfl

instance [eα: Encodable α] [eβ: Encodable β] : Encodable (α ⊕ β) where
  encode x := Equiv.nat_equiv_nat_sum_nat.symm (Sum.map eα.encode eβ.encode x)
  decode' n :=
    match (Equiv.nat_equiv_nat_sum_nat n).map eα.decode' eβ.decode' with
    | .inl .none | .inr .none => .none
    | .inl (.some x) => .some (.inl x)
    | .inr (.some x) => .some (.inr x)
  spec x := by cases x <;> simp [eα.spec, eβ.spec, Sum.map]

instance {α: ι -> Type*} [eι: Encodable ι] [eα: ∀i, Encodable (α i)] : Encodable (Σi, α i) where
  encode x := Equiv.nat_equiv_nat_prod_nat.symm (eι.encode x.1, (eα _).encode x.2)
  decode' x :=
    have x := Equiv.nat_equiv_nat_prod_nat x
    (eι.decode' x.1).bind fun i => ((eα i).decode' x.2).map fun a => ⟨i, a⟩
  spec x := by simp [eι.spec, (eα _).spec]

instance [eα: Encodable α] [eβ: Encodable β] : Encodable (α × β) := Encodable.ofEquiv (Equiv.prod_equiv_sigma _ _)
instance : Encodable Int := Encodable.ofEquiv Equiv.int_equiv_nat_sum_nat

-- a computable choice function for Encodable types
def choice {α: Type*} [Encodable α] (h: Nonempty α) : α :=
  have : ∃n, (decode' n).isSome := (by
    obtain ⟨x⟩ := h
    exists encode x
    dsimp
    rw [decode'_spec]
    rfl)
  (decode' (Nat.findP this)).get (Nat.findP_spec this)

section

variable {α : Type*} [Encodable α] {p : α → Prop} [DecidablePred p] (h : ∃ x, p x)

def indefiniteDescription : {x // p x} := by
  apply choice
  obtain ⟨x, px⟩ := h
  exact ⟨⟨x, px⟩⟩

-- a computable version of Classical.choose for countable types
def choose: α := indefiniteDescription h
def choose_spec: p (choose h) := (indefiniteDescription h).property

end

/-- the axiom of choice for sets of countable types -/
def axiomOfChoice {α : Sort u}
  {β : α → Type v} {r : ∀ x, β x → Prop}
  [∀x, Encodable (β x)]
  [∀x, DecidablePred (r x)]
  (h : ∀ x, ∃ y, r x y) :
  Subtype fun (f : ∀ x, β x) => ∀ x, r x (f x) :=
  ⟨_, fun x => choose_spec (h x)⟩

def cantor_diag : Encodable (Nat -> Bool) -> False := by
  intro enc
  exact Embedding.cantor Nat Bool ⟨encode, encode_inj⟩

end Encodable

def Quot.rep {r: α -> α -> Prop} [Encodable α] [DecidableEq (Quot r)] (a: Quot r) : α :=
  Encodable.choose a.exists_rep

def Quotient.rep [s: Setoid α] [Encodable α] [@DecidableRel α α (· ≈ ·)] (a: Quotient s) : α :=
  Encodable.choose a.exists_rep

def Quot.rep_spec {r: α -> α -> Prop} [Encodable α] [DecidableEq (Quot r)] (a: Quot r) : Quot.mk _ a.rep = a :=
  Encodable.choose_spec a.exists_rep

def Quotient.rep_spec [s: Setoid α] [Encodable α] [@DecidableRel α α (· ≈ ·)] (a: Quotient s) : Quotient.mk _ a.rep = a :=
  Encodable.choose_spec a.exists_rep
