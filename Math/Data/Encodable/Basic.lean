import Math.Type.Basic
import Math.Data.Nat.Find
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

def Embedding [Encodable α] : α ↪ Nat where
  toFun := encode
  inj := encode_inj

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
    dsimp
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
  ∃ (f : ∀ x, β x), ∀ x, r x (f x) :=
  ⟨_, fun x => choose_spec (h x)⟩

private def cantor (enc: Encodable (Nat -> Bool)) (n: Nat) : Bool :=
  match enc.decode' n with
    | .some g => !g n
    | .none => false

def cantor_diag : Encodable (Nat -> Bool) -> False := by
  intro enc
  let fenc := enc.encode (cantor enc)
  have h : enc.decode' (enc.encode (cantor enc)) = (cantor enc) := by rw [decode'_spec]
  have g : (decode' (encode (cantor enc))).get (by rw[h]; rfl) = (cantor enc) := by
    apply Option.some.inj
    rw [Option.some_get, h]
  have := congrFun g (encode (cantor enc))
  conv at this => {
    rhs; rw [cantor, h]; dsimp
  }
  conv at this => { lhs; arg 1; rw [h] }
  rw [Option.get_some] at this
  have := Bool.eq_not.mp this
  contradiction

end Encodable

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

instance [Encodable α] [Encodable β] : Encodable (α ⊕ β) where
  encode
  | .inl x => 2 * encode x
  | .inr x => 2 * encode x + 1
  decode' x :=
    if x % 2 = 0 then
      (decode' (x / 2)).map .inl
    else
      (decode' (x / 2)).map .inr
  spec
  | .inl x => by
    dsimp
    rw [if_pos, Nat.mul_comm, Nat.mul_div_cancel, decode'_spec]
    rfl
    decide
    rw [Nat.mul_mod_right]
  | .inr x => by
    dsimp
    rw [if_neg, Nat.mul_add_div, Nat.div_eq, if_neg, Nat.add_zero, decode'_spec]
    rfl
    decide
    decide
    rw [Nat.add_mod,  Nat.mul_mod_right, Nat.zero_add]
    decide
