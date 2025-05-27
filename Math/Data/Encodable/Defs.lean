import Math.Logic.Equiv.Like
import Math.Data.Nat.Find
import Math.Data.Nat.Pairing
import Math.Data.Fintype.Defs

structure Encodable.Repr (α: Type*) where
  ofEncode ::
  encode: α -> ℕ
  decode: ℕ -> Option α
  encode_decode: ∀x, decode (encode x) = x
  spec (n: ℕ): (decode n).isSome ↔ ∃a, n = encode a

class Encodable (α: Type*) where
  ofRepr ::
  toRepr : Trunc (Encodable.Repr α)

namespace Encodable

namespace Repr

def toEmbedding (r: Repr α) : α ↪ ℕ where
  toFun := r.encode
  inj' := by
    intro x y h
    have : r.decode (r.encode x) = r.decode (r.encode y) := by rw [h]
    rw [r.encode_decode, r.encode_decode] at this
    exact Option.some.inj this

def decode_congr (r₀ r₁: Repr α) (n: ℕ) :
  r₀.encode = r₁.encode ->
  (∃a, n = r₀.encode a) -> (∃a, n = r₁.encode a) ->
  r₀.decode n = r₁.decode n := by
  intro eq ⟨a, h⟩ ⟨b, g⟩
  subst h
  rw [r₀.encode_decode, g, r₁.encode_decode]
  rw [eq] at g
  rw [r₁.toEmbedding.inj g]

instance : EmbeddingLike (Repr α) α ℕ where
  coe_inj := by
    intro x y h
    dsimp at h
    have eq := Embedding.mk.inj h
    suffices x.decode = y.decode by
      cases x <;> cases y
      congr
    funext i
    by_cases h₀:(x.decode i).isSome
    by_cases h₁:(y.decode i).isSome
    · apply decode_congr
      assumption
      apply (x.spec _).mp
      assumption
      apply (y.spec _).mp
      assumption
    · have := (Iff.not_iff_not (y.spec i)).mp (by assumption)
      simp only [←eq] at this
      have := (Iff.not_iff_not (x.spec i)).mpr this
      contradiction
    · have := (Iff.not_iff_not (x.spec i)).mp (by assumption)
      simp only [eq] at this
      have := (Iff.not_iff_not (y.spec i)).mpr this
      simp at h₀ this
      rw [h₀, this]

def choice [h: Nonempty α] (r: Repr α) : α :=
  have : ∃i, (r.decode i).isSome := by
    have ⟨x⟩ := h
    exists r.encode x
    dsimp
    rw [r.encode_decode]
    rfl
  let i := Nat.find this
  (r.decode i).get (Nat.find_spec this)

def mk [DecidableEq α] (encode: α -> ℕ) (decode : ℕ -> Option α) (spec: ∀x, decode (encode x) = x) : Repr α where
  encode := encode
  decode i :=
    match h:decode i with
    | .none => .none
    | .some x =>
      if encode x = i then
        .some x
      else
        .none
  encode_decode := by
    intro x
    rw [spec]
    simp
  spec := by
    intro i
    split
    simp
    intro x h
    subst i
    rename_i g
    rw [spec] at g
    contradiction
    simp; rename_i a g
    apply Iff.intro
    intro; exists a
    symm; assumption
    rintro ⟨b, rfl⟩
    rw [spec] at g
    cases g; rfl

@[simp]
def coe_decode (r: Repr α) (a: α) : r.decode (r a) = a := r.encode_decode a
def decode_coe (r: Repr α) (i: ℕ) (h: ∃a, i = r a) : r ((r.decode i).get (by
  obtain ⟨a, rfl⟩ := h
  rw [r.coe_decode]
  rfl)) = i := by
  obtain ⟨i, rfl⟩ := h
  simp [r.coe_decode]

def coe_spec (r: Repr α) (n: ℕ): (r.decode n).isSome ↔ ∃a, n = r a := r.spec n

def of_decode_eq_some (r: Repr α) (i: ℕ) (a: α) : r.decode i = a -> r a = i := by
  intro h
  have : r ((r.decode i).get (by rw [h]; rfl)) = i := by
    rw [decode_coe]
    apply (r.coe_spec _).mp
    rw [h]; rfl
  simpa [h] using this

end Repr

instance : Subsingleton (Encodable α) where
  allEq a b := by cases a; cases b; congr; apply Subsingleton.allEq

def toEmbedding (α: Type*) [e: Encodable α] : Trunc (α ↪ ℕ) :=
  e.toRepr.map Repr.toEmbedding

def choice {α: Type*} [e: Encodable α] (h: Nonempty α) : Trunc α :=
  e.toRepr.map fun e => e.choice

def mk [DecidableEq α] (encode: α -> ℕ) (decode : ℕ -> Option α) (spec: ∀x, decode (encode x) = x) : Encodable α where
  toRepr := Trunc.mk (Repr.mk encode decode spec)

instance [e: Encodable α] : DecidableEq α := e.toRepr.recOnSubsingleton fun e => e.toEmbedding.DecidableEq

def ofFintype (α: Type*) [DecidableEq α] [f: Fintype α] : Encodable α where
  toRepr :=
    f.toEquiv.map fun f => {
      encode a := f.symm a
      decode i := if h:i < Fintype.card α then Option.some (f ⟨i, h⟩) else .none
      encode_decode a := by simp
      spec i := by
        simp
        apply Iff.intro
        · intro h
          exists f ⟨_, h⟩
          simp
        · rintro ⟨a, rfl⟩
          simp

    }

def ofEquiv' [e: Encodable α] (h: α ≃ β) : Encodable β where
  toRepr := e.toRepr.map fun e => {
    encode := e.encode ∘ h.symm
    decode := Option.map h ∘ e.decode
    encode_decode x := by simp [e.encode_decode]
    spec i := by
      simp
      apply Iff.trans (e.spec _)
      apply Iff.intro
      intro ⟨a, g⟩
      exists h a
      simpa
      intro ⟨a, g⟩
      exists h.symm a
  }
def ofEquiv [Encodable β] (h: α ≃ β) : Encodable α := ofEquiv' h.symm

instance : Encodable (Fin n) := ofFintype _
instance : Encodable Bool := ofFintype _
instance [IsEmpty α] : Encodable α :=
  have : DecidableEq α := fun a => elim_empty a
  ofFintype _
instance [Inhabited α] [Subsingleton α] : Encodable α :=
  have : DecidableEq α := fun _ _ => .isTrue (Subsingleton.allEq _ _)
  ofFintype _

instance : Encodable ℕ where
  toRepr := Trunc.mk {
    encode i := i
    decode i := i
    encode_decode i := rfl
    spec i := by
      dsimp
      apply Iff.intro
      intro; exists i
      intro; rfl
  }

instance [eα: Encodable α] [eβ: Encodable β] : Encodable (α ⊕ β) where
  toRepr :=
    eα.toRepr.bind fun eα =>
    eβ.toRepr.map fun eβ => {
    encode
    | .inl i => 2 * eα i
    | .inr i => 2 * eβ i + 1
    decode i :=
      if i % 2 = 0 then
        eα.decode (i / 2) |>.map .inl
      else
        eβ.decode (i / 2) |>.map .inr
    encode_decode i := by
      cases i <;> simp
      rw [Nat.mul_add_div, Nat.div_eq_of_lt, Nat.add_zero]
      all_goals simp
    spec i := by
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · simp [h]
        rw [eα.coe_spec]
        apply Iff.intro
        intro ⟨a, g⟩
        exists .inl a
        simp
        rw [←g]
        rw [Nat.mul_div_cancel']
        rwa [Nat.dvd_iff_mod_eq_zero]
        rintro ⟨x, rfl⟩
        cases x <;> simp at h
        simp
        rename_i x
        exists x
      · simp [h]
        rw [eβ.coe_spec]
        apply Iff.intro
        intro ⟨a, g⟩
        exists .inr a
        simp
        rw [←g, ←h, Nat.div_add_mod]
        rintro ⟨x, rfl⟩
        cases x <;> simp at h
        simp
        rename_i x
        exists x
        rw [Nat.mul_add_div, Nat.div_eq_of_lt, Nat.add_zero]
        omega
        omega
  }

instance [eα: Encodable α] : Encodable (Option α) where
  toRepr := eα.toRepr.map fun eα => {
    encode
    | .none => 0
    | .some x => eα x + 1
    decode
    | 0 => .some .none
    | n + 1 => eα.decode n |>.map .some
    encode_decode x := by cases x <;> simp
    spec i := by
      cases i
      simp
      exists .none
      simp
      apply Iff.trans (eα.coe_spec _)
      apply Iff.intro
      · intro ⟨a, h⟩
        exists .some a
        simpa
      · intro ⟨a, h⟩
        cases a
        contradiction
        rename_i a
        exists a
        simpa using h
  }

instance : Encodable ℤ := Encodable.ofEquiv Equiv.int_equiv_nat_sum_nat

instance [eα: Encodable α] [eβ: Encodable β] : Encodable (α × β) where
  toRepr :=
    eα.toRepr.bind fun eα =>
    eβ.toRepr.map fun eβ => {
      encode x := Equiv.nat_equiv_nat_prod_nat.symm (eα x.1, eβ x.2)
      decode n :=
        have x := Equiv.nat_equiv_nat_prod_nat n
        (eα.decode x.1).bind (fun a => (eβ.decode x.2).map fun b => (a, b))
      encode_decode x := by simp
      spec i := by
        simp
        apply Iff.intro
        · intro h
          let x := Equiv.nat_equiv_nat_prod_nat i
          cases h₀:eα.decode x.1
          rw [h₀] at h
          simp at h
          cases h₁:eβ.decode x.2
          rw [h₁] at h
          simp at h
          clear h
          have ⟨a, ha⟩ := (eα.coe_spec x.fst).mp (by simp [h₀])
          have ⟨b, hb⟩ := (eβ.coe_spec x.snd).mp (by simp [h₁])
          exists a; exists b
          rw [←ha, ←hb]
          simp [x]
          show i = Equiv.nat_equiv_nat_prod_nat.symm (Equiv.nat_equiv_nat_prod_nat _)
          simp
        · rintro ⟨a, b, rfl⟩
          simp
    }

instance {P: α -> Prop} [DecidablePred P] [eα: Encodable α] : Encodable (Subtype P) where
  toRepr := eα.toRepr.map fun eα => {
    encode x := eα x.val
    decode i :=
      match eα.decode i with
      | .none => .none
      | .some a =>
        if p:P a then
          .some ⟨_, p⟩
        else
          .none
    encode_decode x := by simp; exact x.property
    spec i := by
      simp
      cases h:eα.decode i
      simp
      rintro x hx rfl
      simp at h
      simp
      rename_i a
      apply Iff.intro
      intro p
      exists a
      apply And.intro
      assumption
      exact (eα.of_decode_eq_some _ _ h).symm
      rintro ⟨_, _, rfl⟩
      simp at h
      subst a; assumption
  }

def choose [e: Encodable α] {P: α -> Prop} [DecidablePred P] (h: ∃a, P a) : Trunc { x // P x } :=
  choice <| by
    obtain ⟨x, h⟩ := h
    exists x

end Encodable
