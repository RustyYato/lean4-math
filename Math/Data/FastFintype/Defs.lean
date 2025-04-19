import Math.Logic.Equiv.Basic
import Math.Data.Trunc

structure Fintype.Encoding (α: Type*) where
  card: Nat
  all: Fin card ↪ α
  complete: Function.Surjective all
  decode : Option (α -> Fin card) := .none
  decode_spec : ∀f ∈ decode, ∀i: Fin card, f (all i) = i := by intro f hf; contradiction

class Fintype (α: Type*) where
  encode: Trunc (Fintype.Encoding α)

namespace Fintype

instance : Subsingleton (Fintype α) where
  allEq | ⟨a⟩, ⟨b⟩ => by congr; apply Subsingleton.allEq

def recOnSubsingleton {α: Type*}
  {motive: Fintype α -> Sort*}
  [∀f, Subsingleton (motive f)]
  (mk: ∀enc: Fintype.Encoding α, motive ⟨Trunc.mk enc⟩)
  (h: Fintype α) : motive h :=
  h.encode.recOnSubsingleton (motive := fun h => motive ⟨h⟩) fun h =>
  mk h

@[induction_eliminator]
def induction {α: Type*}
  {motive: Fintype α -> Prop}
  (mk: ∀enc: Fintype.Encoding α, motive ⟨Trunc.mk enc⟩)
  (h: Fintype α) : motive h :=
  recOnSubsingleton mk h

def lift
  [fa: Fintype α]
  (f: Fintype.Encoding α -> β)
  (resp: ∀x y, f x = f y): β := fa.encode.lift f resp

def hrec
  (α: Type*)
  {motive: Fintype α -> Sort*}
  [fa: Fintype α]
  (mk: ∀x, motive ⟨Trunc.mk x⟩)
  (resp: ∀a b, HEq (mk a) (mk b))
  : motive fa :=
  fa.encode.hrecOn (motive := fun f => motive ⟨f⟩) (fun x => mk x) <| by
    intro a b h
    dsimp
    apply resp

def map {α β: Type*}
  (mk: Fintype.Encoding α -> Fintype.Encoding β)
  (h: Fintype α) : Fintype β :=
  recOnSubsingleton (motive := fun _ => _) (fun x => ⟨Trunc.mk (mk x)⟩) h

def bind {α β: Type*}
  (mk: Fintype.Encoding α -> Fintype β)
  (h: Fintype α) : Fintype β :=
  recOnSubsingleton (motive := fun _ => _) mk h

def Encoding.card_eq (a b: Encoding α) : a.card = b.card := by
  obtain ⟨ac, fa, ha, ha', ha''⟩ := a
  obtain ⟨bc, fb, hb, hb', hb''⟩ := b
  simp
  clear ha' hb' ha'' hb''
  have eq_range : ∀{x}, (∃i: Fin ac, x = fa i) ↔ (∃i: Fin bc, x = fb i) := by
    intro x
    apply Iff.intro
    intro; apply hb
    intro; apply ha
  clear hb ha
  induction ac generalizing bc with
  | zero =>
    cases bc with
    | zero => rfl
    | succ bc =>
      have ⟨i, _⟩ := eq_range.mpr ⟨0, rfl⟩
      exact i.elim0
  | succ ac ih =>
    cases bc with
    | zero =>
      have ⟨i, _⟩ := eq_range.mp ⟨0, rfl⟩
      exact i.elim0
    | succ bc =>
      let a := fa 0
      let ⟨i, hi⟩ := eq_range.mp ⟨0, rfl⟩
      congr; refine ih ?_ _ ?_ ?_
      · exact (Embedding.finSucc _).trans fa
      · apply Embedding.trans _ fb
        apply Embedding.optionSome.trans
        apply Equiv.toEmbedding
        apply (Equiv.fin_erase i).symm
      · simp
        intro x
        apply Iff.intro
        · rintro ⟨j, rfl⟩
          have ⟨k, eq⟩ := eq_range.mp ⟨j.succ, rfl⟩
          suffices ((Equiv.fin_erase i) k).isSome = true by
            refine ⟨(Equiv.fin_erase i k).get this, ?_⟩
            rw [eq]
            congr
            simp
          rcases Nat.lt_trichotomy i k with h | h | h
          · rw [Equiv.apply_fin_erase_of_gt]
            rfl; assumption
          · rw [Fin.val_inj] at h
            subst k
            rw [←hi] at eq
            have := Fin.val_inj.mpr (fa.inj eq)
            contradiction
          · rw [Equiv.apply_fin_erase_of_lt]
            rfl; assumption
        · rintro ⟨j, rfl⟩
          let j' := ((Equiv.fin_erase i).symm (some j))
          show ∃i₀, fb j' = _
          have ⟨k, eq⟩ := eq_range.mpr ⟨j', rfl⟩
          cases k using Fin.cases with
          | succ k => exists k
          | zero =>
            exfalso
            rw [hi, fb.inj.eq_iff] at eq
            unfold j' at eq
            rcases Nat.lt_or_ge j.val i.val with h | h
            rw [Equiv.symm_apply_fin_erase_some_of_lt _ _ h,
              ←Fin.val_inj] at eq
            dsimp at eq
            omega
            rw [Equiv.symm_apply_fin_erase_some_of_ge _ _ h,
              ←Fin.val_inj] at eq
            dsimp at eq
            omega

def card (α: Type*) [f: Fintype α] : Nat :=
  f.hrec (motive := fun _ => Nat) _ (fun f => f.card) <| by
    intro a b
    simp; apply Encoding.card_eq

inductive FindResult (P: α -> Prop) where
| ok (a: α) (p: P a)
| never (h: ∀a: α, ¬P a)

def findFin (n: Nat) (P: Fin n -> Prop) [dec: DecidablePred P] : FindResult P :=
  match n, P, dec with
  | 0, P, dec => .never nofun
  | n + 1, P, dec =>
    match dec ⟨n, Nat.lt_succ_self _⟩ with
    | .isTrue h => .ok _ h
    | .isFalse h =>
    match findFin n (fun i => P i.castSucc) with
    | .ok _ h => .ok _ h
    | .never h => .never <| by
      intro i hi
      induction i using Fin.lastCases with
      | cast i => exact h i hi
      | last => contradiction

private def Encoding.equiv_ind₀
  (aenc: Fin (n + 1) ↪ α)
  (benc: Fin (m + 1) ↪ α)
  (idx: Fin (m + 1))
  (hi: benc idx = aenc (Fin.last n))
  (a_sub_b : ∀ (i : Fin (n + 1)), ∃ j, aenc i = benc j):
  ∀(i : Fin n), ∃j: Fin m, (aenc.comp (Fin.embedFin (Nat.le_succ _))) i = ((Embedding.fin_erase idx).trans benc) j := by
  intro k
  have ⟨j, hj⟩ := a_sub_b (Fin.embedFin (Nat.le_succ _) k)
  refine ⟨((Equiv.fin_erase idx) j).get ?_, ?_⟩
  rcases Nat.lt_trichotomy j.val idx.val with h | h | h
  · rw [Equiv.apply_fin_erase_of_lt _ _ h]
    rfl
  · rw [Fin.val_inj] at h
    subst j
    rw [hi] at hj
    have k_eq_last := aenc.inj hj
    obtain ⟨k, kLt⟩ := k
    simp [Fin.embedFin_eq_castLE] at k_eq_last
    cases k_eq_last
    omega
  · rw [Equiv.apply_fin_erase_of_gt _ _ h]
    rfl
  simp [Fin.embedFin]
  apply Eq.trans hj
  congr
  rcases Nat.lt_trichotomy j.val idx.val with h | h | h
  · simp [Equiv.apply_fin_erase_of_lt _ _ h]
    rw [Embedding.apply_fin_erase_of_lt _ _ h]
    rfl
  · rw [Fin.val_inj] at h
    subst j
    rw [hi] at hj
    have k_eq_last := aenc.inj hj
    obtain ⟨k, kLt⟩ := k
    simp [Fin.embedFin_eq_castLE] at k_eq_last
    cases k_eq_last
    omega
  · simp [Equiv.apply_fin_erase_of_gt _ _ h]
    rw [Embedding.apply_fin_erase_of_ge]
    simp; apply Fin.val_inj.mp; simp; omega
    simp; omega

private def Encoding.equiv_ind₁
  (aenc: Fin (n + 1) ↪ α)
  (benc: Fin (m + 1) ↪ α)
  (idx: Fin (m + 1))
  (hi: benc idx = aenc (Fin.last n))
  (b_sub_a : ∀(j: Fin (m + 1)), ∃ i, benc j = aenc i):
  ∀(j : Fin m), ∃i: Fin n, ((Embedding.fin_erase idx).trans benc) j = (aenc.comp (Fin.embedFin (Nat.le_succ _))) i := by
  intro k
  have ⟨j, hj⟩ := b_sub_a (Embedding.fin_erase idx k)
  have : ((Equiv.fin_erase (Fin.last n)) j).isSome = true := by
    rcases Nat.lt_trichotomy j.val (Fin.last n).val with h | h | h
    · rw [Equiv.apply_fin_erase_of_lt _ _ h]
      rfl
    · rw [Fin.val_inj] at h
      subst j
      rw [←hi] at hj
      have k_eq_last := benc.inj hj
      obtain ⟨k, kLt⟩ := k
      rw [Embedding.apply_fin_erase_of_ge] at k_eq_last
      simp at k_eq_last; subst idx
      rw [Embedding.apply_fin_erase_of_lt, benc.inj.eq_iff] at hj
      simp at hj
      simp; simp
      apply Nat.le_of_not_lt
      intro h
      rw [Embedding.apply_fin_erase_of_lt _ _ h] at k_eq_last
      simp at k_eq_last
      cases k_eq_last
      simp at h
    · rw [Equiv.apply_fin_erase_of_gt _ _ h]
      rfl
  refine ⟨((Equiv.fin_erase (Fin.last _)) j).get ?_, ?_⟩
  assumption
  simp
  apply Eq.trans hj
  congr
  simp [Fin.embedFin_eq_castLE]
  rcases Nat.lt_trichotomy j.val (Fin.last n).val with h | h | h
  · simp [Equiv.apply_fin_erase_of_lt _ _ h]
  · rw [Fin.val_inj] at h
    rw [h] at this
    simp at this
  · simp at h
    omega

private def Encoding.equiv'
  [DecidableEq α]
  (acard bcard: Nat)
  (aenc: Fin acard ↪ α)
  (benc: Fin bcard ↪ α)
  (a_sub_b: ∀i, ∃j, aenc i = benc j)
  (b_sub_a: ∀j, ∃i, benc j = aenc i)
   : { f: Fin acard ≃ Fin bcard // ∀x, aenc x = benc (f x) } :=
  match acard with
  | 0 =>
    match bcard with
    | 0 => ⟨.rfl, fun i => i.elim0⟩
    | bcard + 1 => False.elim <| by
      have ⟨i, _⟩ := b_sub_a 0
      exact i.elim0
  | acard + 1 =>
    match bcard with
    | 0 => False.elim <| by
      have ⟨i, _⟩ := a_sub_b 0
      exact i.elim0
    | bcard + 1 =>
      match findFin _ (fun i => benc i = aenc (Fin.last _)) with
      | .ok i hi =>
        let aenc' := aenc.comp (Fin.embedFin (Nat.le_succ _))
        let benc' := (Embedding.fin_erase i).trans benc
        have ⟨f, h⟩ := Encoding.equiv' acard bcard aenc' benc' (by
          apply Encoding.equiv_ind₀
          assumption
          assumption) (by
          apply Encoding.equiv_ind₁
          assumption
          assumption)
        let ha := Equiv.fin_erase (Fin.last acard)
        let hb := Equiv.fin_erase i
        let hf := Equiv.congrOption f
        {
          val := ha.trans (hf.trans hb.symm)
          property x := by
            simp [aenc', benc', Embedding.fin_erase] at h
            simp [ha, hb, hf]
            cases x using Fin.lastCases with
            | last =>
              rw [Equiv.apply_fin_erase_of_eq]
              simp [Equiv.symm_apply_fin_erase_none]
              symm; assumption
            | cast x =>
              erw [h]
              rw [Equiv.apply_fin_erase_of_lt]
              simp
              split
              rw [Equiv.symm_apply_fin_erase_some_of_lt]
              rfl
              assumption
              rw [Equiv.symm_apply_fin_erase_some_of_ge]
              rfl
              omega
              apply x.isLt
        }
      | .never h => False.elim <| by
        have ⟨_, g⟩ := a_sub_b (Fin.last _)
        exact h _ g.symm

@[irreducible]
def Encoding.equiv [DecidableEq α] (a b: Encoding α) : { f: Fin a.card ≃ Fin b.card // ∀x, a.all x = b.all (f x) } :=
  equiv' a.card b.card a.all b.all (by
    intro i
    have ⟨j, h⟩ := b.complete (a.all i)
    exists j) (by
    intro i
    have ⟨j, h⟩ := a.complete (b.all i)
    exists j)

private def find (n: Nat) (f: Nat -> α) (h: α -> Bool) (hx: ∃i < n, h (f i)) : Σ' i: Nat, i < n ∧ h (f i) :=
  match n with
  | 0 =>
    False.elim <| by
    have ⟨i, h, _⟩ := hx
    contradiction
  | n + 1 =>
    if hi:h (f n) then
      ⟨n, Nat.lt_succ_self _, hi⟩
    else
      have ⟨i, hi, eq⟩ := find n f h (by
        obtain ⟨i, hi, eq⟩ := hx
        exists i
        apply And.intro
        rw [Nat.lt_succ] at hi
        apply (Nat.lt_or_eq_of_le hi).resolve_right
        rintro rfl; contradiction
        assumption)
      ⟨i, Nat.lt_trans hi (Nat.lt_succ_self _), eq⟩

def ofEquiv' (h: α ≃ β) [f: Fintype α] : Fintype β :=
  f.map fun e => {
    card := e.card
    all := Equiv.congrEmbed .rfl h e.all
    complete x := by
      have ⟨i, g⟩ := e.complete (h.symm x)
      exists i
      show x = h (e.all i)
      simp [←g]
  }

def ofEquiv (h: α ≃ β) [f: Fintype β] : Fintype α := ofEquiv' h.symm

def equiv_fin_card (α: Type*) [DecidableEq α] [h: Fintype α] : Trunc (α ≃ Fin (card α)) :=
  h.encode.recOnSubsingleton (motive := fun e: Trunc (Fintype.Encoding α) => Trunc (α ≃ Fin (@card α ⟨e⟩))) <|
  fun enc =>
  if hcard:enc.card = 0 then
    Trunc.mk <| Equiv.symm <| Equiv.trans (Equiv.fin hcard) {
      toFun x := x.elim0
      invFun x := by
        exfalso
        have ⟨i, _⟩ := enc.complete x
        rw [hcard] at i
        exact i.elim0
      leftInv x := x.elim0
      rightInv x := by
        have ⟨i, _⟩ := enc.complete x
        rw [hcard] at i
        exact i.elim0
    }
  else
    have default : α := enc.all ⟨0, by omega⟩
    have find (x: α) := find enc.card (fun i => if hi:i < enc.card then enc.all ⟨i, hi⟩ else default)
      (x = ·) (by
        have ⟨i, h⟩ := enc.complete x
        refine ⟨i.val, i.isLt, ?_⟩
        simp [h])
    Trunc.mk {
      toFun x :=
        have := find x
        ⟨this.1, this.2.1⟩
      invFun := enc.all
      leftInv := by
        intro x
        simp
        let h := (find x)
        show enc.all ⟨h.1, _⟩ = x
        have h' := h.2.2
        simp at h'
        conv => { rhs; rw [h'] }
        rw [dif_pos h.2.1]
      rightInv := by
        intro x
        simp
        apply enc.all.inj
        let h := (find (enc.all x))
        show enc.all ⟨h.1, _⟩ = _
        have := h.2.2
        simp at this
        rw [dif_pos h.2.1] at this
        symm; assumption
    }

def equiv_of_card_eq (α β: Type*) [DecidableEq α] [DecidableEq β] {ha: Fintype α} {hb: Fintype β} (h: card α = card β) : Trunc (α ≃ β) :=
  (ha.equiv_fin_card _).bind fun fa =>
  (hb.equiv_fin_card _).map fun fb =>
  fa.trans <| (Equiv.fin h).trans fb.symm

def card_eq_of_equiv (h: α ≃ β) [fa: Fintype α] [fb: Fintype β] : card α = card β := by
  rw [Subsingleton.allEq fa (ofEquiv h)]
  induction fb; rfl
local instance decFinExists (n: Nat) (P: Fin n -> Prop) [dec: DecidablePred P] : Decidable (∃i: Fin n, P i) :=
  match n, P, dec with
  | 0, P, dec => .isFalse nofun
  | n + 1, P, dec =>
    match dec ⟨n, Nat.lt_succ_self _⟩ with
    | .isTrue h => .isTrue ⟨_, h⟩
    | .isFalse h =>
    match decFinExists n (fun i => P i.castSucc) with
    | .isTrue h => .isTrue <| by
      obtain ⟨i, p⟩ := h
      exists i.castSucc
    | .isFalse h => .isFalse <| by
      intro ⟨i, hi⟩; apply h
      induction i using Fin.lastCases with
      | cast i => exists i
      | last => contradiction

instance {P: α -> Prop} [DecidablePred P] [f: Fintype α] : Decidable (∃x, P x) :=
  f.recOnSubsingleton (motive := fun _ => _) fun enc =>
    decidable_of_iff (∃i: Fin enc.card, P (enc.all i)) <| by
      apply Iff.intro
      intro ⟨i, h⟩
      exact ⟨_, h⟩
      intro ⟨x, h⟩
      obtain ⟨i, rfl⟩ := enc.complete x
      exists i

instance {P: α -> Prop} [DecidablePred P] [Fintype α] : Decidable (∀x, P x) := decidable_of_iff _ Decidable.not_exists_not

instance {β: α -> Type _} [Fintype α] [∀x, DecidableEq (β x)] : DecidableEq (∀x, β x) :=
  fun f g => if h:∀x, f x = g x then
    .isTrue (funext h)
  else
    .isFalse fun eq => (eq ▸ h) fun _ => rfl

instance [Fintype α] [DecidableEq β] : DecidableEq (α -> β) := inferInstance

instance [Fintype α] [DecidableEq β] [DecidableEq α] {f: α -> β} : Decidable (Function.Injective f) :=
  inferInstance

instance [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {f: α -> β} : Decidable (Function.Surjective f) :=
  inferInstance

instance [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {f: α -> β} : Decidable (Function.Bijective f) :=
  inferInstance

instance [Fintype β] [DecidableEq β] {f: α -> β} {g: β -> α} : Decidable (Function.IsLeftInverse f g) := by
  delta Function.IsLeftInverse
  exact inferInstance
instance [Fintype α][DecidableEq α] {f: α -> β} {g: β -> α} : Decidable (Function.IsRightInverse f g) := by
  delta Function.IsRightInverse
  exact inferInstance

instance instFin : Fintype (Fin n) where
  encode := Trunc.mk {
    card := n
    all := .rfl
    complete _ := ⟨_, rfl⟩
    decode := .some id
    decode_spec := by
      intro f h; cases h
      intro i; rfl
  }

instance instBool : Fintype Bool where
  encode := Trunc.mk {
    card := 2
    all := {
      toFun
      | 0 => false
      | 1 => true
      inj' := by trivial
    }
    complete := by trivial
    decode := .some <| fun
    | false => 0
    | true => 1
    decode_spec := by
      intro f h; cases h
      intro i
      match i with | 0 | 1 => rfl
  }

instance instProp : Fintype Prop where
  encode := Trunc.mk {
      card := 2
      all := {
        toFun
        | 0 => false
        | 1 => true
        inj' := by
          intro x y
          simp
          match x, y with
          | 0, 0 | 0, 1 | 1, 1 | 1, 0 => simp
      }
      complete P := by
        by_cases h:P
        exists 1; simp [h]
        exists 0; simp [h]
  }

@[simp]
def card_fin {f: Fintype (Fin n)} : card (Fin n) = n := by
  rw [Subsingleton.allEq f instFin]
  rfl

@[simp]
def card_bool {f: Fintype Bool} : card Bool = 2 := by
  rw [Subsingleton.allEq f instBool]
  rfl

@[simp]
def card_prop {f: Fintype Prop} : card Prop = 2 := by
  rw [Subsingleton.allEq f instProp]
  rfl

-- stores all values in an array and then just
-- indexes the array to get the values
def cache (f: Fintype α) : Fintype α := f.map fun f =>
  let all := Array.ofFn f.all
  {
    card := f.card
    all := {
      toFun x := all[x]'(by
        rw [Array.size_ofFn]
        exact x.isLt)
      inj' := by
        intro x y h
        dsimp at h
        rw [Array.getElem_ofFn, Array.getElem_ofFn] at h
        exact f.all.inj h
    }
    complete x := by
      have ⟨i, h⟩ := f.complete x
      exists i
      show x = all[i]'_
      dsimp; rw [Array.getElem_ofFn]
      assumption
  }

private def maxNat (f: Fin n -> Nat) : Nat :=
  Fin.foldl n (fun acc i => max acc (f i)) 0

private def le_maxNat (f: Fin n -> Nat) : ∀i, f i ≤ maxNat f := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i
    unfold Fintype.maxNat
    rw [Fin.foldl_succ_last]
    show f i ≤ max (maxNat _) _
    cases i using Fin.lastCases with
    | last => apply Nat.le_max_right
    | cast i =>
      apply flip Nat.le_trans
      apply Nat.le_max_left
      exact ih (fun i => f i.castSucc) _

def nat_not_fintype : Fintype Nat -> False := by
  intro h
  induction h with | mk h =>
  obtain ⟨card, f, h, _⟩ := h
  let m := maxNat f
  have ⟨i, g⟩ := h (m + 1)
  have : f i ≤ m := le_maxNat f i
  rw [←g] at this
  omega

end Fintype
