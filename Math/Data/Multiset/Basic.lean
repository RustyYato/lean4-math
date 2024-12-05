import Math.Data.QuotLike.Basic
import Math.Type.Notation
import Math.Data.List.Basic
import Math.Function.Basic
import Math.AxiomBlame

def Multiset (α: Type*) := Quotient (List.isSetoid α)
instance : QuotientLike (List.isSetoid α) (Multiset α) where

local notation "⟦" a "⟧" => (QuotLike.mk (a: List _): Multiset _)

instance : EmptyCollection (Multiset α) := ⟨⟦[]⟧⟩

def Multiset.toList : Multiset α -> List α := unwrapQuot

def Multiset.mem (x: α) : Multiset α -> Prop := Quot.lift (x ∈ ·) <| by
  intro x y eq
  exact propext eq.mem_iff

instance : Membership α (Multiset α) := ⟨flip Multiset.mem⟩

def Multiset.MinCount (x: α) (n: Nat) : Multiset α -> Prop := Quot.lift (List.MinCount · x n) <| by
  intro x y eq
  dsimp
  exact propext eq.min_count_iff

instance : Membership α (Multiset α) := ⟨flip Multiset.mem⟩

@[simp]
def Multiset.mk_mem (x: α) (as: List α) : (x ∈ ⟦as⟧) = (x ∈ as) := rfl

def Multiset.cons (x: α) : Multiset α -> Multiset α := Quot.lift (⟦List.cons x ·⟧) <| by
  intro x y eq
  apply quot.sound
  apply List.Perm.cons
  assumption

infix:67 " ::ₘ " => Multiset.cons

instance : Insert α (Multiset α) := ⟨.cons⟩
instance : Singleton α (Multiset α) := ⟨(.cons · ∅)⟩

@[simp]
def Multiset.mk_cons (x: α) (as: List α) : x ::ₘ ⟦as⟧ = ⟦x::as⟧ := rfl

@[simp]
def Multiset.mem_cons {a: α} {as: Multiset α} : ∀{x}, x ∈ a::ₘas ↔ x = a ∨ x ∈ as := by
  intro x
  quot_ind as
  simp

def Multiset.append : Multiset α -> Multiset α -> Multiset α := by
  apply Quotient.lift₂ (⟦· ++ ·⟧)
  intro a b c d ac bd
  apply quot.sound
  apply List.Perm.append <;> assumption

instance : Append (Multiset α) := ⟨.append⟩

@[simp]
def Multiset.mk_append (as bs: List α) : ⟦as⟧ ++ ⟦bs⟧ = ⟦as ++ bs⟧ := rfl

@[simp]
def Multiset.mem_append {as bs: Multiset α} : ∀{x}, x ∈ as ++ bs ↔ x ∈ as ∨ x ∈ bs := by
  intro x
  quot_ind (as bs)
  simp

def Multiset.append_comm (as bs: Multiset α) : as ++ bs = bs ++ as := by
  quot_ind (as bs)
  simp
  apply quot.sound
  apply List.perm_append_comm
def Multiset.append_assoc (as bs cs: Multiset α) : as ++ bs ++ cs = as ++ (bs ++ cs) := by
  quot_ind (as bs cs)
  simp

def Multiset.map {β: Type _} (f: α -> β) (as: Multiset α) : Multiset β := by
  apply Quot.lift (⟦·.map f⟧) _ as
  intro a b h
  apply quot.sound
  induction h with
  | nil => apply List.Perm.nil
  | trans _ _ aih bih => apply aih.trans bih
  | cons a _ ih =>
    apply List.Perm.cons
    assumption
  | swap => apply List.Perm.swap

@[simp]
def Multiset.mk_map (a: List α) (f: α -> β) : ⟦a⟧.map f = ⟦a.map f⟧ := rfl

def Multiset.flatten (as: Multiset (Multiset α)) : Multiset α := by
  apply Quot.lift _ _ as
  intro xs
  exact xs.foldr (· ++ ·) ∅
  intro a b aeqb
  induction aeqb with
  | nil => rfl
  | cons a as ih =>
    unfold List.foldr
    congr
  | trans _ _ aih bih => rw [aih, bih]
  | swap a as ih =>
    unfold List.foldr
    unfold List.foldr
    rw [←append_assoc, ←append_assoc, append_comm a]

@[simp]
def Multiset.mk_flatten (as: List (List α)) : ⟦as.map (⟦·⟧)⟧.flatten = ⟦as.flatten⟧ := by
  unfold flatten
  show List.foldr _ _ _ = _
  rw [List.foldr_map]
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

def Multiset.mk_flatten' (as: List (Multiset α)) : ⟦as⟧.flatten = ⟦(as.map unwrapQuot).flatten⟧ := by
  rw [←mk_flatten]
  congr
  rw [List.map_map, List.map_id'']
  apply mk_unwrapQuot

def Multiset.flatMap {β: Type _} (f: α -> Multiset β) (as: Multiset α) : Multiset β :=
  (as.map f).flatten

def Multiset.flatten_cons (a: Multiset α) (as: Multiset (Multiset α)) : (a::ₘas).flatten = a ++ as.flatten := by
  quot_ind (a as)
  rfl

@[simp]
def Multiset.mk_flatMap (as: List α) (f: α -> List β) : ⟦as⟧.flatMap (fun x => ⟦f x⟧) = ⟦as.flatMap f⟧ := by
  unfold flatMap
  rw [mk_map]
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp [ih, ←mk_cons, flatten_cons]

def Multiset.mk_flatMap' (as: List α) (f: α -> Multiset β) : ⟦as⟧.flatMap f = ⟦as.flatMap (unwrapQuot ∘ f)⟧ := by
  rw [←mk_flatMap]
  congr
  funext
  symm
  apply mk_unwrapQuot

def Multiset.flatMap_cons (a: α) (as: Multiset α) (f: α -> Multiset β) : (a::ₘas).flatMap f = f a ++ as.flatMap f := by
  quot_ind as
  simp
  rfl

def Multiset.map_append (as bs: Multiset α) (f: α -> β) : (as ++ bs).map f = as.map f ++ bs.map f := by
  quot_ind (as bs)
  simp

def Multiset.rec' {motive: Multiset α -> Sort _}
  (nil: motive ∅) (cons: ∀a as, motive as -> motive (a::ₘas)) :
  ∀ms, motive ⟦ms⟧ := by
  intro ms
  match ms with
  | [] => exact nil
  | m::ms =>
    show motive (m::ₘ⟦ms⟧)
    apply cons
    apply rec'
    assumption
    assumption

def cast_eq_of_heq (h: α = β) (a: α) (b: β): HEq a b -> h ▸ a = b := by
  intro h
  cases h
  rfl

def rec_prf_cons {x as bs}
  {motive: Multiset α -> Sort u}
  {cons: ∀a as, motive as -> motive (a::ₘas)}
  (as_eq_bs: as = bs)
  (mas: motive as)
  (mbs: motive bs):
  HEq mas mbs -> HEq (cons x as mas) (cons x bs mbs) := by
  intro eq
  subst bs
  cases eq
  rfl

def Multiset.rec {motive: Multiset α -> Sort _}
  (nil: motive ∅) (cons: ∀a as, motive as -> motive (a::ₘas))
  (swap: ∀a a' as mas, HEq (cons a _ (cons a' as mas)) (cons a' _ (cons a as mas))) :
  ∀ms, motive ms := by
  intro ms
  apply Quot.hrecOn ms
  case f =>
    intro ms
    apply Multiset.rec' <;> assumption
  intro a b a_perm_b
  induction a_perm_b with
  | nil => rfl
  | trans _ _ aih bih => exact aih.trans bih
  | cons _ _ ih =>
    unfold rec'
    dsimp
    apply rec_prf_cons
    apply quot.sound
    assumption
    assumption
  | swap =>
    unfold rec' rec'
    dsimp
    rename_i x y as
    apply swap (a := y) (a' := x) (as := ⟦as⟧)

def Multiset.map_map (ms: Multiset α) (f: α -> β) (g: β -> γ) : (ms.map f).map g = ms.map (g ∘ f) := by
  quot_ind ms
  apply quot.sound
  simp
  induction ms with
  | nil => apply List.Perm.nil
  | cons m ms ih =>
    apply List.Perm.cons
    apply ih

def Multiset.flatMap_map (ms: Multiset α) (f: α -> Multiset β) (g: β -> γ) : (ms.flatMap f).map g = ms.flatMap (fun x => (f x).map g) := by
  quot_ind ms
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp [flatMap_cons, ←mk_cons, map_append]
    congr

theorem Multiset.flatMap_congr {ms : Multiset α} {f f': α → Multiset β}
  (hf : ∀ a ∈ ms, (f a) = (f' a)) : ms.flatMap f = ms.flatMap f' := by
  quot_ind ms
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp [←mk_cons, flatMap_cons]
    congr 1
    apply hf
    apply List.Mem.head
    apply ih
    intro a ha
    apply hf
    apply List.Mem.tail
    assumption

theorem Multiset.flatMap_hcongr {β' : Type v} {m : Multiset α} {f : α → Multiset β} {f' : α → Multiset β'}
    (h : β = β') (hf : ∀ a ∈ m, HEq (f a) (f' a)) : HEq (m.flatMap f) (m.flatMap f') := by
  subst h
  simp only [heq_eq_eq] at hf
  simp [flatMap_congr hf]

instance [DecidableEq α] : DecidableEq (Multiset α) := Quotient.decidableEq

def Multiset.of_count_cons {x a: α} {as: Multiset α} {n: Nat} :
  (a::ₘas).MinCount x n -> as.MinCount x n ∨ (n ≠ 0 ∧ x = a ∧ as.MinCount a n.pred) := by
  quot_ind as
  intro h
  cases h
  left
  assumption
  right
  apply And.intro
  exact Nat.noConfusion
  apply And.intro rfl
  assumption

def Multiset.MinCount.zero : MinCount x 0 ms := by
  quot_ind ms
  apply List.MinCount.zero

def Multiset.MinCount.head : MinCount x n ms -> MinCount x n.succ (x::ₘms) := by
  quot_ind ms
  intro c
  apply List.MinCount.head
  assumption

def Multiset.MinCount.cons : MinCount x n ms -> MinCount x n (m::ₘms) := by
  quot_ind ms
  intro c
  apply List.MinCount.cons
  assumption

-- theorem Multiset.flatMap_flatMap {m : Multiset α} {n: Multiset β} {f : α → β -> Multiset γ} :
--   m.flatMap (fun a => n.flatMap (fun b => f a b)) = n.flatMap (fun b => m.flatMap (fun a => f a b)) := by
--   quot_ind (m n)
--   induction m generalizing n with
--   | nil =>
--     show ∅ = _
--     symm
--     show flatMap (fun _ => ∅) _ = ∅
--     induction n with
--     | nil => rfl
--     | cons n ns ih =>
--       simp [ih, flatMap_cons, ←mk_cons]
--       rfl
--   | cons m ms ih =>
--     cases n
--     simp [ih, flatMap_cons, ←mk_cons]
--     rfl
--     rw [←mk_cons, flatMap_cons]
--     rw [←mk_cons, flatMap_cons]
--     rw [flatMap_cons]
--     rw [flatMap_cons]
--     simp [append_assoc]
--     congr 1
--     rw [ih]
--     rw [←mk_cons, flatMap_cons]
--     rw [←append_assoc, append_comm (flatMap _ _), append_assoc]
--     congr 1
--     sorry

-- theorem bind_bind (m : Multiset α) (n : Multiset β) {f : α → β → Multiset γ} :
--     ((bind m) fun a => (bind n) fun b => f a b) = (bind n) fun b => (bind m) fun a => f a b :=
