import Math.Function.Basic
import Math.Data.Like.Equiv

class IsEmpty (α: Sort*): Prop where
  elim: α -> False

def elim_empty [IsEmpty α] : α -> β := False.elim ∘ IsEmpty.elim

instance : IsEmpty False := ⟨id⟩
instance : IsEmpty PEmpty := ⟨PEmpty.elim⟩
instance : IsEmpty Empty := ⟨Empty.elim⟩
instance {α: Sort*} {β: α -> Sort*} [Inhabited α] [IsEmpty (β default)] : IsEmpty (∀x, β x) where
  elim f := elim_empty (f default)
instance {α: Type*} {β: α -> Type*} [∀x, IsEmpty (β x)] : IsEmpty ((x: α) × β x) where
  elim f := elim_empty f.2
instance {α: Sort*} {β: α -> Sort*} [∀x, IsEmpty (β x)] : IsEmpty ((x: α) ×' β x) where
  elim f := elim_empty f.2
instance {α: Type*} {β: α -> Type*} [IsEmpty α] : IsEmpty ((x: α) × β x) where
  elim f := elim_empty f.1
instance {α: Sort*} {β: α -> Sort*} [IsEmpty α] : IsEmpty ((x: α) ×' β x) where
  elim f := elim_empty f.1
instance {α: Type*} {β: Type*} [IsEmpty α] : IsEmpty (α × β) where
  elim f := elim_empty f.1
instance {α: Sort*} {β: Sort*} [IsEmpty α] : IsEmpty (α ×' β) where
  elim f := elim_empty f.1
instance {α: Type*} {β: Type*} [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕ β) where
  elim f := (by cases f <;> (rename_i f; exact elim_empty f))
instance {α: Sort*} {β: Sort*} [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕' β) where
  elim f := (by cases f <;> (rename_i f; exact elim_empty f))
instance {α: Prop} {β: Prop} [IsEmpty α] : IsEmpty (α ∧ β) where
  elim f := elim_empty f.1
instance {α: Prop} {β: Prop} [IsEmpty β] : IsEmpty (α ∧ β) where
  elim f := elim_empty f.2
instance {α: Prop} {β: Prop} [IsEmpty α] [IsEmpty β] : IsEmpty (α ∨ β) where
  elim f := (by cases f <;> (rename_i f; exact elim_empty f))
instance {α: Type*} [IsEmpty α] : IsEmpty (ULift α) where
  elim f := (by cases f <;> (rename_i f; exact elim_empty f))
instance {α: Sort*} [IsEmpty α] : IsEmpty (PLift α) where
  elim f := (by cases f <;> (rename_i f; exact elim_empty f))
instance : IsEmpty (Fin 0) where
  elim f := f.elim0
def Function.isEmpty (f: α -> β) [IsEmpty β] : IsEmpty α where
  elim x := elim_empty (f x)

def Function.empty [IsEmpty α] : α -> β := elim_empty
def Function.empty_inj [IsEmpty α] {f: α -> β} : Function.Injective f := by
  intro x; exact elim_empty x
def Function.empty_surj [IsEmpty β] {f: α -> β} : Function.Surjective f := by
  intro x; exact elim_empty x
def Function.empty_bij [IsEmpty α] [IsEmpty β] : Function.Bijective (empty (α := α) (β := β)) :=
  ⟨empty_inj, empty_surj⟩

instance [IsEmpty α] : Subsingleton α where
  allEq x := elim_empty x

instance [IsEmpty α] (β: α -> Sort*) : Subsingleton (∀x, β x) where
  allEq f g := by
    funext x
    exact elim_empty x

instance [IsEmpty α] : Subsingleton (α -> β) := inferInstance

def IsEmpty.ofNotNonempty (h: ¬Nonempty α) : IsEmpty α where
  elim x := h ⟨x⟩

structure Embedding (α β: Sort*) where
  toFun: α -> β
  inj: Function.Injective toFun

infixr:25 " ↪ " => Embedding

structure Equiv (α β: Sort*) where
  toFun: α -> β
  invFun: β -> α
  leftInv: invFun.IsLeftInverse toFun
  rightInv: invFun.IsRightInverse toFun

infixl:25 " ≃ " => Equiv

def Equiv.toFun_inj (h: α ≃ b) : Function.Injective h.toFun := h.leftInv.Injective
def Equiv.invFun_inj (h: α ≃ b) : Function.Injective h.invFun := h.rightInv.Injective

def Equiv.toEmbedding (h: α ≃ β) : α ↪ β where
  toFun := h.toFun
  inj := h.toFun_inj

instance : FunLike (α ↪ β) α β where
  coe e := e.toFun
  coe_inj x y h := by cases x; cases y; congr

instance : IsEmbeddingLike (α ↪ β) α β where
  coe_inj e := e.inj

instance : IsEquivLike (α ≃ β) α β where
  coe e := e.toFun
  inv e := e.invFun
  leftInv e := e.leftInv
  rightInv e := e.rightInv
  inj a b h g := by cases a; cases b; congr

@[refl]
def Embedding.refl : α ↪ α where
  toFun := id
  inj _ _ := id

@[refl]
def Equiv.refl : Equiv α α where
  toFun := id
  invFun := id
  leftInv _ := rfl
  rightInv _ := rfl

def Embedding.trans (h: α ↪ β) (g: β ↪ γ) : α ↪ γ where
  toFun := g ∘ h
  inj := Function.Injective.comp g.inj h.inj

@[symm]
def Equiv.symm (h: Equiv α β) : Equiv β α where
  toFun := h.invFun
  invFun := h.toFun
  leftInv := h.rightInv
  rightInv := h.leftInv

def Equiv.trans (h: Equiv α β) (g: Equiv β γ) : Equiv α γ where
  toFun := g.toFun ∘ h.toFun
  invFun := h.invFun ∘ g.invFun
  leftInv x := by
    dsimp
    rw [g.leftInv, h.leftInv]
  rightInv x := by
    dsimp
    rw [h.rightInv, g.rightInv]

instance [IsEmpty α] : Embedding α β where
  toFun x := elim_empty x
  inj x := elim_empty x

def Equiv.coe_symm (h: α ≃ β) (x: α) : h.symm (h x) = x := h.leftInv _
def Equiv.symm_coe (h: α ≃ β) (x: β) : h (h.symm x) = x := h.rightInv _

def Equiv.inj (h: Equiv α β) : Function.Injective h := by
  intro x y eq
  exact h.toFun_inj eq

def Equiv.symm_inj : Function.Injective (Equiv.symm (α := α) (β := β)) := by
  intro x y eq
  have : x.symm.symm = y.symm.symm := by rw [eq]
  exact this

def Equiv.toFun_inj' : Function.Injective (Equiv.toFun (α := α) (β := β)) := by
  intro x y eq
  suffices x.invFun = y.invFun by
    cases x; cases y
    congr
  funext z
  have : (x.toFun (x.invFun z)) = (y.toFun (y.invFun z)) := by
    rw [x.rightInv, y.rightInv]
  rw [eq] at this
  exact y.toFun_inj this

def Equiv.invFun_inj' : Function.Injective (Equiv.invFun (α := α) (β := β)) := by
  intro x y eq
  apply Equiv.symm_inj
  apply Equiv.toFun_inj'
  assumption

def Equiv.ofBij {f: α -> β} (b: Function.Bijective f) : ∃x: Equiv α β, x = f := by
  have ⟨finv, finvdef⟩ := b.Surjective.exists_inv
  refine ⟨?_, ?_⟩
  apply Equiv.mk f finv _ _
  intro x
  apply b.Injective
  rw [←finvdef]
  intro x
  symm; apply finvdef
  rfl

def Embedding.comp (b: β ↪ γ) (a: α ↪ β) : α ↪ γ where
  toFun := b.toFun ∘ a.toFun
  inj := Function.Injective.comp b.inj a.inj

def Equiv.toProd (h: a ≃ c) (g: b ≃ d) : a × b ≃ c × d where
  toFun | ⟨x, y⟩ => ⟨h x, g y⟩
  invFun | ⟨x, y⟩ => ⟨h.symm x, g.symm y⟩
  leftInv := by
    intro ⟨x, y⟩
    simp [DFunLike.coe, IsEquivLike.coe, Equiv.symm]
    rw [h.leftInv, g.leftInv]
    trivial
  rightInv := by
    intro ⟨x, y⟩
    simp [DFunLike.coe, IsEquivLike.coe, Equiv.symm]
    rw [h.rightInv, g.rightInv]
    trivial

def Prod.equivPProd : (α × β) ≃ α ×' β where
  toFun
  | ⟨a, b⟩ => ⟨a, b⟩
  invFun
  | ⟨a, b⟩ => ⟨a, b⟩
  leftInv
  | ⟨_, _⟩ => rfl
  rightInv
  | ⟨_, _⟩ => rfl
def Prod.equivSigma : (α × β) ≃ (_: α) × β where
  toFun
  | ⟨a, b⟩ => ⟨a, b⟩
  invFun
  | ⟨a, b⟩ => ⟨a, b⟩
  leftInv
  | ⟨_, _⟩ => rfl
  rightInv
  | ⟨_, _⟩ => rfl
def PProd.equivPSigma : (α ×' β) ≃ (_: α) ×' β where
  toFun
  | ⟨a, b⟩ => ⟨a, b⟩
  invFun
  | ⟨a, b⟩ => ⟨a, b⟩
  leftInv
  | ⟨_, _⟩ => rfl
  rightInv
  | ⟨_, _⟩ => rfl
def Prod.equivComm : (α × β) ≃ (β × α) where
  toFun
  | ⟨a, b⟩ => ⟨b, a⟩
  invFun
  | ⟨a, b⟩ => ⟨b, a⟩
  leftInv
  | ⟨_, _⟩ => rfl
  rightInv
  | ⟨_, _⟩ => rfl
def Sum.equivComm : (α ⊕ β) ≃ (β ⊕ α) where
  toFun
  | .inl x => .inr x
  | .inr x => .inl x
  invFun
  | .inl x => .inr x
  | .inr x => .inl x
  leftInv | .inl _ | .inr _ => rfl
  rightInv | .inl _ | .inr _ => rfl
def PSum.equivComm : (α ⊕' β) ≃ (β ⊕' α) where
  toFun
  | .inl x => .inr x
  | .inr x => .inl x
  invFun
  | .inl x => .inr x
  | .inr x => .inl x
  leftInv | .inl _ | .inr _ => rfl
  rightInv | .inl _ | .inr _ => rfl
def PSum.equivCongr (ha: α ≃ α₀) (hb: β ≃ β₀) : (α ⊕' β) ≃ (α₀ ⊕' β₀) where
  toFun
  | .inl x => .inl (ha.toFun x)
  | .inr x => .inr (hb.toFun x)
  invFun
  | .inl x => .inl (ha.invFun x)
  | .inr x => .inr (hb.invFun x)
  leftInv
  | .inl _ => by dsimp; rw [ha.leftInv]
  | .inr _ => by dsimp; rw [hb.leftInv]
  rightInv
  | .inl _ => by dsimp; rw [ha.rightInv]
  | .inr _ => by dsimp; rw [hb.rightInv]
def Sum.equivPSum : (α ⊕ β) ≃ (α ⊕' β) where
  toFun
  | .inl x => .inl x
  | .inr x => .inr x
  invFun
  | .inl x => .inl x
  | .inr x => .inr x
  leftInv | .inl _ | .inr _ => rfl
  rightInv | .inl _ | .inr _ => rfl
def Sum.equivCongr (ha: α ≃ α₀) (hb: β ≃ β₀) : (α ⊕ β) ≃ (α₀ ⊕ β₀) where
  toFun
  | .inl x => .inl (ha.toFun x)
  | .inr x => .inr (hb.toFun x)
  invFun
  | .inl x => .inl (ha.invFun x)
  | .inr x => .inr (hb.invFun x)
  leftInv
  | .inl _ => by dsimp; rw [ha.leftInv]
  | .inr _ => by dsimp; rw [hb.leftInv]
  rightInv
  | .inl _ => by dsimp; rw [ha.rightInv]
  | .inr _ => by dsimp; rw [hb.rightInv]
def Fin.equivOfEq (h: n = m) : Fin n ≃ Fin m where
  toFun x := x.cast h
  invFun x := x.cast h.symm
  leftInv | ⟨_, _⟩ => rfl
  rightInv | ⟨_, _⟩ => rfl

def Equiv.symm_trans_self (h: α ≃ β) : h.symm.trans h = Equiv.refl := by
  apply Equiv.toFun_inj'
  ext x
  show h (h.symm x) = x
  rw [h.symm_coe]

def Equiv.heq_invFun_left {a: α ≃ β} {b: α₀ ≃ β} (h: HEq a b) : α = α₀ -> ∀x, HEq (a.invFun x) (b.invFun x) := by
  intro eq
  subst α₀
  cases h
  intro x
  rfl
def Equiv.heq_toFun_left {a: α ≃ β} {b: α₀ ≃ β₀} (hb: HEq β β₀) (h: HEq a b) : α = α₀ -> ∀x x₀, HEq x x₀ -> HEq (a.toFun x) (b.toFun x₀) := by
  intro eq
  intro x x₀ eq
  cases eq
  cases hb
  cases h
  rfl

def PSigma.equivCongr {β: α -> Sort*} {β₀: α₀ -> Sort*} (ha: α ≃ α₀) (hb: ∀x x₀, x₀ = ha.toFun x -> β x ≃ β₀ x₀) :
  (x: α) ×' β x ≃ (x: α₀) ×' β₀ x where
  toFun | ⟨a, b⟩ => ⟨ha.toFun a, (hb _ _ rfl).toFun b⟩
  invFun | ⟨a, b⟩ => ⟨ha.invFun a, by
    apply (hb (ha.invFun a) _ _).invFun
    exact b
    rw [ha.rightInv]⟩
  leftInv := by
    intro ⟨a, b⟩
    dsimp
    congr
    rw [ha.leftInv]
    apply HEq.trans
    apply Equiv.heq_invFun_left
    show HEq _ (hb a (ha.toFun a) rfl)
    congr 1
    rw [ha.leftInv]
    apply proof_irrel_heq
    rw [ha.leftInv]
    rw [(hb  _ _ _).leftInv]
  rightInv := by
    intro ⟨a, b⟩
    dsimp
    congr
    rw [ha.rightInv]
    apply HEq.trans
    apply Equiv.heq_toFun_left _
    show HEq _ (hb (ha.invFun a) a (ha.rightInv _).symm)
    congr
    rw [ha.rightInv]
    apply proof_irrel_heq
    rfl
    rfl
    rw [ha.rightInv]
    rw [(hb _ _ _).rightInv]

def Sigma.equivPSigma {β: α -> Type*} :
  (x: α) × β x ≃ (x: α) ×' β x where
  toFun | ⟨a, b⟩ => ⟨a, b⟩
  invFun | ⟨a, b⟩ => ⟨a, b⟩
  leftInv _ := rfl
  rightInv _ := rfl

def Sigma.equivCongr {β: α -> Type*} {β₀: α₀ -> Type*} (ha: α ≃ α₀) (hb: ∀x x₀, x₀ = ha.toFun x -> β x ≃ β₀ x₀) :
  (x: α) × β x ≃ (x: α₀) × β₀ x := by
  apply Equiv.trans Sigma.equivPSigma
  apply Equiv.trans _ Sigma.equivPSigma.symm
  apply PSigma.equivCongr
  assumption

def PProd.equivCongr (ha: α ≃ α₀) (hb: β ≃ β₀) :
  α ×' β ≃ α₀ ×' β₀ := by
  apply Equiv.trans PProd.equivPSigma
  apply Equiv.trans _ PProd.equivPSigma.symm
  apply PSigma.equivCongr
  intro x x₀ eq
  assumption
  assumption

def Prod.equivCongr (ha: α ≃ α₀) (hb: β ≃ β₀) :
  α × β ≃ α₀ × β₀ := by
  apply Equiv.trans Prod.equivSigma
  apply Equiv.trans _ Prod.equivSigma.symm
  apply Sigma.equivCongr
  intro x x₀ eq
  assumption
  assumption

def cast_eq_of_heq' {β: α -> Sort _}
  {a: β x}
  {b: β y}
  (h: HEq a b) (g: x = y) : g ▸ a = b := by
  cases g
  cases h
  rfl

def Pi.congrEquiv {β₀: α₀ -> Sort _} {β₁: α₁ -> Sort _}
  (h: α₀ ≃ α₁) (g: ∀x, β₀ x ≃ β₁ (h.toFun x)) : (∀x, β₀ x) ≃ (∀x, β₁ x) where
  toFun f x := h.rightInv x ▸ (g _).toFun (f (h.invFun x))
  invFun f x := (g _).invFun (f (h.toFun x))
  leftInv f := by
    funext x
    dsimp
    apply (g x).toFun_inj
    rw [(g x).rightInv]
    apply cast_eq_of_heq'
    rw [h.leftInv]
  rightInv f := by
    funext x
    dsimp
    apply cast_eq_of_heq'
    rw [(g _).rightInv, h.rightInv]

def Function.congrEquiv (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ -> β₀) ≃ (α₁ -> β₁) := by
  apply Pi.congrEquiv
  intro
  assumption
  assumption

def Char.equivSubtype : Char ≃ { x : UInt32 // x.isValidChar } where
  toFun | ⟨x, p⟩ => ⟨x, p⟩
  invFun | ⟨x, p⟩ => ⟨x, p⟩
  leftInv _ := rfl
  rightInv _ := rfl

def UInt8.equivFin : UInt8 ≃ Fin (2^8) where
  toFun | ⟨⟨x⟩⟩ => x
  invFun x := ⟨⟨x⟩⟩
  leftInv _ := rfl
  rightInv _ := rfl

def UInt16.equivFin : UInt16 ≃ Fin (2^16) where
  toFun | ⟨⟨x⟩⟩ => x
  invFun x := ⟨⟨x⟩⟩
  leftInv _ := rfl
  rightInv _ := rfl

def UInt32.equivFin : UInt32 ≃ Fin (2^32) where
  toFun | ⟨⟨x⟩⟩ => x
  invFun x := ⟨⟨x⟩⟩
  leftInv _ := rfl
  rightInv _ := rfl

def UInt64.equivFin : UInt64 ≃ Fin (2^64) where
  toFun | ⟨⟨x⟩⟩ => x
  invFun x := ⟨⟨x⟩⟩
  leftInv _ := rfl
  rightInv _ := rfl

def Except.equivSum : Except α β ≃ α ⊕ β where
  toFun
  | .ok x => .inr x
  | .error x => .inl x
  invFun
  | .inr x => .ok x
  | .inl x => .error x
  leftInv | .ok _ | .error _ => rfl
  rightInv | .inl _ | .inr _ => rfl

def ULift.equiv : ULift α ≃ α where
  toFun | ⟨x⟩ => x
  invFun x := ⟨x⟩
  leftInv | ⟨_⟩ => rfl
  rightInv _ := rfl

def ULift.equivCongr (h: α ≃ β) : ULift α ≃ ULift β :=
  (ULift.equiv.trans h).trans ULift.equiv.symm

def PLift.equiv : PLift α ≃ α where
  toFun | ⟨x⟩ => x
  invFun x := ⟨x⟩
  leftInv | ⟨_⟩ => rfl
  rightInv _ := rfl

def Array.equivList : Array α ≃ List α where
  toFun | ⟨x⟩ => x
  invFun x := ⟨x⟩
  leftInv | ⟨_⟩ => rfl
  rightInv _ := rfl

def Subtype.congrEquiv { α β: Sort _ } {P: α -> Prop} {Q: β -> Prop}
  (h: α ≃ β)
  (iff: ∀{x}, P x ↔ Q (h.toFun x))
  : Subtype P ≃ Subtype Q where
  toFun | ⟨x, prop⟩ => ⟨h.toFun x, iff.mp prop⟩
  invFun | ⟨x, prop⟩ => ⟨h.invFun x, by
    apply iff.mpr
    rw [h.rightInv]
    exact prop⟩
  leftInv
  | ⟨_, _⟩ => by
    dsimp; congr
    rw [h.leftInv]
  rightInv
  | ⟨_, _⟩ => by
    dsimp; congr
    rw [h.rightInv]

def Embedding.equivSubtype : (α ↪ β) ≃ { x: α -> β // x.Injective } where
  toFun | ⟨a, b⟩ => ⟨a, b⟩
  invFun | ⟨a, b⟩ => ⟨a, b⟩
  leftInv _ := rfl
  rightInv _ := rfl

def Equiv.equivSubtype {α β: Type*} : (α ≃ β) ≃ { x: (α -> β) × (β -> α) // x.1.IsLeftInverse x.2 ∧ x.1.IsRightInverse x.2 } where
  toFun | ⟨f, g, l, r⟩ => ⟨⟨f, g⟩, r, l⟩
  invFun | ⟨⟨f, g⟩, l, r⟩ => ⟨f, g, r, l⟩
  leftInv _ := rfl
  rightInv| ⟨⟨_, _⟩, _, _⟩ => rfl

def Embedding.congr (emb: α ↪ β) (eqa: α ≃ α₀) (eqb: β ≃ β₀) : α₀ ↪ β₀ where
  toFun := eqb.toFun ∘ emb.toFun ∘ eqa.invFun
  inj := by
    apply Function.Injective.comp
    apply eqb.toFun_inj
    apply Function.Injective.comp
    apply emb.inj
    apply eqa.invFun_inj

def Embedding.congr_apply (emb: α ↪ β) (eqa: α ≃ α₀) (eqb: β ≃ β₀): (emb.congr eqa eqb) x = eqb (emb (eqa.symm x)) := rfl

def Fin.embedNat : Fin n ↪ Nat where
  toFun := Fin.val
  inj {_ _} := Fin.val_inj.mp

def Fin.embedFin (h: n ≤ m) : Fin n ↪ Fin m where
  toFun x := x.castLE h
  inj := by
    intro ⟨x, _⟩ ⟨y, _⟩ eq
    cases eq
    rfl

def Subtype.embed {P: α -> Prop} : Subtype P ↪ α where
  toFun := Subtype.val
  inj {a b} eq := by
    cases a; cases b
    congr

def Subtype.val_inj {P: α -> Prop} : Function.Injective (Subtype.val (p := P)) :=
  Subtype.embed.inj

def empty_equiv_empty (α β: Sort*) [IsEmpty α] [IsEmpty β] : α ≃ β where
  toFun x := elim_empty x
  invFun x := elim_empty x
  leftInv x := elim_empty x
  rightInv x := elim_empty x

def unique_eq_unique (α β: Sort*) [Subsingleton α] [Subsingleton β] [Inhabited α] [Inhabited β] : α ≃ β where
  toFun _ := default
  invFun _ := default
  leftInv _ := Subsingleton.allEq _ _
  rightInv _ := Subsingleton.allEq _ _

def empty_inj [IsEmpty α] (f: α -> β) : Function.Injective f := fun x => elim_empty x

def Option.congrEquiv (h: α ≃ β) : Option α ≃ Option β where
  toFun
  | .some x => .some (h x)
  | .none => .none
  invFun
  | .some x => .some (h.symm x)
  | .none => .none
  leftInv := by
    intro x
    cases x
    rfl
    dsimp
    rw [h.coe_symm]
  rightInv := by
    intro x
    cases x
    rfl
    dsimp
    rw [h.symm_coe]

def Fin.equivSubtype (n: Nat) : Fin n ≃ Subtype (· < n) where
  toFun | ⟨x, h⟩ => ⟨x, h⟩
  invFun | ⟨x, h⟩ => ⟨x, h⟩
  leftInv _ := rfl
  rightInv _ := rfl

def Fin.embed_reduce (emb: α ↪ Fin n) (x: Fin n) (h: ∀a, emb a ≠ x) : α ↪ Fin n.pred where
  toFun a :=
    if g:(emb a).val = n.pred then by
      refine ⟨x.val, ?_⟩
      apply Nat.lt_of_le_of_ne
      apply Nat.le_of_lt_succ
      rw [Nat.succ_pred]
      exact x.isLt
      intro h
      exact Nat.not_lt_zero x.val (h ▸ x.isLt)
      rw [←g, Fin.val_inj]
      apply Ne.symm
      apply h
    else by
      refine ⟨(emb a).val, ?_⟩
      apply Nat.lt_of_le_of_ne
      apply Nat.le_of_lt_succ
      rw [Nat.succ_pred]
      apply Fin.isLt
      intro h
      exact Nat.not_lt_zero x.val (h ▸ x.isLt)
      assumption
  inj := by
    intro a b eq
    dsimp at eq
    split at eq <;> split at eq <;> rename_i g₀ g₁
    exact emb.inj <| Fin.val_inj.mp (g₀.trans g₁.symm)
    have := Fin.val_inj.mp (Fin.mk.inj eq)
    have := h _ this.symm
    contradiction
    have := Fin.val_inj.mp (Fin.mk.inj eq)
    have := h _ this
    contradiction
    exact emb.inj <| Fin.val_inj.mp (Fin.mk.inj eq)

instance [IsEmpty α] : Subsingleton (Option α) where
  allEq := by
    intro a b
    cases a; cases b
    rfl
    rename_i x
    exact elim_empty x
    rename_i x
    exact elim_empty x

def empty_or_nonempty {motive: Sort u -> Prop} (empty: ∀t, IsEmpty t -> motive t) (nonempty: ∀t, Nonempty t -> motive t) : ∀t, motive t := by
  intro t
  by_cases h:Nonempty t
  apply nonempty
  assumption
  apply empty
  exact IsEmpty.ofNotNonempty h

def Embedding.ofOptionEmbed (emb: Option α ↪ Option β) : α ↪ β where
  toFun a :=
    match h:emb a with
    | .some x => x
    | .none => (emb .none).get <| by
      cases g:emb .none
      have := emb.inj (h.trans g.symm)
      contradiction
      rfl
  inj := by
    intro x y eq
    dsimp at eq
    split at eq <;> split at eq
    rename_i h₀ _ h₁
    subst eq
    exact Option.some.inj <| emb.inj (h₀.trans h₁.symm)
    subst eq
    rename_i h₀ h₁
    rw [Option.some_get] at h₁
    have := emb.inj h₁; contradiction
    rename_i h₀ eq h₁; subst eq
    rw [Option.some_get] at h₁
    have := emb.inj h₁; contradiction
    rename_i h₀ h₁
    exact Option.some.inj <| emb.inj (h₀.trans h₁.symm)

def Embedding.toOptionEmbed (emb: α ↪ β) : Option α ↪ Option β where
  toFun
  | .some x => emb x
  | .none => .none
  inj := by
    intro x y eq
    dsimp at eq
    split at eq <;> split at eq
    rw [emb.inj <| Option.some.inj eq]
    contradiction
    contradiction
    rfl

def Embedding.DecidableEq (emb: α ↪ β) [DecidableEq β] : DecidableEq α :=
  fun a b =>
  match inferInstanceAs (Decidable (emb a = emb b)) with
  | .isTrue h => .isTrue (emb.inj h)
  | .isFalse h => .isFalse fun g => h (g ▸ rfl)

def Option.embed : α ↪ Option α where
  toFun := some
  inj _ _ := Option.some.inj

def Option.swapULift.{u} : ULift.{u} (Option α) ≃ Option (ULift.{u} α) where
  toFun x := x.down.map ULift.up
  invFun x := ⟨x.map ULift.down⟩
  leftInv := by intro ⟨x⟩; cases x <;> rfl
  rightInv := by intro x; cases x <;> rfl
