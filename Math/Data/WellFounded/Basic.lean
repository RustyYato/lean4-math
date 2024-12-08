
namespace WellFounded

def wrap {r: α -> α -> Prop} (x: α) (acc: Acc r x) : { x // Acc r x } := ⟨x, acc⟩

instance : WellFoundedRelation { x // Acc r x } where
  rel a b := r a b
  wf := by
    apply WellFounded.intro
    intro ⟨x, accx⟩
    induction accx with
    | intro _ _ ih =>
    apply Acc.intro
    intro ⟨y, accy⟩ r₀
    apply ih
    assumption

def fixFC
  {α : Sort u} {r : α → α → Prop} {C : α → Sort v}
  (f: (x : α) → ((y : α) → r y x → C y) → C x) (x : α) (acc: Acc r x): C x :=
  f x (fun y r => fixFC f y (match acc with | .intro acc r₀ => r₀ y r))
termination_by wrap x acc

@[csimp]
def fixFC_eq_fixF : @fixF = @fixFC := by
  funext α r C f x acc
  induction acc with
  | intro acc _ ih =>
  unfold fixF fixFC
  simp
  congr
  funext y r₀
  apply ih
  assumption

def fixC.{u, v} : {α : Sort u} →
  {C : α → Sort v} → {r : α → α → Prop} → WellFounded r → ((x : α) → ((y : α) → r y x → C y) → C x) → (x : α) → C x :=
fun hwf F x => WellFounded.fixF F x (hwf.apply _)

-- provide a computable version of fix, and override WellFounded.fix
@[csimp]
def fixC_eq_fix : @fix = @fixC := rfl

end WellFounded
