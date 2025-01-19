import Math.Data.Group.Alternating
import Math.Data.Group.Symmetric

def Group.evenperm_emb_perm (n: Nat) : Group.SubgroupEmbedding (Group.EvenPermuatation n) (Group.Permuatation (Fin n)) where
  toFun a := a.val
  inj := Subtype.val_inj
  resp_mul' _ _ := rfl
  resp_inv' _ := rfl

def Group.evenperm_sub_perm (n: Nat) : Group.EvenPermuatation n ⊆ Group.Permuatation (Fin n) :=
  IsSubgroup.ofSub (evenperm_emb_perm n)

def Group.IsoClass.alternating_sub_symmetric (n: Nat) : Group.IsoClass.Alternating n ⊆ Group.IsoClass.Symmetric (Fin n) :=
  Group.evenperm_sub_perm n
