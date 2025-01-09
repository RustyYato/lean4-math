noncomputable
def Quot.out {r: α -> α -> Prop} (q: Quot r) : α := Classical.choose q.exists_rep
noncomputable
def Quotient.out {s: Setoid α} (q: Quotient s) : α := Quot.out q

noncomputable
def Quot.out_spec {r: α -> α -> Prop} (q: Quot r) : Quot.mk r q.out = q := Classical.choose_spec q.exists_rep
noncomputable
def Quotient.out_spec {s: Setoid α} (q: Quotient s) : Quotient.mk s q.out = q := Quot.out_spec q
