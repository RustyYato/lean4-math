

inductive Relation.ReflTransGen (r: α -> α -> Prop) : α -> α -> Prop where
| refl : ReflTransGen r a a
| cons : r a b -> ReflTransGen r b c -> ReflTransGen r a c

namespace Relation.ReflTransGen

def single (x: r a b) : ReflTransGen r a b := by
  apply ReflTransGen.cons x
  apply ReflTransGen.refl

def trans (x: ReflTransGen r a b) (y: ReflTransGen r b c) : ReflTransGen r a c := by
  induction x with
  | refl => assumption
  | cons ab bc ih =>
    apply ReflTransGen.cons
    assumption
    apply ih
    assumption

end Relation.ReflTransGen
