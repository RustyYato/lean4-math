class Fact (P: Prop) where
  proof: P

def of_fact (P: Prop) [f: Fact P] : P := f.proof
