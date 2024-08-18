def WellFounded.irrefl {r: α -> α -> Prop} (wf: WellFounded r) : ¬r a a := by
  induction a using wf.induction with
  | h a' ih =>
  intro rel
  apply ih <;> assumption

def WellFounded.asymm {r: α -> α -> Prop} (wf: WellFounded r) : r a b -> ¬r b a := by
  intro ab ba
  induction b using wf.induction generalizing a with
  | h a' ih => exact ih a ab ba ab

def WellFounded.no_cycle { r: α -> α -> Prop } (wf: WellFounded r) :
  Relation.TransGen r a a -> False := by
  intro rel
  exact wf.transGen.irrefl rel
