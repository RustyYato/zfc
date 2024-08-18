axiom lem (p: Prop) : p ∨ ¬p

namespace lem

def not_not { P: Prop } (p: ¬¬P) : P :=
  match lem P with
  | .inl h => h
  | .inr h => (p h).elim

def byContradiction { P: Prop } (p: ¬P -> False) : P := not_not p

def not_and { P Q: Prop } :
  ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  apply Iff.intro
  intro not_and
  cases lem P
  apply Or.inr
  intro q
  apply not_and
  apply And.intro <;> assumption
  apply Or.inl
  assumption
  intro not_or and
  cases and
  cases not_or <;> contradiction

def not_forall { P: α -> Prop } :
  ¬(∀x, P x) ↔ ∃x, ¬P x := by
  apply Iff.intro
  intro not_forall
  apply byContradiction
  intro h
  have := fun x => not_not <| (not_exists.mp h) x
  contradiction
  intro exists_not all
  have ⟨ x, notp ⟩ := exists_not
  apply notp
  exact all x

def not_imp : ¬(P → Q) ↔ P ∧ ¬Q := by
  apply Iff.intro
  intro not_p_imp_q
  cases lem P
  apply And.intro
  assumption
  intro q
  apply not_p_imp_q
  intro
  assumption
  apply False.elim
  apply not_p_imp_q
  intro p
  contradiction
  intro p_and_not_q
  intro f
  apply p_and_not_q.right
  apply f p_and_not_q.left

end lem
