import FYP.Graph.Basic

namespace FYP

lemma mem_pair_iff {n : ℕ} (i j : Fin n) :
 ∀ v ∈ [i, j], v = i ∨ v = j := by
  intro v hv
  cases List.mem_cons.mp hv with
  | inl h1 =>
    left
    rw [h1]
  | inr h2 =>
    right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
    exact h2

-- TODO : might not be necessary
lemma add_min : ∀ (a b c : ℕ∞), a + min b c = min (a + b) (a + c) := by
    intros a b c
    rcases le_or_gt b c with h | h
    · simp only [min_eq_left h, left_eq_inf]
      exact add_le_add_right h a
    · simp only [min_eq_right h.le, right_eq_inf]
      apply add_le_add_right h.le a

end FYP
