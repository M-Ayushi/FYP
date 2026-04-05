import FYP.Graph.Basic

namespace FYP

lemma two_list_membership {n : ℕ} (i j : Fin n) :
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

end FYP
