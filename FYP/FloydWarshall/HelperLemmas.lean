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

lemma add_min : ∀ (a b c : ℕ∞), a + min b c = min (a + b) (a + c) := by
    intros a b c
    rcases le_or_gt b c with h | h
    · simp only [min_eq_left h, left_eq_inf]
      exact add_le_add_right h a
    · simp only [min_eq_right h.le, right_eq_inf]
      apply add_le_add_right h.le a

lemma takeWhile_drop_split {α : Type} [DecidableEq α]
  (k : α) (p : List α) (h : k ∈ p) :
  let p1 := List.takeWhile (fun v => v ≠ k) p
  let p2 := List.drop (p1.length + 1) p
  p = p1 ++ [k] ++ p2 := by
  induction p with
  | nil =>
      simp at h
  | cons hd tl ih =>
      by_cases h_hd : hd = k
      · -- k is at the head
        simp [h_hd]
      · -- k is in tail
        have h_tl : k ∈ tl := by
          simp only [List.mem_cons] at h
          cases h with
          | inl h_eq =>
            cases h_hd (Eq.symm h_eq)
          | inr h_in =>
            exact h_in
        specialize ih h_tl
        simp only [List.mem_cons, h_hd, not_false_eq_true, ne_eq,
                  decide_not, List.append_assoc, List.cons_append,
                  List.nil_append, List.takeWhile, decide_true,
                  List.length_cons, List.drop_succ_cons,
                  List.cons.injEq, true_and] at *
        exact ih

end FYP
