import FYP.Graph.Basic
import FYP.Graph.Path
import FYP.Graph.PathLemmas
import FYP.ShortestPath.FloydWarshall

namespace FYP

-- each iteration of FW doesn't increase distances
lemma fwStep_le_self {n : ℕ} (d : Fin n → Fin n → ℕ∞) (k i j : Fin n) :
  fwStep d k i j ≤ d i j := by
  simp [fwStep]

lemma fwStep_le_via_k {n : ℕ} (d : Fin n → Fin n → ℕ∞) (k i j : Fin n) :
  fwStep d k i j ≤ d i k + d k j := by
  simp [fwStep]

lemma fwStep_monotone {n : ℕ} (d : Fin n → Fin n → ℕ∞) (k : Fin n) :
  ∀ i j, fwStep d k i j ≤ d i j := by
  intro i j
  simp [fwStep]

lemma foldl_fwStep_le {n : ℕ} (l : List (Fin n)) :
  ∀ d i j, (l.foldl fwStep d) i j ≤ d i j := by
  induction l with
  | nil =>
    intro d i j
    simp
  | cons k ks ih =>
    intro d i j
    simp only [List.foldl]
    have h1 := ih (fwStep d k) i j
    have h2 := fwStep_le_self d k i j
    exact le_trans h1 h2

lemma fwStep_correct :
  fwStep d k i j = min (d i j) (d i k + d k j) := by
    simp [fwStep]

-- lemma distUpTo_step :
--   distUpTo G k i j =
--     min (distUpTo G (k - 1) i j) (distUpTo G (k - 1) i k + distUpTo G (k - 1) k j) := by
--   sorry

-- lemma fwStep_correct_step {n : ℕ} (G : Graph n) (d : Fin n → Fin n → ℕ∞) (k : Fin n)
--   (h : ∀ i j, d i j = distUpTo G k i j) :
--   ∀all i j, fwStep d k i j = distUpTo G k i j := by
--   sorry

end FYP
