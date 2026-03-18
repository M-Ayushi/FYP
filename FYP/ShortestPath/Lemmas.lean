import FYP.Graph.Basic
import FYP.Graph.Path
import FYP.ShortestPath.FloydWarshall

namespace FYP

-- each iteration of FW doesn't increase distances
lemma fwStep_le_self {n : ℕ} (d : Fin n → Fin n → ℕ∞) (k i j : Fin n) :
  fwStep d k i j ≤ d i j := by
  simp [fwStep]

lemma fwStep_le_via_k {n : ℕ} (d : Fin n → Fin n → ℕ∞) (k i j : Fin n) :
  fwStep d k i j ≤ d i k + d k j := by
  simp [fwStep]

-- lemma fwStep_monotone {n : ℕ} (d : Fin n → Fin n → ℕ∞) (k : Fin n) :
--   ∀ i j, fwStep d k i j ≤ d i j := by
--   sorry

lemma foldl_fwStep_le {n : ℕ} (l : List (Fin n)) : --(d : Fin n → Fin n → ℕ∞) :
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


end FYP
