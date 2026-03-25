import FYP.Graph.Basic
import FYP.Graph.Path
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold

namespace FYP

-- Floyd-Warshall Algorithm: Computes shortest paths between all pairs of vertices.
-- Returns a function dist : (i j : Fin n) → Weight that represents the shortest distance.

def initDist {n : ℕ} (G : Graph n) : Fin n → Fin n → ℕ∞ :=
  fun i j => if i = j then 0 else G.w i j

noncomputable def fwStep {n : ℕ}
  (d : Fin n → Fin n → ℕ∞)
  (k : Fin n) :
  Fin n → Fin n → ℕ∞ :=
  fun i j => min (d i j) (d i k + d k j)

noncomputable def floydWarshall {n : ℕ} (G : Graph n) : Fin n → Fin n → ℕ∞ :=
  let d0 := initDist G
  (List.finRange n).foldl (fun d k => fwStep d k) d0

theorem floydWarshall_correct (G : Graph n) (i j : Fin n) :
  floydWarshall G i j = dist G i j := by
  sorry

end FYP
