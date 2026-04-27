import FYP.Graph.Path

namespace FYP

-- Floyd-Warshall Algorithm: Computes shortest paths between all pairs of vertices.
-- Returns a function shortestDist : (i j : Fin n) → Weight that represents the shortest distance.

def initDist {n} (G : Graph n) : Fin n → Fin n → ℕ∞ :=
  fun i j => if i = j then 0 else G.w i j

noncomputable def distUpToList (G : Graph n) (l : List (Fin n)) (i j : Fin n) : ℕ∞ :=
  sInf {w | ∃ p,
    isPathFromTo G p i j ∧
    (∀ v ∈ p, v ∈ l ∨ v = i ∨ v = j) ∧
    pathWeight G p = w}

noncomputable def fwStep {n} (distance : Fin n → Fin n → ℕ∞) (k : Fin n) :
  Fin n → Fin n → ℕ∞ :=
    fun i j => min (distance i j) (distance i k + distance k j)

noncomputable def floydWarshall {n} (G : Graph n) :
  Fin n → Fin n → ℕ∞ :=
    let d0 := initDist G
    (List.finRange n).foldl (fun distance k => fwStep distance k) d0

end FYP
