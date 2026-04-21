import FYP.Graph.Basic

namespace FYP

-- Floyd-Warshall Algorithm: Computes shortest paths between all pairs of vertices.
-- Returns a function dist : (i j : Fin n) → Weight that represents the shortest distance.

def initDist {n} (G : Graph n) : Fin n → Fin n → ℕ∞ :=
  fun i j => if i = j then 0 else G.w i j

noncomputable def fwStep {n} (distance : Fin n → Fin n → ℕ∞) (k : Fin n) :
  Fin n → Fin n → ℕ∞ :=
    fun i j => min (distance i j) (distance i k + distance k j)

noncomputable def floydWarshall {n} (G : Graph n) :
  Fin n → Fin n → ℕ∞ :=
    let d0 := initDist G
    (List.finRange n).foldl (fun distance k => fwStep distance k) d0

end FYP
