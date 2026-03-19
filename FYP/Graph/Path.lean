import FYP.Graph.Basic
import Mathlib.Data.List.Basic

namespace FYP

-- A path is a sequence of vertices
def Path (n : ℕ) := List (Fin n)

def validPath {n : ℕ} (G : Graph n) : Path n → Prop
  | [] => False
  | [_] => True
  | (u :: v :: rest) =>
      G.w u v ≠ ⊤ ∧ validPath G (v :: rest)

-- Compute weight of a path by summing edge weights
def pathDistance {n : ℕ} (G : Graph n) (p : Path n) : ℕ∞ :=
  match p with
  | [] => 0
  | [_] => 0  -- single vertex has distance 0
  | u :: v :: rest =>
      G.w u v + pathDistance G (v :: rest)
-- termination_by p.length

-- Shortest distance between two vertices considering all possible paths
def shortestDistance {n : ℕ} (G : Graph n) (i j : Fin n) : ℕ∞ :=
  if i = j then 0
  else
    -- For now, use a simple definition
    -- True definition would compute infimum over all paths from i to j
    G.w i j

end FYP
