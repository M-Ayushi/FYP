import FYP.Graph.Basic
import Mathlib.Data.List.Basic

namespace FYP

-- A path is a sequence of vertices
def Path (n : ℕ) := List (Fin n)

-- A path is valid if every consecutive pair of vertices has an edge in the graph.
def validPath {n : ℕ} (G : Graph n) : Path n → Prop
  | [] => False
  | [_] => True
  | (u :: v :: rest) =>
      G.w u v ≠ ⊤ ∧ validPath G (v :: rest)

def pathStart {n : ℕ} : Path n → Option (Fin n)
  | [] => none
  | v :: _ => some v

def pathEnd {n : ℕ} : Path n → Option (Fin n)
  | [] => none
  | [v] => some v
  | _ :: rest => pathEnd rest

-- Compute weight of a path by summing edge weights
def pathWeight {n : ℕ} (G : Graph n) : Path n → ℕ∞
  | [] => 0
  | [_] => 0  -- single vertex has weight 0
  | (u :: v :: rest) =>
      G.w u v + pathWeight G (v :: rest)
-- termination_by p.length

def pathsBetween {n : ℕ} (G : Graph n) (i j : Fin n) :=
  {
    p : Path n |
    validPath G p ∧
    pathStart p = some i ∧
    pathEnd p = some j
  }

-- Shortest distance between two vertices considering all possible paths
def shortestDist {n : ℕ} (G : Graph n) (i j : Fin n) : ℕ∞ :=
  if i = j then 0
  else
    -- For now, use a simple definition
    -- True definition would compute infimum over all paths from i to j
    G.w i j

def isShortestPath {n : ℕ} (G : Graph n) (d : Fin n → Fin n → ℕ∞) : Prop :=
  ∀ i j, d i j = shortestDist G i j

end FYP
