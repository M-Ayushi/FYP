import FYP.Graph.Basic

namespace FYP

-- A path is a sequence of vertices
abbrev Path (n : ℕ) := List (Fin n)

instance {n : ℕ} : Membership (Fin n) (Path n) :=
  inferInstanceAs (Membership (Fin n) (List (Fin n)))

-- A path is valid if every consecutive pair of vertices
-- has an edge in the graph.
def validPath (G : Graph n) : Path n → Prop
  | [] => False
  | [_] => True
  | (u :: v :: rest) =>
      G.w u v ≠ ⊤ ∧ validPath G (v :: rest)

def pathStart : Path n → Option (Fin n)
  | [] => none
  | v :: _ => some v

def pathEnd : Path n → Option (Fin n)
  | [] => none
  | [v] => some v
  | _ :: rest => pathEnd rest

-- Compute weight of a path by summing edge weights
def pathWeight (G : Graph n) : Path n → ℕ∞
  | [] => 0
  | [_] => 0  -- single vertex has weight 0
  | (u :: v :: rest) =>
      G.w u v + pathWeight G (v :: rest)
@[simp] lemma pathWeight_single (u : Fin n) :
  pathWeight G [u] = 0 := rfl
@[simp] lemma pathWeight_cons (u v : Fin n) (rest : Path n) :
  pathWeight G (u :: v :: rest) = G.w u v + pathWeight G (v :: rest) := rfl

def isPathFromTo (G : Graph n) (p : Path n) (i j : Fin n) : Prop :=
  validPath G p ∧
  pathStart p = some i ∧
  pathEnd p = some j

-- defines distance as the minimum weight over all paths from i to j
noncomputable def shortestDist (G : Graph n) (i j : Fin n) : ℕ∞ :=
  sInf {w | ∃ p, isPathFromTo G p i j ∧ pathWeight G p = w}

end FYP
