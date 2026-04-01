import FYP.Graph.Basic
import Mathlib.Data.List.Basic

namespace FYP

-- A path is a sequence of vertices
def Path (n : ℕ) := List (Fin n)

instance {n : ℕ} : Membership (Fin n) (Path n) :=
  inferInstanceAs (Membership (Fin n) (List (Fin n)))

-- A path is valid if every consecutive pair of vertices
-- has an edge in the graph.
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
@[simp] lemma pathWeight_nil :
  pathWeight G [] = 0 := rfl
@[simp] lemma pathWeight_single (u : Fin n) :
  pathWeight G [u] = 0 := rfl
@[simp] lemma pathWeight_cons (u v : Fin n) (rest : Path n) :
  pathWeight G (u :: v :: rest) = G.w u v + pathWeight G (v :: rest) := rfl
-- termination_by p.length

def isPathFromTo {n : ℕ} (G : Graph n) (p : Path n) (i j : Fin n) : Prop :=
  validPath G p ∧
  pathStart p = some i ∧
  pathEnd p = some j

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

def isShortestPath {n : ℕ} (G : Graph n) (i j : Fin n) (p : Path n) : Prop :=
  isPathFromTo G p i j ∧
  ∀ q, isPathFromTo G q i j → pathWeight G p ≤ pathWeight G q

-- defines distance as the minimum weight over all paths from i to j
noncomputable def dist {n : ℕ} (G : Graph n) (i j : Fin n) : ℕ∞ :=
  sInf {w | ∃ p, isPathFromTo G p i j ∧ pathWeight G p = w}

def concatPath {n : ℕ} : Path n → Path n → Path n
  | [], q => q
  | [u], q => u :: q
  | (u :: v :: ps), q => u :: concatPath (v :: ps) q

def usesOnlyUpTo {n : ℕ} (k : Fin n) (p : Path n) : Prop :=
  ∀ v ∈ p, v ≤ k

-- Paths that only use vertices up to k
def pathUpTo {n : ℕ} (G : Graph n) (k : Fin n) (i j : Fin n) :=
  {
    p : Path n |
    validPath G p ∧
    pathStart p = some i ∧
    pathEnd p = some j ∧
    usesOnlyUpTo k p
  }

noncomputable def distUpTo {n : ℕ} (G : Graph n) (k : Fin n) (i j : Fin n) : ℕ∞ :=
  sInf {w | ∃ p,
    isPathFromTo G p i j ∧
    usesOnlyUpTo k p ∧
    pathWeight G p = w}

noncomputable def distUpToList {n : ℕ} (G : Graph n) (l : List (Fin n)) (i j : Fin n) : ℕ∞ :=
  sInf {w | ∃ p,
    isPathFromTo G p i j ∧
    (∀ v ∈ p, v ∈ l ∨ v = i ∨ v = j) ∧
    pathWeight G p = w}

end FYP
