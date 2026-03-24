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
@[simp] lemma pathWeight_nil :
  pathWeight G [] = 0 := rfl
@[simp] lemma pathWeight_single (u : Fin n) :
  pathWeight G [u] = 0 := rfl
@[simp] lemma pathWeight_cons (u v : Fin n) (rest : Path n) :
  pathWeight G (u :: v :: rest) = G.w u v + pathWeight G (v :: rest) := rfl
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

def concatPath {n : ℕ} : Path n → Path n → Path n
  | [], q => q
  | [u], q => u :: q
  | (u :: v :: ps), q => u :: concatPath (v :: ps) q

@[simp] lemma graphNoSelfLoop {n : ℕ} (G : Graph n) :
  ∀ u : Fin n, G.w u u = 0 := sorry

-- Glue two paths by identifying the end of the first path with the start of the
-- second path (when they are equal), so the junction vertex is not duplicated.
-- def gluePath {n : ℕ} : Path n → Path n → Path n
--   | [], q => q
--   | [u], [] => [u]
--   | [u], v :: qs =>
--       if u = v then u :: qs else u :: v :: qs
--   | (u :: v :: ps), q => u :: gluePath (v :: ps) q

-- lemma gluePath_cons {n : ℕ} (u : Fin n) (ps q : Path n) :
--   ∃ t : Path n, gluePath (u :: ps) q = u :: t := by
--   cases ps with
--   | nil =>
--     cases q with
--     | nil =>
--       exact ⟨[], rfl⟩
--     | cons v qs =>
--       by_cases h : u = v
--       · exact ⟨qs, by simp [gluePath, h]⟩
--       · exact ⟨v :: qs, by simp [gluePath, h]⟩
--   | cons v vs =>
--     exact ⟨gluePath (v :: vs) q, rfl⟩

def usesOnlyUpTo {n : ℕ} (k : Fin n) (p : (List (Fin n))) : Prop :=
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

end FYP
