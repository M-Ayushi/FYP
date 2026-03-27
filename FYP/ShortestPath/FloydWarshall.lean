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

-- applying fwStep l times is the same as applying fwStep to the list of vertices in l
lemma fw_invariant {n : ℕ} (G : Graph n) :
  ∀ (l : List (Fin n)) (i j : Fin n),
    (l.foldl fwStep (initDist G)) i j = distUpToList G l i j := by
      intro l
      induction l with
      -- base case: no intermediate vertices
      | nil =>
        intro i j
        simp only [List.foldl, distUpToList]
        -- show that initDist G i j = distUpToList G [] i j
        apply le_antisymm
        · apply le_sInf
          intros p hp
          rcases hp with ⟨hp_path, hp_vertices, hp_weight⟩
          simp only [initDist]
          by_cases h : i = j
          · -- case i == j
            simp [h]
          · -- case i != j
            simp [h]
            sorry
        · apply sInf_le
          sorry
      -- inductive step: add vertex k to the list of intermediate vertices
      | cons k ks ih =>
        sorry

theorem floydWarshall_correct (G : Graph n) (i j : Fin n) :
  floydWarshall G i j = dist G i j := by
  sorry

end FYP
