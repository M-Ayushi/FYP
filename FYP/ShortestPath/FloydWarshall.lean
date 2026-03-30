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

-- Iniitial distance function is the same as the shortest distance
-- considering only paths that use vertices in the empty list
-- This is the base case for the induction in fw_invariant
lemma initDist_eq_sInf {n : ℕ} (G : Graph n) (i j : Fin n) :
  initDist G i j =
    sInf {w | ∃ p,
                isPathFromTo G p i j ∧
                (∀ v ∈ p, v ∈ [] ∨ v = i ∨ v = j) ∧
                pathWeight G p = w} := by
  simp only [List.not_mem_nil, false_or]
  by_cases h : i = j
  · -- case i == j
    simp only [h, or_self]
    apply le_antisymm
    · -- show initDist G i i ≤ sInf ...
      simp[initDist]
    · -- show sInf ... ≤ initDist G i i
      simp [initDist]
      sorry
  · -- case i != j
    sorry

lemma foldl_fwStep_swap {n : ℕ} (ks : List (Fin n))
  (d : Fin n → Fin n → ℕ∞) (k i j : Fin n) :
  (List.foldl fwStep (fwStep d k) ks) i j =
    fwStep (List.foldl fwStep d ks) k i j := by
    sorry

-- proof for adding vertex k to the list of intermediate vertices
lemma sInf_split {n : ℕ} (G : Graph n) (ks : List (Fin n)) (k i j : Fin n) :
  distUpToList G (k :: ks) i j =
    min (distUpToList G ks i j) (distUpToList G ks i k + distUpToList G ks k j) := by
  simp only [distUpToList]
  apply le_antisymm
  · -- show distUpToList G (k :: ks) i j ≤ min ...
    apply le_min
    · -- show distUpToList G (k :: ks) i j ≤ distUpToList G ks i j
      apply le_sInf
      intro w hw
      rcases hw with ⟨p, hp_path, hp_vertices, hp_weight⟩
      apply sInf_le
      refine ⟨p, hp_path, ?_, hp_weight⟩
      intro v hv
      specialize hp_vertices v hv
      cases hp_vertices with
      | inl h1 =>
        left
        simp [h1]
      | inr h2 =>
        sorry
    · -- show distUpToList G (k :: ks) i j ≤ distUpToList G ks i k + distUpToList G ks k j
      apply le_trans
      · change distUpToList G (k :: ks) i j ≤ distUpToList G ks i j
        apply le_sInf
        intro w hw
        rcases hw with ⟨p, hp_path, hp_vertices, hp_weight⟩
        by_cases hk : k ∈ p
        · -- split path at k
          apply sInf_le
          refine ⟨p, hp_path, ?_, hp_weight⟩
          intro v hv
          specialize hp_vertices v hv
          cases hp_vertices with
          | inl hvks =>
            left
            exact List.mem_cons_of_mem k hvks
          | inr hvij =>
            right
            exact hvij
        · -- path avoids k
          apply sInf_le
          refine ⟨p, hp_path, ?_, hp_weight⟩
          intro v hv
          specialize hp_vertices v hv
          cases hp_vertices with
          | inl hvks =>
            left
            exact List.mem_cons_of_mem k hvks
          | inr hvij =>
            right
            exact hvij
      · -- show distUpToList G ks i k + distUpToList G ks k j ≤ min ...
        apply sInf_le
        sorry
  sorry

-- applying fwStep l times is the same as applying fwStep to the list of vertices in l
lemma fw_invariant {n : ℕ} (G : Graph n) :
  ∀ (l : List (Fin n)) (i j : Fin n),
    (l.foldl fwStep (initDist G)) i j = distUpToList G l i j := by
      intro l
      induction l with
      -- base case: no intermediate vertices
      | nil =>
        apply initDist_eq_sInf
      -- inductive step: add vertex k to the list of intermediate vertices
      | cons k ks ih =>
        intro i j
        simp only [List.foldl]
        rw [foldl_fwStep_swap]
        simp only [fwStep]
        rw [ih i j, ih i k, ih k j]
        rw [sInf_split G ks k i j]

theorem floydWarshall_correct (G : Graph n) (i j : Fin n) :
  floydWarshall G i j = dist G i j := by
  simp only [floydWarshall]
  rw [fw_invariant G (List.finRange n) i j]
  simp only [dist, distUpToList]
  -- show that distUpToList G (List.finRange n) i j = dist G i j
  -- this should follow from the fact that
  -- distUpToList G (List.finRange n) i j is the infimum over all
  -- paths from i to j, which is exactly dist G i j
  apply le_antisymm
  · -- show distUpToList G (List.finRange n) i j ≤ dist
    apply le_sInf
    intro w hw
    rcases hw with ⟨p, hp_path, hp_vertices, hp_weight⟩
    apply sInf_le
    refine ⟨p, hp_path, ?_, rfl⟩
    -- show that p only uses vertices in List.finRange n
    -- this should be true since List.finRange n contains all vertices
    simp [List.mem_finRange, true_or]
  · -- show dist G i j ≤ distUpToList G (List.finRange n) i j
    simp

end FYP
