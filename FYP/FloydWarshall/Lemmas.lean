import FYP.Graph.Basic
import FYP.Graph.Path
import FYP.Graph.PathLemmas
import FYP.FloydWarshall.Definitions

namespace FYP

-- each iteration of FW doesn't increase distances
lemma fwStep_le_self {n : ℕ} (d : Fin n → Fin n → ℕ∞) (k i j : Fin n) :
  fwStep d k i j ≤ d i j := by
  simp [fwStep]

lemma fwStep_le_via_k {n : ℕ} (d : Fin n → Fin n → ℕ∞) (k i j : Fin n) :
  fwStep d k i j ≤ d i k + d k j := by
  simp [fwStep]

lemma fwStep_monotone {n : ℕ} (d : Fin n → Fin n → ℕ∞) (k : Fin n) :
  ∀ i j, fwStep d k i j ≤ d i j := by
  intro i j
  simp [fwStep]

lemma foldl_fwStep_le {n : ℕ} (l : List (Fin n)) :
  ∀ d i j, (l.foldl fwStep d) i j ≤ d i j := by
  induction l with
  | nil =>
    intro d i j
    simp
  | cons k ks ih =>
    intro d i j
    simp only [List.foldl]
    have h1 := ih (fwStep d k) i j
    have h2 := fwStep_le_self d k i j
    exact le_trans h1 h2

lemma fwStep_correct :
  fwStep d k i j = min (d i j) (d i k + d k j) := by
    simp [fwStep]

-- lemma distUpTo_step :
--   distUpTo G k i j =
--     min (distUpTo G (k - 1) i j) (distUpTo G (k - 1) i k + distUpTo G (k - 1) k j) := by
--   sorry

-- lemma fwStep_correct_step {n : ℕ} (G : Graph n) (d : Fin n → Fin n → ℕ∞) (k : Fin n)
--   (h : ∀ i j, d i j = distUpTo G k i j) :
--   ∀all i j, fwStep d k i j = distUpTo G k i j := by
--   sorry

lemma initDist_eq_sInf_i_eq_j {n : ℕ} (G : Graph n) (j : Fin n) :
 initDist G j j =
  sInf {w | ∃ p, isPathFromTo G p j j ∧
            (∀ v ∈ p, v = j) ∧
            pathWeight G p = w} := by
  apply le_antisymm
  · -- show initDist G j j ≤ sInf ...
    simp [initDist]  -- initDist G j j = 0
  · -- show sInf ... ≤ initDist G j j
    apply sInf_le
    -- pick the path [j]
    refine ⟨[j], ⟨?_, ?_, ?_⟩⟩
    · simp only [isPathFromTo, validPath, pathStart, pathEnd, and_self]
    · intro v hv
      rw [List.mem_singleton] at hv
      rw [hv]
    · simp [initDist]

lemma initDist_eq_sInf_i_neq_j {n : ℕ} (G : Graph n) (i j : Fin n) (h : i ≠ j):
 initDist G i j = sInf {w | ∃ p, isPathFromTo G p i j ∧ (∀ v ∈ p, v = i ∨ v = j)
  ∧ pathWeight G p = w} := by
  apply le_antisymm
  · -- show G.w i j ≤ sInf {w | ...}
    apply le_sInf
    intro w hw
    rcases hw with ⟨p, hp_path, hp_verts, hp_weight⟩
    induction p with
    | nil =>
      simp only [initDist, h, ↓reduceIte]
      cases hp_path
      · contradiction
    | cons u rest =>
      have hu : u = i := by sorry
        -- simp [pathStart] at hp_path
        -- injection hp_path.2.1 with hstart
        -- exact hstart
      cases rest with
      | nil =>
        sorry
        -- simp at hp_path; contradiction
      | cons v rest' =>
        -- v = j or v = i
        have hv : v = j ∨ v = i :=
          sorry
          -- hp_verts v (by simp; left; rfl)
        cases hv
        · -- direct edge i → j
          sorry
          -- rw [hp_weight, pathWeight_cons]
          -- simp [hu, hv]
          -- exact le_refl (G.w i j)
        · -- first edge is i → i, then rest must reach j
          -- inductive hypothesis: sum of rest ≥ G.w i j
          sorry
  · -- show sInf {w | ...} ≤ G.w i j
    apply sInf_le
    refine ⟨[i, j], ⟨?_, ?_, ?_⟩⟩
    · simp [isPathFromTo, validPath, pathStart, pathEnd]
      sorry
    · intro v hv
      cases List.mem_cons.mp hv with
      | inl h1 =>
        left
        rw [h1]
      | inr h2 =>
        right
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        exact h2
    · sorry

-- Iniitial distance function is the same as the shortest distance
-- considering only paths that use vertices in the empty list
-- This is the base case for the induction in fw_invariant
lemma initDist_eq_sInf {n : ℕ} (G : Graph n) (i j : Fin n) :
  initDist G i j = distUpToList G [] i j := by
  simp only [distUpToList, List.not_mem_nil, false_or]
  by_cases h : i = j
  · -- case i = j
    rw [h]
    simp only [or_self]
    exact initDist_eq_sInf_i_eq_j G j
  · -- case i ≠ j
    exact initDist_eq_sInf_i_neq_j G i j h

-- helper lemma for swapping fwStep and foldl
lemma foldl_fwStep_swap {n : ℕ} (ks : List (Fin n))
  (d : Fin n → Fin n → ℕ∞) (k i j : Fin n) :
  (List.foldl fwStep (fwStep d k) ks) i j =
    fwStep (List.foldl fwStep d ks) k i j := by
    sorry

-- adding a vertex to the list of intermediate vertices is a monotone operation
-- i.e. it can only decrease distances
lemma distUpToList_mono {n : ℕ} (G : Graph n) (ks1 ks2 : List (Fin n))
  (h : ∀ v, v ∈ ks1 → v ∈ ks2) :
  ∀ i j , distUpToList G ks2 i j ≤ distUpToList G ks1 i j := by
  intro i j
  apply le_sInf
  intro w hw
  rcases hw with ⟨p, hp_path, hp_vertices, hp_weight⟩
  apply sInf_le
  refine ⟨p, hp_path, ?_, hp_weight⟩
  intro v hv
  specialize hp_vertices v hv
  cases hp_vertices with
  | inl hks1 =>
    left
    exact h v hks1
  | inr hij =>
    right
    simp [hij]

-- helper lemma showing that adding vertex k to the list of intermediate
-- vertices can only decrease distances
lemma add_vertex_le {n : ℕ} (G : Graph n) (ks : List (Fin n)) (k i j : Fin n) :
  distUpToList G (k :: ks) i j ≤ distUpToList G ks i j := by
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
    right
    simp [h2]

-- helper lemma for showing that any path from i to j that can use k is less than
-- or equal to the path that goes via k
lemma add_vertex_split {n : ℕ} (G : Graph n) (ks : List (Fin n)) (k i j : Fin n) :
  distUpToList G (k :: ks) i j ≤ distUpToList G ks i k + distUpToList G ks k j := by
  apply le_of_forall_ge
  intro w hw
  sorry

-- helper lemma showing that any path from i to j that can use k is at least as long
-- as the shorter of the path that doesn't use k and the path that goes via k
lemma consider_k_le_list_incl_k {n : ℕ} (G : Graph n) (ks : List (Fin n)) (k i j : Fin n) :
  min (distUpToList G ks i j) (distUpToList G ks i k + distUpToList G ks k j) ≤
    distUpToList G (k :: ks) i j := by
  apply min_le_iff.mpr
  constructor
  · -- show distUpToList G ks i j ≤ distUpToList G (k :: ks) i j
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
      sorry
    | inr h2 =>
      right
      simp [h2]

-- proof for adding vertex k to the list of intermediate vertices
lemma sInf_split {n : ℕ} (G : Graph n) (ks : List (Fin n)) (k i j : Fin n) :
  distUpToList G (k :: ks) i j =
    min (distUpToList G ks i j) (distUpToList G ks i k + distUpToList G ks k j) := by
  apply le_antisymm
  · -- upper bound: show distUpToList G (k :: ks) i j ≤ min ...
    apply le_min
    · -- show distUpToList G (k :: ks) i j ≤ distUpToList G ks i j
      -- i.e. paths that can use k can only be shorter than paths that can't use k
      exact add_vertex_le G ks k i j
    · -- show distUpToList G (k :: ks) i j ≤ distUpToList G ks i k + distUpToList G ks k j
      -- i.e. any path from i to j that can use k can be split into
      -- a path from i to k and a path from k to j
      exact add_vertex_split G ks k i j
  · -- lower bound: show min ... ≤ distUpToList G (k :: ks) i j
    -- i.e. any path from i to j that can use k is at least as long as the shorter of
    -- the path that doesn't use k and the path that goes via k
    exact consider_k_le_list_incl_k G ks k i j

end FYP
