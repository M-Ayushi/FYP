import FYP.Graph.Basic
import FYP.Graph.Path
import FYP.Graph.PathLemmas
import FYP.FloydWarshall.Definitions
import FYP.FloydWarshall.HelperLemmas

namespace FYP

lemma initDist_eq_sInf_diag (j : Fin n) :
 initDist G j j = sInf {w | ∃ p,
            isPathFromTo G p j j ∧
            (∀ v ∈ p, v = j) ∧
            pathWeight G p = w} := by
  apply le_antisymm
  · -- initDist G j j ≤ sInf ...
    simp [initDist]  -- initDist G j j = 0
  · -- sInf ... ≤ initDist G j j
    apply sInf_le
    refine ⟨[j], ⟨?_, ?_, ?_⟩⟩
    · simp [isPathFromTo, validPath, pathStart, pathEnd]
    · intro v hv
      rw [List.mem_singleton] at hv
      rw [hv]
    · simp [initDist]

lemma initDist_le_pathWeight_two_vertices (i j : Fin n) (h : i ≠ j)
  (p : Path n) (hpath : isPathFromTo G p i j) (hverts : ∀ v ∈ p, v = i ∨ v = j) :
  G.w i j ≤ pathWeight G p := by
    rcases hpath with ⟨ hvalid, hstart, hend ⟩
    induction p with
    | nil => contradiction
    | cons x xs =>
      rename_i ih
      have hx : x = i := by
        simp only [pathStart, Option.some.injEq] at hstart
        exact hstart
      subst hx
      cases xs with
      | nil =>
          simp only [pathStart, pathEnd] at hstart hend
          cases hstart
          cases hend
          exact (h rfl).elim
      | cons y ys =>
        have hy := hverts y (by simp)
        cases hy with
        | inl hy_i =>
            rw [hy_i] at hvalid hstart hend hverts ih
            simp only [pathWeight, ge_iff_le, hy_i, G.self_weight x, zero_add, ge_iff_le]
            have all_x_j : (∀ v ∈ x :: ys, v = x ∨ v = j) := by
              simp only [List.mem_cons, or_self_left] at hverts
              simp only [List.mem_cons]
              exact hverts
            have hvalid' : validPath G ([x] ++ ys) := by
                exact validPath_suffix [x] ys x hvalid
            have hstart' : pathStart (x :: ys) = some x := by
              simp [pathStart]
            have hend' : pathEnd (x :: ys) = some j := by
              simpa [pathEnd] using hend
            exact ih all_x_j hvalid' hstart' hend'
        | inr hy_j =>
            simp [hy_j]

lemma initDist_eq_sInf_offdiag (i j : Fin n) (h : i ≠ j) :
  initDist G i j = sInf {w | ∃ p, isPathFromTo G p i j ∧ (∀ v ∈ p, v = i ∨ v = j)
                     ∧ pathWeight G p = w} := by
  apply le_antisymm
  · simp only [initDist, h]
    apply le_sInf
    intro w hw
    rcases hw with ⟨p, hp_path, hp_verts⟩
    rcases hp_verts with ⟨hverts, rfl⟩
    exact initDist_le_pathWeight_two_vertices i j h p hp_path hverts
  · apply sInf_le
    refine ⟨[i, j], ⟨?path_valid, ?path_start, ?path_end⟩, ?verts⟩
    · simp [validPath, path_valid G i j h]
    · simp [pathStart]
    · simp [pathEnd]
    · constructor
      · exact mem_pair_iff i j
      · simp [initDist, h]

-- Initial distance function is the same as the shortest distance
-- considering only paths that use vertices in the empty list
-- This is the base case for the induction in fw_invariant
lemma initDist_eq_sInf (i j : Fin n) :
  initDist G i j = distUpToList G [] i j := by
  simp only [distUpToList, List.not_mem_nil, false_or]
  by_cases h : i = j
  · simp only [h, or_self]
    exact initDist_eq_sInf_diag j
  · exact initDist_eq_sInf_offdiag i j h

lemma distUpToList_le_of_path (ks : List (Fin n)) (i j : Fin n)
  (p : Path n) (hp_path : isPathFromTo G p i j)
  (hp_verts : ∀ v ∈ p, v ∈ ks ∨ v = i ∨ v = j) :
  distUpToList G ks i j ≤ pathWeight G p := by
    unfold distUpToList
    apply sInf_le
    exact ⟨p, hp_path, hp_verts, rfl⟩

-- adding a vertex to the list of intermediate vertices is a monotone operation
-- i.e. it can only decrease distances
lemma distUpToList_mono (ks1 ks2 : List (Fin n))
  (h : ∀ v, v ∈ ks1 → v ∈ ks2) :
  ∀ i j , distUpToList G ks2 i j ≤ distUpToList G ks1 i j := by
  intro i j
  apply le_sInf
  intro w hw
  rcases hw with ⟨p, hp_path, hp_vertices, hp_weight⟩
  rw [<- hp_weight]
  have hp_vertices_ks2 : ∀ v ∈ p, v ∈ ks2 ∨ v = i ∨ v = j := by
      exact fun v a ↦ Or.imp_left (h v) (hp_vertices v a)
  exact distUpToList_le_of_path ks2 i j p hp_path hp_vertices_ks2

-- normally an infimum is not guaranteed to be attained, but in this case
-- we are restricted to only positive integer weights so the infimum is actually a minimum
lemma exists_path_weight_eq_distUpToList (ks : List (Fin n)) (i j : Fin n) :
  ∃ p, isPathFromTo G p i j ∧ (∀ v ∈ p, v ∈ ks) -- ∨ v = i ∨ v = j)
      ∧ pathWeight G p = distUpToList G ks i j := by
    unfold distUpToList
    sorry

end FYP
