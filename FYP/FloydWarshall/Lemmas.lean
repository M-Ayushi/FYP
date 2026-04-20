import FYP.Graph.Basic
import FYP.Graph.Path
import FYP.Graph.PathLemmas
import FYP.FloydWarshall.Definitions
import FYP.FloydWarshall.HelperLemmas

namespace FYP

lemma initDist_eq_sInf_eq {n : ℕ} (G : Graph n) (j : Fin n) :
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

lemma initDist_le_sInf_neq_by_path_witness {n : ℕ} (G : Graph n) (i j : Fin n) (h : i ≠ j) :
  initDist G i j ≤
    sInf {w | ∃ p, isPathFromTo G p i j ∧
            (∀ v ∈ p, v = i ∨ v = j) ∧ pathWeight G p = w} := by
  simp only [initDist, h, ↓reduceIte]
  apply le_sInf
  intro w hw
  rcases hw with ⟨p, hp_path, hp_verts⟩
  rcases hp_verts with ⟨hverts, rfl⟩
  rcases hp_path with ⟨hvalid, hstart, hend⟩
  induction p with
  | nil =>
    contradiction
  | cons x xs =>
    cases xs with
    | nil =>
        simp only [pathStart, pathEnd] at hstart hend
        cases hstart
        cases hend
        exact (h rfl).elim
    | cons y ys =>
      have hx : x = i := by
        simp only [pathStart, Option.some.injEq] at hstart
        exact hstart
      subst hx
      have hy := hverts y (by simp)
      cases hy with
      | inl hy_i =>
          rename_i ih
          simp only [pathWeight, ge_iff_le]
          rw [<- hy_i] at hvalid hstart hend hverts ih
          rw [<- hy_i]
          have self_weight : G.w y y = 0 := by
            exact G.self_weight y
          simp only [self_weight, zero_add, ge_iff_le]
          have all_x_j : (∀ v ∈ y :: ys, v = y ∨ v = j) := by
            simp only [List.mem_cons, or_self_left] at hverts
            simp only [List.mem_cons]
            exact hverts
          have hstart' : pathStart (y :: ys) = some y := by
            simp [pathStart]
          have hend' : pathEnd (y :: ys) = some j := by
            simpa [pathEnd] using hend
          have hvalid' : validPath G ([y] ++ ys) := by
              exact validPath_suffix G [y] ys y hvalid
          simp only at hvalid'
          have h1 := ih all_x_j hvalid' hstart' hend'
          exact h1
      | inr hy_j =>
          simp only [pathWeight, ge_iff_le]
          rw [<- hy_j]
          simp

lemma initDist_eq_sInf_neq {n : ℕ} (G : Graph n) (i j : Fin n) (h : i ≠ j) :
  initDist G i j = sInf {w | ∃ p, isPathFromTo G p i j ∧ (∀ v ∈ p, v = i ∨ v = j)
                     ∧ pathWeight G p = w} := by
  apply le_antisymm
  · exact initDist_le_sInf_neq_by_path_witness G i j h
  · apply sInf_le
    refine ⟨[i, j], ⟨?path_valid, ?path_start, ?path_end⟩, ?verts⟩
    · simp [validPath]
      simp [path_valid G i j h]
    · simp [pathStart]
    · simp [pathEnd]
    · constructor
      · exact mem_pair_iff i j
      · simp [initDist, h, ↓reduceIte]

-- Initial distance function is the same as the shortest distance
-- considering only paths that use vertices in the empty list
-- This is the base case for the induction in fw_invariant
lemma initDist_eq_sInf {n : ℕ} (G : Graph n) (i j : Fin n) :
  initDist G i j = distUpToList G [] i j := by
  simp only [distUpToList, List.not_mem_nil, false_or]
  by_cases h : i = j
  · simp only [h, or_self]
    exact initDist_eq_sInf_eq G j
  · exact initDist_eq_sInf_neq G i j h

lemma distUpToList_le_of_path {n : ℕ} (G : Graph n)
  (ks : List (Fin n)) (i j : Fin n) (p : Path n)
  (hp_path : isPathFromTo G p i j)
  (hp_verts : ∀ v ∈ p, v ∈ ks ∨ v = i ∨ v = j) :
  distUpToList G ks i j ≤ pathWeight G p := by
    unfold distUpToList
    apply sInf_le
    exact ⟨p, hp_path, hp_verts, rfl⟩

-- adding a vertex to the list of intermediate vertices is a monotone operation
-- i.e. it can only decrease distances
lemma distUpToList_mono {n : ℕ} (G : Graph n) (ks1 ks2 : List (Fin n))
  (h : ∀ v, v ∈ ks1 → v ∈ ks2) :
  ∀ i j , distUpToList G ks2 i j ≤ distUpToList G ks1 i j := by
  intro i j
  apply le_sInf
  intro w hw
  rcases hw with ⟨p, hp_path, hp_vertices, hp_weight⟩
  rw [<- hp_weight]
  have hp_vertices_ks2 : ∀ v ∈ p, v ∈ ks2 ∨ v = i ∨ v = j := by
      exact fun v a ↦ Or.imp_left (h v) (hp_vertices v a)
  exact distUpToList_le_of_path G ks2 i j p hp_path hp_vertices_ks2

-- normally an infimum is not guaranteed to be attained, but in this case
-- we are restricted to only positive integer weights so the infimum is actually a minimum
lemma exists_path_weight_eq_distUpToList {n : ℕ} (G : Graph n) (ks : List (Fin n)) (i j : Fin n) :
  ∃ p, isPathFromTo G p i j ∧ (∀ v ∈ p, v ∈ ks)
      ∧ pathWeight G p = distUpToList G ks i j := by
    unfold distUpToList
    sorry

-- any path from i to j that can use k is less than
-- or equal to the path that goes via k
lemma fwStep_le_split {n : ℕ} (G : Graph n) (ks : List (Fin n)) (k i j : Fin n) :
  distUpToList G (k :: ks) i j ≤ distUpToList G ks i k + distUpToList G ks k j := by
  -- apply infimum lemma
  unfold distUpToList
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro w hw
    exact zero_le _
  · rcases exists_path_weight_eq_distUpToList G ks i k with
      ⟨p1, hp1_path, hp1_verts, hp1_w⟩
    rcases exists_path_weight_eq_distUpToList G ks k j with
      ⟨p2, hp2_path, hp2_verts, hp2_w⟩
    -- define concatenation
    let p := p1 ++ p2.tail
    rcases hp1_path with ⟨hvalid1, hstart1, hend1⟩
    rcases hp2_path with ⟨hvalid2, hstart2, hend2⟩
    have h_link : pathEnd p1 = pathStart p2 := by
      simp [hend1, hstart2]
    refine ⟨p, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · exact validPath_append_tail G p1 p2 h_link hvalid1 hvalid2
      · have pathStart_eq : pathStart p = pathStart p1 := by
          exact pathStart_append_tail p1 p2 i hstart1
        simp [hstart1, pathStart_eq]
      · have pathEnd_eq : pathEnd p = pathEnd p2 := by
          exact pathEnd_append_tail p1 p2 j h_link hend2
        simp [hend2, pathEnd_eq]
    · intro v hv
      unfold p at hv
      apply List.mem_append.mp at hv
      cases hv with
      | inl hv1 =>
          have : v ∈ ks := hp1_verts v hv1
          exact Or.inl (List.mem_cons_of_mem _ this)
      | inr hv2 =>
          have : v ∈ p2 := List.mem_of_mem_tail hv2
          have : v ∈ ks := hp2_verts v this
          exact Or.inl (List.mem_cons_of_mem _ this)
    · simp only [distUpToList] at hp1_w hp2_w
      rw [<- hp1_w, <- hp2_w]
      unfold p
      rw [pathWeight_append_tail G p1 p2 hvalid1 h_link]

-- any path from i to j that can use k is at least as long as the
-- shorter of the path that doesn't use k and the path that goes via k
lemma min_le_list_with_k {n : ℕ} (G : Graph n) (ks : List (Fin n)) (k i j : Fin n) :
  min (distUpToList G ks i j) (distUpToList G ks i k + distUpToList G ks k j) ≤
    distUpToList G (k :: ks) i j := by
    obtain ⟨p, hp_path, hp_verts, hp_weight⟩ :=
      exists_path_weight_eq_distUpToList G (k :: ks) i j
    by_cases h : k ∈ p
    · -- any path from i to j that uses k can be split into
      -- a path from i to k and a path from k to j
      let p1 := p.takeWhile (fun v => v ≠ k)
      let p2 := p.drop (p1.length + 1)
      have hp_split : p = p1 ++ [k] ++ p2 :=
        takeWhile_drop_split k p h
      have split :=
        isPathFromTo_split G p1 p2 i j k
          (by simpa [hp_split] using hp_path)
      have hp_verts_p1 : ∀ v ∈ p1 ++ [k], v ∈ ks ∨ v = i ∨ v = k := by
        intros v hv;
        simp only [List.mem_cons] at hp_verts
        have hv_p : v ∈ p := by
          have : v ∈ p1 ++ [k] ++ p2 := by
            apply List.mem_append.mpr
            exact Or.inl hv
          simpa [hp_split] using this
        specialize hp_verts v hv_p
        cases hp_verts with
        | inl hk => exact Or.inr (Or.inr hk)
        | inr hks => exact Or.inl hks
      have h1 : distUpToList G ks i k ≤ pathWeight G (p1 ++ [k]) :=
        distUpToList_le_of_path G ks i k (p1 ++ [k])
          (split.1) (hp_verts_p1)
      have hp_verts_p2 : ∀ v ∈ ([k] ++ p2), v ∈ ks ∨ v = k ∨ v = j := by
        intros v hv
        have hv_p : v ∈ p := by
          have : v ∈ p1 ++ [k] ++ p2 := by
            apply List.mem_append.mpr
            simp only [List.cons_append, List.mem_cons] at hv
            cases hv with
            | inl hk =>
              subst hk
              left
              simp
            | inr hv_p2 =>
              right
              exact hv_p2
          simpa [hp_split] using this
        specialize hp_verts v hv_p
        simp only [List.mem_cons] at hp_verts
        cases hp_verts with
        | inl hk => exact Or.inr (Or.inl hk)
        | inr hks => exact Or.inl hks
      have h2 : distUpToList G ks k j ≤ pathWeight G ([k] ++ p2) := by
        exact distUpToList_le_of_path G ks k j ([k] ++ p2)
          (split.2) hp_verts_p2
      have hp_sum :
        pathWeight G p = pathWeight G (p1 ++ [k]) + pathWeight G ([k] ++ p2) := by
          have h_valid : validPath G (p1 ++ [k]) := by
            simp [isPathFromTo, hp_split] at hp_path
            exact validPath_prefix G p1 p2 k (by simp [hp_path.left])
          have h_end : pathEnd (p1 ++ [k]) = pathStart ([k] ++ p2) := by
            simp [pathEnd_append p1 [k] (by simp), pathStart, pathEnd]
          rw [<- pathWeight_append_tail G (p1 ++ [k]) ([k] ++ p2) h_valid h_end]
          simp [hp_split]
      -- transitivity
      have h_total : distUpToList G ks i k + distUpToList G ks k j ≤ pathWeight G p := by
        simp only [hp_sum]
        exact add_le_add h1 h2
      have h_right :
        distUpToList G ks i k + distUpToList G ks k j
          ≤ distUpToList G (k :: ks) i j := by
        simpa [hp_weight] using h_total
      exact le_trans (min_le_right _ _) h_right
    · -- case 2: p doesn't use k
      -- any path from i to j that doesn't use k is still a valid path
      -- when we add k to the list of intermediate vertices
      have hp_verts_ks : ∀ v ∈ p, v ∈ ks ∨ v = i ∨ v = j := by
        intro v hv
        have hmem := hp_verts v hv
        rcases List.mem_cons.mp hmem with h' | h'
        · subst h'
          exact False.elim (h hv)
        · exact Or.inl h'
      have hA :
        distUpToList G ks i j ≤ pathWeight G p :=
        distUpToList_le_of_path G ks i j p hp_path hp_verts_ks
      have h1 := (min_le_left (distUpToList G ks i j)
        (distUpToList G ks i k + distUpToList G ks k j)).trans hA
      rw [hp_weight] at h1
      exact h1

-- proof for adding vertex k to the list of intermediate vertices
lemma fwStep_invariant {n : ℕ} (G : Graph n) (ks : List (Fin n)) (k i j : Fin n) :
  min (distUpToList G ks i j) (distUpToList G ks i k + distUpToList G ks k j)
    = distUpToList G (k :: ks) i j := by
  apply le_antisymm
  · -- lower bound: show min ... ≤ distUpToList G (k :: ks) i j
    -- i.e. any path from i to j that can use k is at least as long as the shorter of
    -- the path that doesn't use k and the path that goes via k
    exact min_le_list_with_k G ks k i j
  · -- upper bound: show distUpToList G (k :: ks) i j ≤ min ...
    apply le_min
    · -- show distUpToList G (k :: ks) i j ≤ distUpToList G ks i j
      -- i.e. paths that can use k can only be shorter than paths that can't use k
      have subsetofList : ∀ v, v ∈ ks → v ∈ k :: ks := by
        intro v hv
        exact List.mem_cons_of_mem k hv
      exact distUpToList_mono G ks (k :: ks) subsetofList i j
    · -- show distUpToList G (k :: ks) i j ≤ distUpToList G ks i k + distUpToList G ks k j
      -- i.e. any path from i to j that can use k can be split into
      -- a path from i to k and a path from k to j
      exact fwStep_le_split G ks k i j

end FYP
