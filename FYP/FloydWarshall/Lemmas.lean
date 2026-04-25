import FYP.Graph.Basic
import FYP.Graph.Path
import FYP.Graph.PathLemmas
import FYP.FloydWarshall.Definitions
import FYP.FloydWarshall.HelperLemmas
import FYP.FloydWarshall.DistanceLemmas

namespace FYP

-- any path from i to j that can use k is less than
-- or equal to the path that goes via k
lemma fwStep_upper_bound_via_k (ks : List (Fin n)) (k i j : Fin n) :
  distUpToList G (k :: ks) i j ≤ distUpToList G ks i k + distUpToList G ks k j := by
  -- apply infimum lemma
  unfold distUpToList
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro w hw
    exact zero_le _
  · rcases exists_path_weight_eq_distUpToList ks i k with
      ⟨p1, hp1_path, hp1_verts, hp1_w⟩
    rcases exists_path_weight_eq_distUpToList ks k j with
      ⟨p2, hp2_path, hp2_verts, hp2_w⟩
    -- define concatenation
    let p := p1 ++ p2.tail
    rcases hp1_path with ⟨hvalid1, hstart1, hend1⟩
    rcases hp2_path with ⟨hvalid2, hstart2, hend2⟩
    have h_link : pathEnd p1 = pathStart p2 := by
      simp [hend1, hstart2]
    refine ⟨p, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · exact validPath_append_tail p1 p2 h_link hvalid1 hvalid2
      · have pathStart_eq : pathStart p = pathStart p1 := by
          have hnonempty1 : p1 ≠ [] := by
            intro h
            rw [h] at hstart1
            contradiction
          exact pathStart_append_tail p1 p2 hnonempty1
        simp [hstart1, pathStart_eq]
      · have pathEnd_eq : pathEnd p = pathEnd p2 := by
          have hnonempty2 : p2 ≠ [] := by
            intro h
            rw [h] at hstart2
            contradiction
          exact pathEnd_append_tail p1 p2 h_link hnonempty2
        simp [hend2, pathEnd_eq]
    · intro v hv
      unfold p at hv
      cases List.mem_append.mp hv with
      | inl hv1 =>
          simp [hp1_verts v hv1]
      | inr hv2 =>
          have hv2' : v ∈ p2 := List.mem_of_mem_tail hv2
          simp [hp2_verts v hv2']
    · simp only [distUpToList] at hp1_w hp2_w
      rw [<- hp1_w, <- hp2_w, pathWeight_append_tail p1 p2 hvalid1 h_link]

lemma pathWeight_eq_split_sum (k i j : Fin n) (p p1 p2 : Path n)
  (hp_split : p = p1 ++ [k] ++ p2)
  (hp_path : isPathFromTo G (p1 ++ [k] ++ p2) i j)
  : pathWeight G p = pathWeight G (p1 ++ [k]) + pathWeight G ([k] ++ p2) := by
    have h_valid : validPath G (p1 ++ [k]) := by
      simp [isPathFromTo] at hp_path
      exact validPath_prefix p1 p2 k (by simp [hp_path.left])
    have h_end : pathEnd (p1 ++ [k]) = pathStart ([k] ++ p2) := by
      simp [pathEnd_append p1 [k] (by simp), pathStart, pathEnd]
    rw [<- pathWeight_append_tail (p1 ++ [k]) ([k] ++ p2) h_valid h_end]
    simp [hp_split]

lemma fwStep_split_cost_le (ks : List (Fin n)) (k i j : Fin n) (p p1 p2 : Path n)
  (hp_split : p = p1 ++ [k] ++ p2)
  (hp_path : isPathFromTo G (p1 ++ [k] ++ p2) i j)
  (hp_verts : ∀ v ∈ p, v = k ∨ v ∈ ks)
  (split_prefix : isPathFromTo G (p1 ++ [k]) i k)
  (split_suffix : isPathFromTo G ([k] ++ p2) k j) :
  distUpToList G ks i k + distUpToList G ks k j ≤ pathWeight G p := by
    -- pathWeight G (p1 ++ [k]) + pathWeight G ([k] ++ p2) := by
    have hp_verts_p1 : ∀ v ∈ p1 ++ [k], v ∈ ks ∨ v = i ∨ v = k := by
      intros v hv;
      have hv_p : v ∈ p := by
        have : v ∈ (p1 ++ [k]) ++ p2 := by
          exact List.mem_append_left p2 hv
        simpa [hp_split] using this
      specialize hp_verts v hv_p
      cases hp_verts with
      | inl hk => exact Or.inr (Or.inr hk)
      | inr hks => exact Or.inl hks
    have h1 : distUpToList G ks i k ≤ pathWeight G (p1 ++ [k]) :=
      distUpToList_le_of_path ks i k (p1 ++ [k])
        (split_prefix) (hp_verts_p1)
    have hp_verts_p2 : ∀ v ∈ ([k] ++ p2), v ∈ ks ∨ v = k ∨ v = j := by
      intros v hv
      have hv_p : v ∈ p := by
        have : v ∈ p1 ++ ([k] ++ p2) := by
          exact List.mem_append_right p1 hv
        simpa [hp_split] using this
      specialize hp_verts v hv_p
      cases hp_verts with
      | inl hk => exact Or.inr (Or.inl hk)
      | inr hks => exact Or.inl hks
    have h2 : distUpToList G ks k j ≤ pathWeight G ([k] ++ p2) := by
      exact distUpToList_le_of_path ks k j ([k] ++ p2)
        (split_suffix) hp_verts_p2
    have hsum : pathWeight G p = pathWeight G (p1 ++ [k]) + pathWeight G ([k] ++ p2) :=
      pathWeight_eq_split_sum k i j p p1 p2 hp_split hp_path
    rw [hsum]
    exact add_le_add h1 h2

lemma fwStep_lower_bound_with_k (ks : List (Fin n)) (k i j : Fin n)
  (p : Path n) (hp_path : isPathFromTo G p i j) (hp_verts : ∀ v ∈ p, v ∈ k :: ks)
  (hp_weight : pathWeight G p = distUpToList G (k :: ks) i j) (h : k ∈ p) :
  min (distUpToList G ks i j)
    (distUpToList G ks i k + distUpToList G ks k j) ≤
      distUpToList G (k :: ks) i j := by
    let p1 := p.takeWhile (fun v => v ≠ k)
    let p2 := p.drop (p1.length + 1)
    have hp_split : p = p1 ++ [k] ++ p2 :=
      takeWhile_drop_split k p h
    simp only [hp_split] at hp_path
    simp only [List.mem_cons] at hp_verts
    have split_prefix := isPathFromTo_prefix p1 p2 i j k hp_path
    have split_suffix := isPathFromTo_suffix p1 p2 i j k hp_path
    have h_total : distUpToList G ks i k + distUpToList G ks k j ≤ pathWeight G p := by
      exact fwStep_split_cost_le ks k i j p p1 p2
        hp_split hp_path hp_verts split_prefix split_suffix
    have h_right :
      distUpToList G ks i k + distUpToList G ks k j
        ≤ distUpToList G (k :: ks) i j := by
      simpa [hp_weight] using h_total
    exact inf_le_of_right_le h_right

lemma fwStep_lower_bound_without_k (ks : List (Fin n)) (k i j : Fin n) (p : Path n)
  (hp_path : isPathFromTo G p i j) (hp_verts : ∀ v ∈ p, v ∈ k :: ks)
  (hp_weight : pathWeight G p = distUpToList G (k :: ks) i j) (h : k ∉ p) :
  min (distUpToList G ks i j) (distUpToList G ks i k + distUpToList G ks k j)
  ≤ distUpToList G (k :: ks) i j := by
    have hp_verts_ks : ∀ v ∈ p, v ∈ ks ∨ v = i ∨ v = j := by
      intro v hv
      have hmem := hp_verts v hv
      have hv_ne_k : v ≠ k := by
        intro hvk
        subst hvk
        exact h hv
      simp [hv_ne_k] at hmem
      simp [hmem]
    have hA :
      distUpToList G ks i j ≤ pathWeight G p :=
      distUpToList_le_of_path ks i j p hp_path hp_verts_ks
    have h1 := (min_le_left (distUpToList G ks i j)
      (distUpToList G ks i k + distUpToList G ks k j)).trans hA
    rw [hp_weight] at h1
    exact h1

-- any path from i to j that can use k is at least as long as the
-- shorter of the path that doesn't use k and the path that goes via k
lemma fwStep_lower_bound (ks : List (Fin n)) (k i j : Fin n) :
  min (distUpToList G ks i j) (distUpToList G ks i k + distUpToList G ks k j) ≤
    distUpToList G (k :: ks) i j := by
    obtain ⟨p, hp_path, hp_verts, hp_weight⟩ :=
      exists_path_weight_eq_distUpToList (k :: ks) i j
    by_cases h : k ∈ p
    · -- path from i to j that uses k can be split into
      -- a path from i to k and a path from k to j
      exact fwStep_lower_bound_with_k ks k i j p hp_path hp_verts hp_weight h
    · -- case 2: p doesn't use k
      -- any path from i to j that doesn't use k is still a valid path
      -- when we add k to the list of intermediate vertices
      exact fwStep_lower_bound_without_k ks k i j p hp_path hp_verts hp_weight h

-- proof for adding vertex k to the list of intermediate vertices
lemma fwStep_invariant (ks : List (Fin n)) (k i j : Fin n) :
  min (distUpToList G ks i j) (distUpToList G ks i k + distUpToList G ks k j)
    = distUpToList G (k :: ks) i j := by
  apply le_antisymm
  · -- lower bound: show min ... ≤ distUpToList G (k :: ks) i j
    exact fwStep_lower_bound ks k i j
  · -- upper bound: show distUpToList G (k :: ks) i j ≤ min ...
    apply le_min
    · -- distUpToList G (k :: ks) i j ≤ distUpToList G ks i j
      have subsetofList : ∀ v, v ∈ ks → v ∈ k :: ks := by
        intro v hv
        exact List.mem_cons_of_mem k hv
      exact distUpToList_mono ks (k :: ks) subsetofList i j
    · -- distUpToList G (k :: ks) i j ≤ distUpToList G ks i k + distUpToList G ks k j
      exact fwStep_upper_bound_via_k ks k i j

end FYP
