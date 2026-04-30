import FYP.FloydWarshall.PathSplitLemmas

namespace FYP

lemma fwStep_lower_bound_with_k (G : Graph n) (ks : List (Fin n)) (k i j : Fin n)
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
    have h_total : distUpToList G ks i k + distUpToList G ks k j ≤ pathWeight G p := by
      exact fwStep_split_cost_le ks k i j p p1 p2
        hp_split hp_path hp_verts
    simp only [hp_weight] at h_total
    exact inf_le_of_right_le h_total

lemma fwStep_lower_bound_without_k (G : Graph n) (ks : List (Fin n)) (k i j : Fin n) (p : Path n)
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
    have distList_le_path : distUpToList G ks i j ≤ pathWeight G p :=
      distUpToList_le_of_path ks i j p hp_path hp_verts_ks
    simp [<- hp_weight, distList_le_path]

-- any path from i to j that can use k is less than
-- or equal to the path that goes via k
lemma fwStep_upper_bound_via_k (G : Graph n) (ks : List (Fin n)) (k i j : Fin n) :
  distUpToList G (k :: ks) i j ≤ distUpToList G ks i k + distUpToList G ks k j := by
  apply csInf_le
  · refine ⟨ 0, ?_ ⟩
    intro w hw
    exact zero_le _
  · rcases exists_path_weight_eq_distUpToList G ks i k with
      ⟨ p1, hp1_path, hp1_verts, hp1_w ⟩
    rcases exists_path_weight_eq_distUpToList G ks k j with
      ⟨ p2, hp2_path, hp2_verts, hp2_w ⟩
    let p := p1 ++ p2.tail
    rcases hp1_path with ⟨ hvalid1, hstart1, hend1 ⟩
    rcases hp2_path with ⟨ hvalid2, hstart2, hend2 ⟩
    have h_link : pathEnd p1 = pathStart p2 := by
      simp [hend1, hstart2]
    refine ⟨ p, ?_, ?_, ?_ ⟩
    · exact isPathFromTo_appendTail G i j p1 p2 hvalid1 hstart1 hvalid2 hend2 h_link
    · intro v hv
      unfold p at hv
      cases List.mem_append.mp hv with
      | inl hv1 =>
          simp [hp1_verts v hv1]
      | inr hv2 =>
          have hv2' : v ∈ p2 := List.mem_of_mem_tail hv2
          simp [hp2_verts v hv2']
    · rw [<- hp1_w, <- hp2_w, pathWeight_append_tail p1 p2 hvalid1 h_link]


end FYP
