import FYP.Graph.Basic
import FYP.Graph.Path
import FYP.Graph.PathLemmas
import FYP.FloydWarshall.Definitions
import FYP.FloydWarshall.HelperLemmas

namespace FYP

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

lemma initDist_eq_sInf_i_neq_j {n : ℕ} (G : Graph n) (i j : Fin n) (h : i ≠ j) :
  initDist G i j = sInf {w | ∃ p, isPathFromTo G p i j ∧ (∀ v ∈ p, v = i ∨ v = j)
                     ∧ pathWeight G p = w} := by
  apply le_antisymm
  · simp only [initDist, h, ↓reduceIte]
    apply le_sInf
    intro w hw
    rcases hw with ⟨p, hp_path, hp_verts⟩
    induction p with
    | nil =>
      rcases hp_path with ⟨hvalid, hstart, hend⟩
      contradiction
    | cons u rest =>
      have hu : u = i := by
        rcases hp_path with ⟨_, hstart, _⟩
        simp only [pathStart] at hstart
        injection hstart with hstart_eq

      cases rest with
      | nil =>
        rcases hp_path with ⟨_, hp_start, hp_end⟩
        have hu_end : u = j := by
          simp only [pathEnd] at hp_end
          injection hp_end with hu_end_eq
        subst hu_end
        subst hu
        exact (h rfl).elim
      | cons v rest' =>
        rcases hp_path with ⟨hvalid, hstart, hend⟩
        have tail_path : isPathFromTo G (v :: rest') i j := by
          simp only [isPathFromTo, pathStart, pathEnd, validPath] at *
          constructor
          · exact hvalid.2
          · simp only [Option.some.injEq]
            rename_i hstart_eq
            constructor
            · -- v = i
              have hv : v ∈ u :: v :: rest' := by
                simp [List.mem_cons]
              have hverts := hp_verts.1
              have hv_cases := hverts v hv
              cases hv_cases with
              | inl hv_i =>
                exact hv_i
              | inr hv_j =>
                have : i = j := by
                  sorry
                  -- simpa [hv_j] using hu.symm
                exact (h this).elim
            · exact hend
        simp only [ge_iff_le]
        rename_i tail_ih
        apply tail_ih
        · exact tail_path
        · constructor
          · intro x hx
            have hx' : x ∈ u :: v :: rest' := by
              simp [hx]
            -- exact hp_verts x hx'
            sorry
          · sorry
  · apply sInf_le
    refine ⟨[i, j], ⟨?path_valid, ?path_start, ?path_end⟩, ?verts⟩
    · simp [validPath]
      simp [path_valid G i j h]
    · simp [pathStart]
    · simp [pathEnd]
    · constructor
      · intro v hv
        cases hv
        · left
          rfl
        · right
          rename_i h2
          cases h2 with
          | head h2_eq_i =>
            rfl
          | tail h2_eq_j =>
            contradiction
      · simp [initDist, h, ↓reduceIte]

-- Initial distance function is the same as the shortest distance
-- considering only paths that use vertices in the empty list
-- This is the base case for the induction in fw_invariant
lemma initDist_eq_sInf {n : ℕ} (G : Graph n) (i j : Fin n) :
  initDist G i j = distUpToList G [] i j := by
  simp only [distUpToList, List.not_mem_nil, false_or]
  by_cases h : i = j
  · -- case i = j
    simp only [h, or_self]
    exact initDist_eq_sInf_i_eq_j G j
  · -- case i ≠ j
    exact initDist_eq_sInf_i_neq_j G i j h

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

lemma exists_path_weight_eq_distUpToList {n : ℕ} (G : Graph n) (ks : List (Fin n)) (i j : Fin n) :
  ∃ p, isPathFromTo G p i j ∧ (∀ v ∈ p, v ∈ ks) ∧ pathWeight G p = distUpToList G ks i j := by
  -- apply sInf_exists
  -- intro w hw
  -- rcases hw with ⟨p, hp_path, hp_vertices, hp_weight⟩
  -- exact ⟨p, hp_path, hp_vertices, hp_weight⟩
  sorry

lemma pathWeight_append_tail  {n : ℕ} (G : Graph n) (p1 p2 : Path n) :
  pathWeight G (p1 ++ p2.tail)
    = pathWeight G p1 + pathWeight G p2 := by
  induction p1 with
  | nil =>
    simp
    sorry
  | cons u ps ih =>
    simp only [List.cons_append]
    have hpq : pathEnd (u :: ps) = pathStart (p2.tail) := by
      simp [pathStart]
      sorry
    have ih' : pathWeight G (ps ++ p2.tail) = pathWeight G ps + pathWeight G p2 := by
      apply ih
    sorry

lemma validPath_append_tail {n : ℕ} (G : Graph n) (p1 p2 : Path n)
  (hvalid1 : validPath G p1) (hvalid2 : validPath G p2) (h_link : pathEnd p1 = pathStart p2) :
  validPath G (p1 ++ p2.tail) := by
    sorry

lemma pathStart_append_tail {n : ℕ} (G : Graph n) (p1 p2 : Path n)
  (ks : List (Fin n)) (i j k : Fin n) (h_link : pathEnd p1 = pathStart p2)
  (hvalid1 : validPath G p1) (hstart1 : pathStart p1 = some i) (hend1 : pathEnd p1 = some k)
  (hvalid2 : validPath G p2) (hstart2 : pathStart p2 = some k) (hend2 : pathEnd p2 = some j) :
  pathStart (p1 ++ p2.tail) = pathStart p1 := by
    sorry

lemma pathEnd_append_tail {n : ℕ} (G : Graph n) (p1 p2 : Path n)
  (ks : List (Fin n)) (i j k : Fin n) (h_link : pathEnd p1 = pathStart p2)
  (hvalid1 : validPath G p1) (hstart1 : pathStart p1 = some i) (hend1 : pathEnd p1 = some k)
  (hvalid2 : validPath G p2) (hstart2 : pathStart p2 = some k) (hend2 : pathEnd p2 = some j) :
  pathEnd (p1 ++ p2.tail) = pathEnd p2 := by
    sorry


-- helper lemma for showing that any path from i to j that can use k is less than
-- or equal to the path that goes via k
lemma add_vertex_split {n : ℕ} (G : Graph n) (ks : List (Fin n)) (k i j : Fin n) :
  distUpToList G (k :: ks) i j ≤ distUpToList G ks i k + distUpToList G ks k j := by
  -- apply infimum lemma
  unfold distUpToList
  apply csInf_le
  -- 1. BddBelow
  · refine ⟨0, ?_⟩
    intro w hw
    exact zero_le _
  -- 2. witness
  ·    -- extract paths
    rcases exists_path_weight_eq_distUpToList G ks i k with
      ⟨p1, hp1_path, hp1_verts, hp1_w⟩
    rcases exists_path_weight_eq_distUpToList G ks k j with
      ⟨p2, hp2_path, hp2_verts, hp2_w⟩
    -- define concatenation
    let p := p1 ++ p2.tail
    refine ⟨p, ?_, ?_, ?_⟩
    · have h_link :
        pathEnd p1 = pathStart p2 := by
          simp [getPathEnd G p1 i k hp1_path, getPathStart G p2 k j hp2_path]
      rcases hp1_path with ⟨hvalid1, hstart1, hend1⟩
      rcases hp2_path with ⟨hvalid2, hstart2, hend2⟩
      refine ⟨?_, ?_, ?_⟩
      · -- show validPath G p
        exact validPath_append_tail G p1 p2 hvalid1 hvalid2 h_link
      · -- show pathStart p = some i
        have pathStart_eq : pathStart p = pathStart p1 := by
          exact pathStart_append_tail G p1 p2 ks i j k
            h_link hvalid1 hstart1 hend1 hvalid2 hstart2 hend2
        simp [hstart1, pathStart_eq]
      · -- show pathEnd p = some j
        have pathEnd_eq : pathEnd p = pathEnd p2 := by
          exact pathEnd_append_tail G p1 p2 ks i j k
            h_link hvalid1 hstart1 hend1 hvalid2 hstart2 hend2
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
      rw [<- hp1_w]
      rw [<- hp2_w]
      unfold p
      rw [pathWeight_append_tail G p1 p2]

lemma distUpToList_le_of_path {n : ℕ} (G : Graph n)
  (ks : List (Fin n)) (i j : Fin n) (p : Path n)
  (hp_path : isPathFromTo G p i j)
  (hp_verts : ∀ v ∈ p, v ∈ ks ∨ v = i ∨ v = j) :
  distUpToList G ks i j ≤ pathWeight G p := by
    unfold distUpToList
    apply sInf_le
    use p

lemma isPathFromTo_prefix {n : ℕ} (G : Graph n)
  (p1 p2 : List (Fin n)) (i j k : Fin n)
  (h : isPathFromTo G (p1 ++ [k] ++ p2) i j) :
  isPathFromTo G (p1 ++ [k]) i k := by
  rcases h with ⟨h_valid, h_start, h_end⟩
  have h_valid_prefix : validPath G (p1 ++ [k]) := by
    exact validPath_prefix G p1 p2 k h_valid
  have h_start_prefix : pathStart (p1 ++ [k]) = some i := by
    exact pathStart_prefix p1 p2 i k h_start
  have h_end_prefix : pathEnd (p1 ++ [k]) = some k := by
    simp only [pathEnd_append_singleton]
  exact ⟨h_valid_prefix, h_start_prefix, h_end_prefix⟩

lemma isPathFromTo_suffix {n} (G : Graph n)
  (p1 p2 : List (Fin n)) (i j k : Fin n)
  (h : isPathFromTo G (p1 ++ [k] ++ p2) i j) :
  isPathFromTo G ([k] ++ p2) k j := by
  rcases h with ⟨hpath, hstart, hend⟩
  have hpath_p2 : validPath G ([k] ++ p2) := by
    exact validPath_suffix G p1 p2 k hpath
  have hj : pathEnd ([k] ++ p2) = j := by
    exact pathEnd_suffix n p1 p2 j k hend
  have hk : pathStart ([k] ++ p2) = k := by
    simp [pathStart]
  exact ⟨hpath_p2, hk, hj⟩

lemma pathWeight_append {n} (G : Graph n) (k : Fin n)
  (p q : List (Fin n)) :
  pathWeight G (p ++ [k] ++ q) =
    pathWeight G (p ++ [k]) + pathWeight G (k :: q) := by
    sorry

-- helper lemma showing that any path from i to j that can use k is at least as long
-- as the shorter of the path that doesn't use k and the path that goes via k
lemma min_le_list_with_k {n : ℕ} (G : Graph n) (ks : List (Fin n)) (k i j : Fin n) :
  min (distUpToList G ks i j) (distUpToList G ks i k + distUpToList G ks k j) ≤
    distUpToList G (k :: ks) i j := by
    obtain ⟨p, hp_path, hp_verts, hp_weight⟩ := exists_path_weight_eq_distUpToList G (k :: ks) i j
    by_cases h : k ∈ p
    · -- case 1: p uses k
      -- show distUpToList G ks i k + distUpToList G ks k j ≤ distUpToList G (k :: ks) i j
      -- i.e. any path from i to j that uses k can be split into a
      -- path from i to k and a path from k to j
      -- split at first occurrence of k
      let p1 := p.takeWhile (fun v => v ≠ k)           -- prefix before first k
      let p2 := p.drop (p1.length + 1)                 -- suffix after first k
      have hp_split : p = p1 ++ [k] ++ p2 :=
        takeWhile_drop_split k p h
      let p1_k := p1
      let p2_j := p2
      -- weights of prefix/suffix ≤ distUpToList on ks
      have h1 : distUpToList G ks i k ≤ pathWeight G (p1_k ++ [k]) :=
        distUpToList_le_of_path G ks i k (p1_k ++ [k])
          (by
            -- p1_k ++ [k] is a path from i → k
            have hp_path' : isPathFromTo G (p1 ++ [k] ++ p2) i j := by
              simpa [hp_split] using hp_path
            exact isPathFromTo_prefix G p1 p2 i j k hp_path'
          )
          (by
            -- all vertices in ks ∪ {i,k}
            intros v hv;
            simp only [List.mem_cons] at hp_verts
            have hv_p : v ∈ p := by
              -- v ∈ p1 ++ [k] ⊆ p1 ++ [k] ++ p2 = p
              have : v ∈ p1 ++ [k] ++ p2 := by
                apply List.mem_append.mpr
                exact Or.inl hv
              simpa [hp_split] using this
            specialize hp_verts v hv_p
            cases hp_verts with
            | inl hk =>
                -- v = k
                exact Or.inr (Or.inr hk)
            | inr hks =>
                -- v ∈ ks
                exact Or.inl hks
            )
      have h2 : distUpToList G ks k j ≤ pathWeight G ([k] ++ p2_j) := by
        have hp_k_j : isPathFromTo G ([k] ++ p2_j) k j := by
          -- suffix of a path starting at k
          -- this is the dual of your prefix lemma
          have hp_path' : isPathFromTo G (p1 ++ [k] ++ p2) i j := by
            simpa [hp_split] using hp_path
          exact isPathFromTo_suffix G p1 p2 i j k hp_path'
        have hp_verts_p2 : ∀ v ∈ ([k] ++ p2_j), v ∈ ks ∨ v = k ∨ v = j := by
          intros v hv
          have hv_p : v ∈ p := by
            have : v ∈ p1 ++ [k] ++ p2 := by
              apply List.mem_append.mpr
              simp only [List.cons_append, List.nil_append,
                        List.mem_cons, p2_j] at hv
              cases hv with
              | inl hk =>
                subst hk
                left
                simp
              | inr hv_p2 =>
                right
                simp [hv_p2]
            simpa [hp_split] using this
          specialize hp_verts v hv_p
          -- hp_verts : v ∈ k :: ks
          simp only [List.mem_cons] at hp_verts
          cases hp_verts with
          | inl hk => exact Or.inr (Or.inl hk)
          | inr hks => exact Or.inl hks
        exact distUpToList_le_of_path G ks k j ([k] ++ p2_j) hp_k_j hp_verts_p2
      -- pathWeight p = pathWeight p1 + pathWeight p2
      have hp_sum :
        pathWeight G p = pathWeight G (p1_k ++ [k]) + pathWeight G ([k] ++ p2_j) := by
        -- use hp_split + pathWeight_append lemma
          simp only [hp_split, List.append_assoc, List.cons_append, List.nil_append]
          have hlist : p1 ++ k :: p2 = (p1 ++ [k]) ++ p2 := by
            simp [List.append_assoc, List.cons_append, List.nil_append]
          rw [hlist]
          apply pathWeight_append
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
      -- show distUpToList G ks i j ≤ distUpToList G (k :: ks) i j
      -- i.e. any path from i to j that doesn't use k is still a valid path
      --  when we add k to the list of intermediate vertices
      have hp_verts_ks : ∀ v ∈ p, v ∈ ks ∨ v = i ∨ v = j := by
        intro v hv
        have hmem := hp_verts v hv
        rcases List.mem_cons.mp hmem with h' | h'
        · -- v = k
          subst h'
          exact False.elim (h hv)
        · -- v ∈ ks
          exact Or.inl h'
      have hA :
        distUpToList G ks i j ≤ pathWeight G p :=
        distUpToList_le_of_path G ks i j p hp_path hp_verts_ks
      have : distUpToList G ks i j ≤ distUpToList G (k :: ks) i j := by
        rw [<- hp_weight]
        exact hA
      -- exact this
      have h1 := (min_le_left (distUpToList G ks i j)
        (distUpToList G ks i k + distUpToList G ks k j)).trans hA
      rw [hp_weight] at h1
      exact h1

-- proof for adding vertex k to the list of intermediate vertices
lemma sInf_split {n : ℕ} (G : Graph n) (ks : List (Fin n)) (k i j : Fin n) :
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
      exact add_vertex_le G ks k i j
    · -- show distUpToList G (k :: ks) i j ≤ distUpToList G ks i k + distUpToList G ks k j
      -- i.e. any path from i to j that can use k can be split into
      -- a path from i to k and a path from k to j
      exact add_vertex_split G ks k i j

end FYP
