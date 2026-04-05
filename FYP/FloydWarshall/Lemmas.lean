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
  · -- i ≠ j
    simp only [initDist, h, ↓reduceIte]
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
          ·
            sorry
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

lemma fwStep_comm {n : ℕ}
  (d : Fin n → Fin n → ℕ∞) (k x : Fin n) :
  fwStep (fwStep d k) x = fwStep (fwStep d x) k := by
  funext i j
  apply le_antisymm

  · -- ≤ direction
    simp [fwStep]
    -- goal:
    -- min (min (d i j) (d i k + d k j))
    --     (min (d i x) (d i k + d k x) + min (d x j) (d x k + d k j))
    -- ≤
    -- min (min (d i j) (d i x + d x j))
    --     (min (d i k) (d i x + d x k) + min (d k j) (d k x + d x j))

    -- apply min_le_iff.mpr
    -- sorry
    constructor
    · -- show first min ≤ LHS
      constructor
      · -- show d i j ≤ LHS
        sorry
      -- · -- show d i x + d x j ≤ LHS
      --   sorry
    · -- show second min ≤ LHS
      sorry

    -- case 1
    -- · -- show first min ≤ RHS
      -- apply le_trans (min_le_left _ _)
      -- apply min_le_iff.mpr
      -- left
      -- rfl
      -- sorry
    -- case 2
    -- · -- show second term ≤ RHS
      -- apply le_trans (min_le_right _ _)
      -- apply min_le_iff.mpr
      -- right
      -- apply add_le_add
      -- sorry
      -- · apply min_le_iff.mpr
      --   right
      --   apply add_le_add <;> exact le_rfl

      -- · apply min_le_iff.mpr
      --   right
      --   apply add_le_add <;> exact le_rfl

  · -- ≥ direction (symmetric)
    simp [fwStep]
    sorry
    -- apply min_le_iff.mpr
    -- constructor

    -- · apply le_trans (min_le_left _ _)
    --   apply min_le_iff.mpr
    --   left
    --   rfl

    -- · apply le_trans (min_le_right _ _)
    --   apply min_le_iff.mpr
    --   right
    --   apply add_le_add

    --   · apply min_le_iff.mpr
    --     right
    --     apply add_le_add <;> exact le_rfl

    --   · apply min_le_iff.mpr
    --     right
    --     apply add_le_add <;> exact le_rfl

-- helper lemma for swapping fwStep and foldl
lemma foldl_fwStep_swap {n : ℕ} (ks : List (Fin n))
  (d : Fin n → Fin n → ℕ∞) (k i j : Fin n) :
  (List.foldl fwStep (fwStep d k) ks) i j =
    fwStep (List.foldl fwStep d ks) k i j := by
    revert d
    induction ks with
    | nil =>
      simp
    | cons x xs ih =>
      intro d
      simp only [List.foldl] at *
      simp only [fwStep_comm d k x]
      exact ih (d := fwStep d x)

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
        sorry
      · -- show pathStart p = some i
        sorry
      · -- show pathEnd p = some j
        sorry
    · sorry
    · sorry

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
