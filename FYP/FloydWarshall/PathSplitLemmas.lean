import FYP.Graph.PathSplit
import FYP.FloydWarshall.DistanceLemmas

namespace FYP

lemma verts_split_left (ks : List (Fin n)) (k i : Fin n)
  (p p1 p2 : Path n) (hp_split : p = p1 ++ [k] ++ p2)
  (hp_verts : ∀ v ∈ p, v = k ∨ v ∈ ks)
  (split_prefix : isPathFromTo G (p1 ++ [k]) i k) :
  distUpToList G ks i k ≤ pathWeight G (p1 ++ [k]) := by
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
    exact distUpToList_le_of_path ks i k (p1 ++ [k]) split_prefix hp_verts_p1

lemma verts_split_right (ks : List (Fin n)) (k j : Fin n)
  (p p1 p2 : Path n) (hp_split : p = p1 ++ [k] ++ p2)
  (hp_verts : ∀ v ∈ p, v = k ∨ v ∈ ks)
  (split_suffix : isPathFromTo G ([k] ++ p2) k j) :
  distUpToList G ks k j ≤ pathWeight G ([k] ++ p2) := by
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
    exact distUpToList_le_of_path ks k j ([k] ++ p2) split_suffix hp_verts_p2

lemma fwStep_split_cost_le (ks : List (Fin n)) (k i j : Fin n)
  (p p1 p2 : Path n) (hp_split : p = p1 ++ [k] ++ p2)
  (hp_path : isPathFromTo G (p1 ++ [k] ++ p2) i j)
  (hp_verts : ∀ v ∈ p, v = k ∨ v ∈ ks) :
  distUpToList G ks i k + distUpToList G ks k j ≤ pathWeight G p := by
    have split_prefix := isPathFromTo_prefix p1 p2 i k hp_path
    have split_suffix := isPathFromTo_suffix p1 p2 j k hp_path
    have h1 : distUpToList G ks i k ≤ pathWeight G (p1 ++ [k]) :=
      verts_split_left ks k i p p1 p2 hp_split hp_verts split_prefix
    have h2 : distUpToList G ks k j ≤ pathWeight G ([k] ++ p2) :=
      verts_split_right ks k j p p1 p2 hp_split hp_verts split_suffix
    have hsum : pathWeight G (p1 ++ [k] ++ p2) =
        pathWeight G (p1 ++ [k]) + pathWeight G ([k] ++ p2) :=
      pathWeight_eq_split_sum k i j p1 p2 hp_path
    rw [hp_split, hsum]
    exact add_le_add h1 h2

end FYP
