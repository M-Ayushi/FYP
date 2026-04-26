import FYP.Graph.PathLemmas
import FYP.FloydWarshall.Definitions
import FYP.FloydWarshall.FWStepLemmas

namespace FYP

-- proof for adding vertex k to the list of intermediate vertices
lemma fwStep_invariant (ks : List (Fin n)) (k i j : Fin n) :
  min (distUpToList G ks i j) (distUpToList G ks i k + distUpToList G ks k j)
    = distUpToList G (k :: ks) i j := by
  apply le_antisymm
  · -- lower bound: show min ... ≤ distUpToList G (k :: ks) i j
    obtain ⟨p, hp_path, hp_verts, hp_weight⟩ :=
      exists_path_weight_eq_distUpToList G (k :: ks) i j
    by_cases h : k ∈ p
    · exact fwStep_lower_bound_with_k G ks k i j p hp_path hp_verts hp_weight h
    · exact fwStep_lower_bound_without_k G ks k i j p hp_path hp_verts hp_weight h
  · -- upper bound: show distUpToList G (k :: ks) i j ≤ min ...
    apply le_min
    · -- distUpToList G (k :: ks) i j ≤ distUpToList G ks i j
      have subsetofList : ∀ v, v ∈ ks → v ∈ k :: ks := by
        intro v hv
        exact List.mem_cons_of_mem k hv
      exact distUpToList_mono ks (k :: ks) subsetofList i j
    · -- distUpToList G (k :: ks) i j ≤ distUpToList G ks i k + distUpToList G ks k j
      exact fwStep_upper_bound_via_k G ks k i j

lemma fw_invariant :
  ∀ (l : List (Fin n)) (i j : Fin n),
    (l.foldl fwStep (initDist G)) i j = distUpToList G l i j := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    apply initDist_eq_sInf
  | append_singleton ks k ih =>
    intro i j
    simp only [List.foldl_append, List.foldl]
    have hfun: (List.foldl fwStep (initDist G) ks) =
        (fun i j => distUpToList G ks i j) :=
      funext (fun i => funext (fun j => ih i j))
    simp [hfun, fwStep, fwStep_invariant ks k i j]
    simp [distUpToList, or_comm]

theorem floydWarshall_correct (G : Graph n) (i j : Fin n) :
  floydWarshall G i j = shortestDist G i j := by
  simp only [floydWarshall]
  rw [fw_invariant (List.finRange n) i j]
  -- distUpToList G (List.finRange n) i j = shortestDist G i j
  simp only [shortestDist, distUpToList]
  apply le_antisymm
  · -- distUpToList G (List.finRange n) i j ≤ shortestDist G i j
    apply le_sInf
    intro w hw
    rcases hw with ⟨p, hp_path, hp_vertices, hp_weight⟩
    apply sInf_le
    refine ⟨p, hp_path, ?_, rfl⟩
    simp [List.mem_finRange, true_or]
  · -- shortestDist G i j ≤ distUpToList G (List.finRange n) i j
    simp

end FYP
