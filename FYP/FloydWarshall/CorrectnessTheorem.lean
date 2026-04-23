import FYP.Graph.Basic
import FYP.Graph.Path
import FYP.Graph.PathLemmas
import FYP.FloydWarshall.Definitions
import FYP.FloydWarshall.Lemmas

namespace FYP

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
