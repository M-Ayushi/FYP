import FYP.Graph.Basic
import FYP.Graph.Path
import FYP.Graph.PathLemmas
import FYP.FloydWarshall.Definitions
import FYP.FloydWarshall.Lemmas

namespace FYP

-- applying fwStep l times is the same as applying fwStep to the list of vertices in l
lemma fw_invariant {n : ℕ} (G : Graph n) :
  ∀ (l : List (Fin n)) (i j : Fin n),
    (l.foldl fwStep (initDist G)) i j = distUpToList G l i j := by
      intro l
      induction l with
      -- base case: no intermediate vertices
      | nil =>
        apply initDist_eq_sInf
      -- inductive step: add vertex k to the list of intermediate vertices
      | cons k ks ih =>
        intro i j
        simp only [List.foldl]
        rw [foldl_fwStep_swap]
        simp only [fwStep]
        rw [ih i j, ih i k, ih k j]
        rw [sInf_split G ks k i j]

theorem floydWarshall_correct (G : Graph n) (i j : Fin n) :
  floydWarshall G i j = dist G i j := by
  simp only [floydWarshall]
  rw [fw_invariant G (List.finRange n) i j]
  simp only [dist, distUpToList]
  -- show that distUpToList G (List.finRange n) i j = dist G i j
  -- this should follow from the fact that
  -- distUpToList G (List.finRange n) i j is the infimum over all
  -- paths from i to j, which is exactly dist G i j
  apply le_antisymm
  · -- show distUpToList G (List.finRange n) i j ≤ dist
    apply le_sInf
    intro w hw
    rcases hw with ⟨p, hp_path, hp_vertices, hp_weight⟩
    apply sInf_le
    refine ⟨p, hp_path, ?_, rfl⟩
    -- show that p only uses vertices in List.finRange n
    -- this should be true since List.finRange n contains all vertices
    simp [List.mem_finRange, true_or]
  · -- show dist G i j ≤ distUpToList G (List.finRange n) i j
    simp

end FYP
