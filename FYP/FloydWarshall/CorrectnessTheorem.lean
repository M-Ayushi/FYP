import FYP.Graph.Basic
import FYP.Graph.Path
import FYP.Graph.PathLemmas
import FYP.FloydWarshall.Definitions
import FYP.FloydWarshall.Lemmas

namespace FYP

lemma fw_invariant {n : ℕ} (G : Graph n) :
  ∀ (l : List (Fin n)) (i j : Fin n),
    (l.foldl fwStep (initDist G)) i j = distUpToList G l i j := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    apply initDist_eq_sInf
  | append_singleton ks k ih =>
    intro i j
    simp only [List.foldl_append, List.foldl]
    -- Now LHS is: fwStep (ks.foldl fwStep (initDist G)) k i j
    -- IH gives:   (ks.foldl fwStep (initDist G)) i j = distUpToList G ks i j
    -- So we can rewrite the inner matrix using ih
    have hfun: (List.foldl fwStep (initDist G) ks) =
        (fun i j => distUpToList G ks i j) :=
      funext (fun i => funext (fun j => ih i j))
    rw [hfun]
    -- Now LHS is: fwStep (distUpToList G ks) k i j
    --           = min (distUpToList G ks i j)
    --                 (distUpToList G ks i k + distUpToList G ks k j)
    simp only [fwStep]
    -- RHS: distUpToList G (ks ++ [k]) i j
    rw [sInf_split G ks k i j]
    simp [distUpToList, or_comm]

theorem floydWarshall_correct (G : Graph n) (i j : Fin n) :
  floydWarshall G i j = dist G i j := by
  simp only [floydWarshall]
  rw [fw_invariant G (List.finRange n) i j]
  -- show that distUpToList G (List.finRange n) i j = dist G i j
  -- follows from the fact that distUpToList G (List.finRange n) i j
  -- is the infimum over all paths from i to j, which is exactly dist G i j
  simp only [dist, distUpToList]
  apply le_antisymm
  · -- show distUpToList G (List.finRange n) i j ≤ dist
    apply le_sInf
    intro w hw
    rcases hw with ⟨p, hp_path, hp_vertices, hp_weight⟩
    apply sInf_le
    refine ⟨p, hp_path, ?_, rfl⟩
    -- show that p only uses vertices in List.finRange n
    -- true since List.finRange n contains all vertices
    simp [List.mem_finRange, true_or]
  · -- show dist G i j ≤ distUpToList G (List.finRange n) i j
    simp

end FYP
