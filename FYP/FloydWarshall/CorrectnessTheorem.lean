import FYP.Graph.Basic
import FYP.Graph.Path
import FYP.Graph.PathLemmas
import FYP.FloydWarshall.Definitions
import FYP.FloydWarshall.Lemmas

namespace FYP

-- applying fwStep l times is the same as applying fwStep to the list of vertices in l
lemma fw_invariant_old {n : ℕ} (G : Graph n) :
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
    rw [show (List.foldl fwStep (initDist G) ks) =
            (fun i j => distUpToList G ks i j) from funext (fun i => funext (fun j => ih i j))]
    -- Now LHS is: fwStep (distUpToList G ks) k i j
    --           = min (distUpToList G ks i j)
    --                 (distUpToList G ks i k + distUpToList G ks k j)
    simp only [fwStep]
    -- RHS: distUpToList G (ks ++ [k]) i j
    rw [← sInf_split G ks k i j]
    simp [distUpToList]
    simp only [or_comm (a := _ = k) (b := _ ∈ ks)]

theorem floydWarshall_correct (G : Graph n) (i j : Fin n) :
  floydWarshall G i j = dist G i j := by
  simp only [floydWarshall]
  rw [fw_invariant G (List.finRange n) i j]
  -- show that distUpToList G (List.finRange n) i j = dist G i j
  -- this follows from the fact that
  -- distUpToList G (List.finRange n) i j is the infimum over all
  -- paths from i to j, which is exactly dist G i j
  simp only [dist, distUpToList]
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
