import FYP.Graph.PathLemmas

namespace FYP

lemma takeWhile_drop_split {n : ℕ} (k : Fin n)
  (p : List (Fin n)) (h : k ∈ p) :
  let p1 := List.takeWhile (fun v => v ≠ k) p
  let p2 := List.drop (p1.length + 1) p
  p = p1 ++ [k] ++ p2 := by
  induction p with
  | nil =>
      simp at h
  | cons hd tl ih =>
      by_cases h_hd : hd = k
      · -- k is at the head
        simp [h_hd]
      · -- k is in tail
        have h_tl : k ∈ tl := by
          simp only [List.mem_cons] at h
          cases h with
          | inl h_eq =>
            cases h_hd (Eq.symm h_eq)
          | inr h_in =>
            exact h_in
        specialize ih h_tl
        simp only [List.mem_cons, h_hd, not_false_eq_true, ne_eq,
                  decide_not, List.append_assoc, List.cons_append,
                  List.nil_append, List.takeWhile, decide_true,
                  List.length_cons, List.drop_succ_cons,
                  List.cons.injEq, true_and] at *
        exact ih

-- isPathFromTo lemmas

lemma isPathFromTo_prefix (p1 p2 : List (Fin n))
  (i k : Fin n) (h : isPathFromTo G (p1 ++ [k] ++ p2) i j) :
  isPathFromTo G (p1 ++ [k]) i k := by
    rcases h with ⟨ hvalid, hstart, hend ⟩
    have hvalid_prefix : validPath G (p1 ++ [k]) := by
      exact validPath_prefix p1 p2 k hvalid
    have hstart_prefix : pathStart (p1 ++ [k]) = some i := by
      simp [<- hstart, pathStart_prefix p1 p2 k]
    have hend_prefix : pathEnd (p1 ++ [k]) = some k := by
      exact pathEnd_append p1 [k] (by simp)
    exact ⟨ hvalid_prefix, hstart_prefix, hend_prefix ⟩

lemma isPathFromTo_suffix (p1 p2 : List (Fin n))
  (j k : Fin n) (h : isPathFromTo G (p1 ++ [k] ++ p2) i j) :
  isPathFromTo G ([k] ++ p2) k j := by
    rcases h with ⟨ hvalid, hstart, hend ⟩
    have hvalid_suffix : validPath G ([k] ++ p2) := by
      exact validPath_suffix p1 p2 k hvalid
    have hstart_suffix : pathStart ([k] ++ p2) = k := by
      simp [pathStart]
    have hend_suffix : pathEnd ([k] ++ p2) = j := by
      simp only [<- hend, pathEnd_suffix p1 p2 k]
    exact ⟨ hvalid_suffix, hstart_suffix, hend_suffix ⟩

lemma isPathFromTo_appendTail (G : Graph n) (i j : Fin n)
  (p1 p2 : Path n) (hvalid1 : validPath G p1)
  (hstart1 : pathStart p1 = some i) (hvalid2 : validPath G p2)
  (hend2 : pathEnd p2 = some j) (hlink : pathEnd p1 = pathStart p2) :
  isPathFromTo G (p1 ++ p2.tail) i j := by
    simp only [isPathFromTo, <- hstart1, <-hend2]
    have hvalid : validPath G (p1 ++ List.tail p2) := by
      exact validPath_append_tail p1 p2 hlink hvalid1 hvalid2
    have pathStart_eq : pathStart (p1 ++ p2.tail) = pathStart p1 := by
      exact pathStart_append_tail p1 p2 hstart1
    have pathEnd_eq : pathEnd (p1 ++ p2.tail) = pathEnd p2 := by
      exact pathEnd_append_tail p1 p2 hlink hend2
    exact ⟨ hvalid, pathStart_eq, pathEnd_eq ⟩

lemma pathWeight_eq_split_sum (k i j : Fin n) (p1 p2 : Path n)
  (hp_path : isPathFromTo G (p1 ++ [k] ++ p2) i j)
  : pathWeight G (p1 ++ [k] ++ p2) = pathWeight G (p1 ++ [k]) + pathWeight G ([k] ++ p2) := by
    have h_valid : validPath G (p1 ++ [k]) := by
      simp [isPathFromTo] at hp_path
      exact validPath_prefix p1 p2 k (by simp [hp_path.left])
    have h_end : pathEnd (p1 ++ [k]) = pathStart ([k] ++ p2) := by
      simp [pathEnd_append p1 [k] (by simp), pathStart, pathEnd]
    rw [<- pathWeight_append_tail (p1 ++ [k]) ([k] ++ p2) h_valid h_end]
    simp

end FYP
