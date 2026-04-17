import FYP.Graph.Basic
import FYP.Graph.Path

namespace FYP

lemma rebuild_path {p : Path n} (x : Fin n) (hx : x = pathStart p) :
  p = [x] ++ p.tail := by
    cases p with
    | nil =>
      contradiction
    | cons v vs =>
      simp [pathStart] at hx
      simp [hx]

-- Path validity lemmas

lemma path_valid {n : ℕ} (G : Graph n) (i j : Fin n) (h : i ≠ j) :
  ¬G.w i j = ⊤ := by sorry

lemma validPath_prefix {n : ℕ} (G : Graph n)
  (p1 p2 : List (Fin n)) (k : Fin n) (h : validPath G (p1 ++ [k] ++ p2)) :
  validPath G (p1 ++ [k]) := by
  induction p1 with
  | nil =>
      simp [validPath]
  | cons hd tl ih =>
      simp only [List.cons_append, List.append_assoc,
                List.nil_append] at h
      cases tl with
      | nil =>
          -- p1 = [hd]
          simp only [List.nil_append] at h
          exact ⟨ h.1, trivial⟩
      | cons v rest =>
          -- main recursive case
          simp only [List.cons_append] at h
          rcases h with ⟨h_edge, h_tail⟩
          have h_tail' : validPath G (v :: (rest ++ [k] ++ p2)) := by
            simpa [List.append_assoc] using h_tail
          have h_mid : validPath G (v :: rest ++ [k]) :=
            ih h_tail'
          exact ⟨h_edge, h_mid⟩

lemma validPath_suffix {n : ℕ} (G : Graph n)
  (p1 p2 : List (Fin n)) (k : Fin n) (h : validPath G (p1 ++ [k] ++ p2)) :
  validPath G ([k] ++ p2) := by
  induction p1 with
  | nil =>
      simpa using h
  | cons hd tl ih =>
    have : validPath G (tl ++ [k] ++ p2) := by
      cases tl with
      | nil =>
        simp only [List.cons_append] at h
        exact h.2
      | cons x xs =>
        simpa using h.right
    exact ih this

lemma validPath_append_tail {n : ℕ} (G : Graph n) (p1 p2 : Path n)
  (h_link : pathEnd p1 = pathStart p2) (hvalid1 : validPath G p1)
  (hvalid2 : validPath G p2) : validPath G (p1 ++ p2.tail) := by
    induction p1 with
    | nil =>
      contradiction
    | cons x xs =>
      cases xs with
      | nil =>
        have same_path : p2 = [x] ++ List.tail p2 := by
          exact rebuild_path x h_link
        rw [<- same_path]
        exact hvalid2
      | cons y ys =>
        rename_i ih
        have hlink' : pathEnd (y :: ys) = pathStart p2 := by
          rw [<- h_link]
          exact (Option.map_inj_right fun x y a ↦ a).mp rfl
        have hvalid' : validPath G (y :: ys) := by
          exact validPath_suffix G [x] ys y hvalid1
        have ih' := ih hlink' hvalid'
        simp only [List.cons_append, validPath, ne_eq]
        constructor
        · simp only [validPath, ne_eq] at hvalid1
          exact hvalid1.1
        · exact ih'

-- Path start/end lemmas

lemma pathStart_prefix {n : ℕ} (p1 p2 : List (Fin n)) (k : Fin n) :
  pathStart (p1 ++ [k]) = pathStart (p1 ++ [k] ++ p2) := by
    cases p1 with
    | nil =>
      simp [pathStart]
    | cons hd tl =>
      simp [pathStart]

lemma pathStart_append_tail {n : ℕ} (p1 p2 : Path n) (i : Fin n)
  (hstart1 : pathStart p1 = some i) :
  pathStart (p1 ++ p2.tail) = pathStart p1 := by
    unfold pathStart
    have hp1_ne_nil : p1 ≠ [] := by
      intro h
      have : pathStart p1 = none := by
        simp [h, pathStart]
      rw [hstart1] at this
      contradiction
    cases p1 with
    | nil =>
      contradiction
    | cons x xs =>
      simp

lemma pathEnd_append {n : ℕ} (p1 p2 : Path n) (h : p2 ≠ []) :
  pathEnd (p1 ++ p2) = pathEnd p2 := by
    induction p1 with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.cons_append]
      have hne : tl ++ p2 ≠ [] := by
        intro heq
        simp only [List.append_eq_nil_iff] at heq
        exact h heq.2
      cases htl : (tl ++ p2) with
      | nil => exact absurd htl hne
      | cons a as =>
        simp only [pathEnd]
        rw [<- htl]
        simp [ih]

lemma pathEnd_suffix (n : ℕ) (p1 p2 : List (Fin n)) (k : Fin n) :
  pathEnd ([k] ++ p2) = pathEnd (p1 ++ [k] ++ p2) := by
    have h := pathEnd_append p1 ([k] ++ p2) (by simp)
    simp at h
    simp only [List.cons_append, List.nil_append, List.append_assoc]
    exact h.symm

lemma pathEnd_append_tail {n : ℕ} (p1 p2 : Path n)
  (j : Fin n) (h_link : pathEnd p1 = pathStart p2)
  (hend2 : pathEnd p2 = some j) :
  pathEnd (p1 ++ p2.tail) = pathEnd p2 := by
    cases p2 with
    | nil =>
      contradiction
    | cons y ys =>
      cases ys with
      | nil =>
        simp only [List.tail_cons, List.append_nil, pathEnd]
        simp only [pathStart] at h_link
        exact h_link
      | cons z zs =>
        have h1 : pathEnd (y :: z :: zs) = pathEnd (z :: zs) := by
          simp [pathEnd]
        simp only [List.tail_cons, h1]
        exact pathEnd_append p1 (z :: zs) (by simp)

-- Path weight lemmas

lemma pathWeight_split (G : Graph n) (v : Fin n) (vs : List (Fin n))
  (h : vs ≠ []) : pathWeight G (v :: vs) = G.w v (vs.head h) + pathWeight G vs := by
    cases vs with
    | nil => contradiction
    | cons u rest => simp [pathWeight]

lemma pathWeight_concat {n : ℕ} (G : Graph n) :
  ∀ p q : Path n,
    pathEnd p = pathStart q →
      pathWeight G (concatPath p q) =
        pathWeight G p + pathWeight G q := by
  intro p q hpq
  induction p with
  | nil =>
    simp [concatPath, pathWeight]
  | cons v vs ih =>
    cases vs with
    | nil =>
      have expand_q : q = v :: q.tail := by
        simp only [pathEnd] at hpq
        exact rebuild_path v hpq
      rw [expand_q]
      simp [concatPath, pathWeight, Graph.self_weight]
    | cons u rest =>
      simp only [concatPath, pathWeight_cons]
      have hpq' : pathEnd (u :: rest) = pathStart q := by
        simpa [pathEnd, concatPath] using hpq
      have ih' := ih hpq'
      cases rest with
      | nil =>
        have expand_q : q = u :: q.tail := by
          simp only [pathEnd] at hpq
          exact rebuild_path u hpq
        rw [expand_q]
        simp [concatPath, pathWeight_cons, Graph.self_weight]
      | cons w ws =>
        have non_empty : (concatPath (u :: w :: ws) q) ≠ [] := by
          simp [concatPath]
        have getHead : ((concatPath (u :: w :: ws) q).head (non_empty)) = u := by
          simp [concatPath]
        have := pathWeight_split G v (concatPath (u :: w :: ws) q) (non_empty)
        simp [this, getHead, ih', add_assoc]

lemma pathWeight_append_tail {n : ℕ} (G : Graph n) (p1 p2 : Path n)
  (hvalid1 : validPath G p1) (hlink : pathEnd p1 = pathStart p2) :
  pathWeight G (p1 ++ p2.tail) = pathWeight G p1 + pathWeight G p2 := by
    induction p1 with
    | nil =>
      contradiction
    | cons x xs ih =>
      cases xs with
      | nil =>
        simp only [pathWeight]
        have rebuild_p2 : p2 = [x] ++ p2.tail := by
          exact rebuild_path x hlink
        rw [rebuild_p2]
        simp
      | cons y ys =>
        simp only [List.cons_append] at *
        have hvalid :validPath G (y :: ys) := by
          exact validPath_suffix G [x] ys y hvalid1
        have hlink' : pathEnd (y :: ys) = pathStart p2 := by
          simpa [pathEnd] using hlink
        have := ih hvalid hlink'
        simp [this, add_assoc]

lemma pathWeight_append {n} (G : Graph n) (k : Fin n)
  (p q : List (Fin n)) :
  pathWeight G (p ++ [k] ++ q) =
    pathWeight G (p ++ [k]) + pathWeight G (k :: q) := by
    induction p with
    | nil =>
      simp
    | cons v vs ih =>
      cases vs with
      | nil =>
        simp
      | cons u rest =>
        simp at ih
        simp [ih, add_assoc]

-- isPathFromTo lemmas

lemma isPathFromTo_prefix {n : ℕ} (G : Graph n)
  (p1 p2 : List (Fin n)) (i j k : Fin n)
  (h : isPathFromTo G (p1 ++ [k] ++ p2) i j) :
  isPathFromTo G (p1 ++ [k]) i k := by
  rcases h with ⟨h_valid, h_start, h_end⟩
  have h_valid_prefix : validPath G (p1 ++ [k]) := by
    exact validPath_prefix G p1 p2 k h_valid
  have h_start_prefix : pathStart (p1 ++ [k]) = some i := by
    rw [<- h_start]
    exact pathStart_prefix p1 p2 k
  have h_end_prefix : pathEnd (p1 ++ [k]) = some k := by
    exact pathEnd_append p1 ([k] ++ []) (by simp)
  exact ⟨h_valid_prefix, h_start_prefix, h_end_prefix⟩

lemma isPathFromTo_suffix {n} (G : Graph n)
  (p1 p2 : List (Fin n)) (i j k : Fin n)
  (h : isPathFromTo G (p1 ++ [k] ++ p2) i j) :
  isPathFromTo G ([k] ++ p2) k j := by
  rcases h with ⟨hpath, hstart, hend⟩
  have hpath_p2 : validPath G ([k] ++ p2) := by
    exact validPath_suffix G p1 p2 k hpath
  have hj : pathEnd ([k] ++ p2) = j := by
    rw [<- hend]
    exact pathEnd_suffix n p1 p2 k
  have hk : pathStart ([k] ++ p2) = k := by
    simp [pathStart]
  exact ⟨hpath_p2, hk, hj⟩

end FYP
