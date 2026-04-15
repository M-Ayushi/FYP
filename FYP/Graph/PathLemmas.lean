import FYP.Graph.Basic
import FYP.Graph.Path

namespace FYP

-- Path validity lemmas

lemma path_valid {n : ℕ} (G : Graph n) (i j : Fin n) (h : i ≠ j) :
  ¬G.w i j = ⊤ := by sorry

lemma validPath_prefix {n : ℕ} (G : Graph n)
  (p1 p2 : List (Fin n)) (k : Fin n) :
  validPath G (p1 ++ [k] ++ p2) → validPath G (p1 ++ [k]) := by
  intro h
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
  (p1 p2 : List (Fin n)) (k : Fin n) :
  validPath G (p1 ++ [k] ++ p2) → validPath G ([k] ++ p2) := by
  intro h
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
  (i j k : Fin n) (h_link : pathEnd p1 = pathStart p2)
  (hvalid1 : validPath G p1) (hstart1 : pathStart p1 = some i) (hend1 : pathEnd p1 = some k)
  (hvalid2 : validPath G p2) (hstart2 : pathStart p2 = some k) (hend2 : pathEnd p2 = some j) :
  validPath G (p1 ++ p2.tail) := by
    cases p2 with
    | nil =>
      -- contradiction: pathStart p2 = some k impossible
      simp only [pathStart] at hstart2
      contradiction
    | cons x xs =>
      -- from hstart2 you get x = k
      have hx : x = k := by
        simp only [pathStart, Option.some.injEq] at hstart2
        exact hstart2

      subst hx
      simp only [List.tail_cons]
      cases xs with
      | nil =>
        simp only [List.append_nil]
        exact hvalid1
      | cons y ys =>
        sorry

-- Path start/end lemmas

lemma getPathStart {n : ℕ} (G : Graph n) (p : Path n)
  (i : Fin n) (k : Fin n) (h : isPathFromTo G p i k) :
  pathStart p = some i := by
  simp only [isPathFromTo] at h
  exact h.2.1

lemma pathStart_prefix {n : ℕ} (p1 p2 : List (Fin n)) (i k : Fin n)
(h_start : pathStart (p1 ++ [k] ++ p2) = some i) :
pathStart (p1 ++ [k]) = some i := by
  cases p1 with
  | nil =>
    simp only [List.nil_append] at h_start
    exact h_start
  | cons hd tl =>
    simp only [List.cons_append] at h_start
    exact h_start

lemma getPathEnd {n : ℕ} (G : Graph n) (p : Path n)
  (i : Fin n) (k : Fin n) (h : isPathFromTo G p i k) :
  pathEnd p = some k := by
  simp only [isPathFromTo] at h
  exact h.2.2

lemma pathEnd_append_singleton {n : ℕ}
  (xs : List (Fin n)) (k : Fin n) :
  pathEnd (xs ++ [k]) = some k := by
  induction xs with
  | nil =>
      simp [pathEnd]
  | cons x xs ih =>
      simp [pathEnd, ih]

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

lemma pathEnd_suffix (n : ℕ) (p1 p2 : List (Fin n))
  (j k : Fin n) (hend : pathEnd (p1 ++ [k] ++ p2) = some j) :
  pathEnd ([k] ++ p2) = some j := by
    rw [List.append_assoc] at hend
    rwa [pathEnd_append p1 ([k] ++ p2) (by simp)] at hend

lemma pathStart_append_tail {n : ℕ} (G : Graph n) (p1 p2 : Path n)
  (i k : Fin n) (h_link : pathEnd p1 = pathStart p2)
  (hvalid1 : validPath G p1) (hstart1 : pathStart p1 = some i)
  (hend1 : pathEnd p1 = some k) :
  pathStart (p1 ++ p2.tail) = pathStart p1 := by
    unfold pathStart
    have hp1_ne_nil : p1 ≠ [] := by
      intro h
      have : pathStart p1 = none := by
        rw [h]
        simp [pathStart]
      rw [hstart1] at this
      contradiction
    cases p1 with
    | nil =>
      contradiction
    | cons x xs =>
      simp

lemma pathEnd_append_tail {n : ℕ} (G : Graph n) (p1 p2 : Path n)
  (ks : List (Fin n)) (i j k : Fin n) (h_link : pathEnd p1 = pathStart p2)
  (hvalid1 : validPath G p1) (hstart1 : pathStart p1 = some i) (hend1 : pathEnd p1 = some k)
  (hvalid2 : validPath G p2) (hstart2 : pathStart p2 = some k) (hend2 : pathEnd p2 = some j) :
  pathEnd (p1 ++ p2.tail) = pathEnd p2 := by
    have h : (List.tail p2) ≠ [] := by sorry
    have h2 := pathEnd_append p1 (List.tail p2) h
    simp [h2]
    sorry

-- Path weight lemmas

lemma pathWeight_concat {n : ℕ} (G : Graph n) :
  ∀ p q : Path n,
    pathEnd p = pathStart q →
      pathWeight G (concatPath p q) =
        pathWeight G p + pathWeight G q := by
  intro p q hpq
  induction p with
  | nil =>
    simp [concatPath]
  | cons u ps ih =>
    sorry

lemma pathWeight_nonneg {n : ℕ} (G : Graph n) (p : Path n) :
  0 ≤ pathWeight G p := by
  induction p with
  | nil => simp
  | cons u ps ih =>
    cases ps with
    | nil => simp
    | cons v rest => simp [pathWeight]

lemma pathWeight_append_tail {n : ℕ} (G : Graph n) (p1 p2 : Path n)
  (hvalid1 : validPath G p1) (hvalid2 : validPath G p2) (hlink : pathEnd p1 = pathStart p2) :
  pathWeight G (p1 ++ p2.tail) = pathWeight G p1 + pathWeight G p2 := by
    induction p1 with
    | nil =>
      contradiction
    | cons x xs ih =>
      cases xs with
      | nil =>
        simp only [pathWeight]
        have rebuild_p2 : p2 = [x] ++ p2.tail := by
          cases p2 with
          | nil =>
            contradiction
          | cons v vs =>
            simp only [List.tail_cons, List.cons_append, List.nil_append, List.cons.injEq, and_true]
            simp only [pathEnd, pathStart, Option.some.injEq] at hlink
            exact Fin.eq_of_val_eq (congrArg Fin.val (id (Eq.symm hlink)))
        rw [rebuild_p2]
        simp
      | cons y ys =>
        simp only [List.tail, List.cons_append, pathWeight_cons, pathWeight] at *
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
    sorry

end FYP
