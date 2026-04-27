import FYP.Graph.Path

namespace FYP

lemma rebuild_path {p : Path n} (x : Fin n) (hx : x = pathStart p) :
  p = [x] ++ p.tail := by
    cases p with
    | nil => contradiction
    | cons v vs =>
      simp [pathStart] at hx
      simp [hx]

-- Path validity lemmas

-- Left as sorry
-- If an edge weight is infinite, then there is no direct edge
-- between those vertices.
-- But the edge weight will always be either a finite number or ∞
-- Thus can be interpreted as always existing, but possibly with infinite weight.
lemma path_valid {n} (G : Graph n) (i j : Fin n) (h : i ≠ j) :
  ¬G.w i j = ⊤ := by sorry

lemma validPath_prefix (p1 p2 : List (Fin n))
  (k : Fin n) (h : validPath G (p1 ++ [k] ++ p2)) :
  validPath G (p1 ++ [k]) := by
    induction p1 with
    | nil => simp [validPath]
    | cons hd tl ih =>
      cases tl with
      | nil => exact ⟨ h.1, trivial ⟩
      | cons v rest =>
        rcases h with ⟨ hedge, htail ⟩
        have htail' : validPath G (v :: (rest ++ [k] ++ p2)) := by
          simpa [List.append_assoc] using htail
        exact ⟨ hedge, ih htail' ⟩

lemma validPath_suffix (p1 p2 : List (Fin n))
  (k : Fin n) (h : validPath G (p1 ++ [k] ++ p2)) :
  validPath G ([k] ++ p2) := by
    induction p1 with
    | nil => exact h
    | cons hd tl ih =>
      have : validPath G (tl ++ [k] ++ p2) := by
        cases tl with
        | nil => exact h.2
        | cons x xs => exact h.2
      exact ih this

lemma validPath_append_tail (p1 p2 : Path n)
  (hlink : pathEnd p1 = pathStart p2) (hvalid1 : validPath G p1)
  (hvalid2 : validPath G p2) : validPath G (p1 ++ p2.tail) := by
    induction p1 with
    | nil => contradiction
    | cons x xs =>
      cases xs with
      | nil =>
        simp [<- rebuild_path x hlink, hvalid2]
      | cons y ys =>
        rename_i ih
        have hlink' : pathEnd (y :: ys) = pathStart p2 := by
          simp [<- hlink, pathEnd]
        have hvalid' : validPath G (y :: ys) := by
          exact validPath_suffix [x] ys y hvalid1
        constructor
        · simp only [validPath] at hvalid1
          exact hvalid1.1
        · exact ih hlink' hvalid'

-- Path start/end lemmas

lemma pathStart_prefix (p1 p2 : List (Fin n)) (k : Fin n) :
  pathStart (p1 ++ [k]) = pathStart (p1 ++ [k] ++ p2) := by
    cases p1 with
    | nil => simp [pathStart]
    | cons hd tl => simp [pathStart]

lemma pathStart_append_tail (p1 p2 : Path n)
  (hstart1 : pathStart p1 = some k) :
  pathStart (p1 ++ p2.tail) = pathStart p1 := by
    unfold pathStart
    cases p1 with
    | nil => contradiction
    | cons x xs => simp

lemma pathEnd_append (p1 p2 : Path n) (h : p2 ≠ []) :
  pathEnd (p1 ++ p2) = pathEnd p2 := by
    induction p1 with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.cons_append]
      cases htl : (tl ++ p2) with
      | nil =>
        simp [h] at htl
      | cons a as =>
        simp [pathEnd, <- htl, ih]

lemma pathEnd_suffix (p1 p2 : List (Fin n)) (k : Fin n) :
  pathEnd ([k] ++ p2) = pathEnd (p1 ++ [k] ++ p2) := by
    have h := pathEnd_append p1 ([k] ++ p2) (by simp)
    simp only [List.append_assoc]
    exact h.symm

lemma pathEnd_append_tail (p1 p2 : Path n)
  (h_link : pathEnd p1 = pathStart p2) (hend2 : pathEnd p2 = some j) :
  pathEnd (p1 ++ p2.tail) = pathEnd p2 := by
    cases p2 with
    | nil => contradiction
    | cons y ys =>
      cases ys with
      | nil =>
        simpa [List.tail_cons, List.append_nil, pathEnd]
      | cons z zs =>
        exact pathEnd_append p1 (z :: zs) (by simp)

-- Path weight lemmas

lemma pathWeight_append_tail (p1 p2 : Path n)
  (hvalid1 : validPath G p1) (hlink : pathEnd p1 = pathStart p2) :
  pathWeight G (p1 ++ p2.tail) = pathWeight G p1 + pathWeight G p2 := by
    induction p1 with
    | nil => contradiction
    | cons x xs ih =>
      cases xs with
      | nil =>
        simp [<- rebuild_path x hlink]
      | cons y ys =>
        simp only [List.cons_append] at *
        have hvalid : validPath G (y :: ys) := by
          exact validPath_suffix [x] ys y hvalid1
        have hlink' : pathEnd (y :: ys) = pathStart p2 := by
          simpa [pathEnd] using hlink
        simp [ih hvalid hlink', add_assoc]

end FYP
