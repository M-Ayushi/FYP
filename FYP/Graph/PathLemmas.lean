import FYP.Graph.Basic
import FYP.Graph.Path

namespace FYP

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

lemma path_valid {n : ℕ} (G : Graph n) (i j : Fin n) (h : i ≠ j) :
  ¬G.w i j = ⊤ := by sorry

lemma getPathStart {n : ℕ} (G : Graph n) (p : Path n)
  (i : Fin n) (k : Fin n) (h : isPathFromTo G p i k) :
  pathStart p = some i := by
  simp only [isPathFromTo] at h
  exact h.2.1

lemma getPathEnd {n : ℕ} (G : Graph n) (p : Path n)
  (i : Fin n) (k : Fin n) (h : isPathFromTo G p i k) :
  pathEnd p = some k := by
  simp only [isPathFromTo] at h
  exact h.2.2

lemma pathEnd_cons {n : ℕ} (u v : Fin n) (rest : List (Fin n)) :
  pathEnd (u :: v :: rest) = pathEnd (v :: rest) := by
  cases rest with
  | nil =>
      -- pathEnd [x] = some x
      simp [pathEnd]
  | cons y ys =>
      -- pathEnd (x :: y :: ys) = pathEnd (y :: ys)
      simp [pathEnd]

end FYP
