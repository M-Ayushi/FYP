import Mathlib

namespace FYP

abbrev Weight := ℕ∞

structure Graph (n : ℕ) where
    w : Fin n → Fin n → ℕ∞

end FYP
