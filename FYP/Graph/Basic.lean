import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic

namespace FYP

structure Graph (n : ℕ) where
    (w : Fin n → Fin n → ℕ∞)
    (self_weight : ∀ i, w i i = 0)

end FYP
