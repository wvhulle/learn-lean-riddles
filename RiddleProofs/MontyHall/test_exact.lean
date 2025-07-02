import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv

open ENNReal

-- Test if the exact pattern works
example {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right (↑a) (↑b) (by norm_cast; assumption) (ENNReal.natCast_ne_top c)
