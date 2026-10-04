import AFTD.Prelude

/-!
# spi_ite_null_signal

Topic: mechanism_design   Node: d726f751da6c

A signal of probability m >= 0 whose posterior mean is below T contributes nothing to the acceptance probability.
-/

/-- A signal of probability `m ≥ 0` whose posterior mean `c` is below `T` contributes nothing to the acceptance probability. -/
lemma spi_ite_null_signal (T m c : ℝ) (hm : 0 ≤ m) (hc : c < T) :
    (if T * m ≤ m * c then m else 0) = 0 := by
  split_ifs with h
  · nlinarith
  · rfl
