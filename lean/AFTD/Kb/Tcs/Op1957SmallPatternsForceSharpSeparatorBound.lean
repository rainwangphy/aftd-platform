import AFTD.Prelude

/-!
# op1957_small_patterns_force_sharp_separator_bound

Topic: graphs   Node: 4958944ea3b7

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Small patterns force sharp separator bound.
-/

set_option maxHeartbeats 2000000

theorem op1957_small_patterns_force_sharp_separator_bound
    (c m eb a b0 b1 b2 b3 c0 c1 c2 c3 : ℕ)
    (hEB : m ≤ eb)
    (hpatterns : a=1 ∧
      ((c1=3 ∧ c2+c3=0 ∧ b0+c0+b2+c2+b3+c3+eb+4=c) ∨
       (c1=1 ∧ c2+c3=2 ∧ (1≤c2 → c2=1 ∧ b2+c2=1) ∧
         (1≤c3 → c3=1 ∧ b3+c3=1))))
    (hrep2C : 1≤c2 → a+b0+b1+b3+eb+c0+c1+c3+3≤c) :
    m+(if 1≤c2 then 1 else 0)+(if 1≤c3 then 1 else 0)+4≤c := by
  rcases hpatterns with ⟨ha,hfirst | hsecond⟩
  · have h2 : c2=0 := by omega
    have h3 : c3=0 := by omega
    simp [h2,h3]
    omega
  · have h2 : c2=1 := by
      by_cases hz : c2=0
      · have hh := hsecond.2.2.2 (by omega)
        omega
      · have hh := hsecond.2.2.1 (by omega)
        omega
    have h3 : c3=1 := by omega
    have hh := hrep2C (by omega)
    simp [h2,h3]
    omega
