import AFTD.Prelude
import AFTD.Kb.Tcs.WildTriplePartitionLargeOrderMassBound

/-!
# wild_triple_partition_term_antitone_odd_step

Topic: graphs   Node: 758397b1c691

Provenance: helper lemma. IN-359 new technical route for OP-306: algebraic continuation of the existing sufficient permutation resource bound. Exact rational audits8964/8965 verify the proposed step ratios on finite inputs, not a uniform theorem. Proof is still required; no wild-number bound or research advance is claimed.

For every odd q>=3 and admissible fixed cut size h>=1 with2*h<=q, the canonical triple-partition resource term wtc_term(q,h) weakly decreases when q is replaced by q+2.
-/

private lemma wtc_step_choose_pos (n k : ℕ) (h : k ≤ n) : (0:ℝ) < ((n.choose k : ℕ) : ℝ) := by
  have := Nat.choose_pos h
  exact_mod_cast this

private lemma wtc_step_choose_two (n k : ℕ) :
    (n+2).choose k * (n+1-k) * (n+2-k) = n.choose k * (n+1) * (n+2) := by
  have h1 : (n+2).choose k * (n+2-k) = (n+1).choose k * (n+2) := (Nat.choose_mul_succ_eq (n+1) k).symm
  have h0 : (n+1).choose k * (n+1-k) = n.choose k * (n+1) := (Nat.choose_mul_succ_eq n k).symm
  calc (n+2).choose k * (n+1-k) * (n+2-k)
      = (n+2).choose k * (n+2-k) * (n+1-k) := by ring
    _ = (n+1).choose k * (n+2) * (n+1-k) := by rw [h1]
    _ = (n+1).choose k * (n+1-k) * (n+2) := by ring
    _ = n.choose k * (n+1) * (n+2) := by rw [h0]

private lemma wtc_step_choose_three (n k : ℕ) :
    (n+3).choose k * (n+1-k) * (n+2-k) * (n+3-k) = n.choose k * (n+1) * (n+2) * (n+3) := by
  have h2 : (n+1).choose k * (n+1-k) = n.choose k * (n+1) := (Nat.choose_mul_succ_eq n k).symm
  have h := wtc_step_choose_two (n+1) k
  calc (n+3).choose k * (n+1-k) * (n+2-k) * (n+3-k)
      = ((n+3).choose k * (n+2-k) * (n+3-k)) * (n+1-k) := by ring
    _ = ((n+1).choose k * (n+2) * (n+3)) * (n+1-k) := by rw [h]
    _ = ((n+1).choose k * (n+1-k)) * (n+2) * (n+3) := by ring
    _ = (n.choose k * (n+1)) * (n+2) * (n+3) := by rw [h2]
    _ = n.choose k * (n+1) * (n+2) * (n+3) := by ring

private lemma wtc_step_choose_six (n k : ℕ) :
    (n+6).choose k * (n+1-k) * (n+2-k) * (n+3-k) * (n+4-k) * (n+5-k) * (n+6-k)
      = n.choose k * (n+1) * (n+2) * (n+3) * (n+4) * (n+5) * (n+6) := by
  have h := wtc_step_choose_three (n+3) k
  have h2 := wtc_step_choose_three n k
  calc (n+6).choose k * (n+1-k) * (n+2-k) * (n+3-k) * (n+4-k) * (n+5-k) * (n+6-k)
      = ((n+6).choose k * (n+4-k) * (n+5-k) * (n+6-k)) * ((n+1-k)*(n+2-k)*(n+3-k)) := by ring
    _ = ((n+3).choose k * (n+4) * (n+5) * (n+6)) * ((n+1-k)*(n+2-k)*(n+3-k)) := by rw [h]
    _ = ((n+3).choose k * (n+1-k) * (n+2-k) * (n+3-k)) * (n+4) * (n+5) * (n+6) := by ring
    _ = (n.choose k * (n+1) * (n+2) * (n+3)) * (n+4) * (n+5) * (n+6) := by rw [h2]
    _ = n.choose k * (n+1) * (n+2) * (n+3) * (n+4) * (n+5) * (n+6) := by ring

private lemma wtc_step_cross_two (n k : ℕ) (hk : k ≤ n) :
    ((n+2).choose k : ℝ) * (((n:ℝ)+1-(k:ℝ)) * ((n:ℝ)+2-(k:ℝ)))
      = ((n).choose k : ℝ) * (((n:ℝ)+1) * ((n:ℝ)+2)) := by
  have h := congrArg (fun x : ℕ => (x:ℝ)) (wtc_step_choose_two n k)
  have e1 : (((n+1-k:ℕ)):ℝ) = (n:ℝ)+1-(k:ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n+1)]; push_cast; ring
  have e2 : (((n+2-k:ℕ)):ℝ) = (n:ℝ)+2-(k:ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n+2)]; push_cast; ring
  push_cast at h
  rw [e1, e2] at h
  linarith [h]

private lemma wtc_step_cross_three (n k : ℕ) (hk : k ≤ n) :
    ((n+3).choose k : ℝ) * (((n:ℝ)+1-(k:ℝ)) * ((n:ℝ)+2-(k:ℝ)) * ((n:ℝ)+3-(k:ℝ)))
      = ((n).choose k : ℝ) * (((n:ℝ)+1) * ((n:ℝ)+2) * ((n:ℝ)+3)) := by
  have h := congrArg (fun x : ℕ => (x:ℝ)) (wtc_step_choose_three n k)
  have e1 : (((n+1-k:ℕ)):ℝ) = (n:ℝ)+1-(k:ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n+1)]; push_cast; ring
  have e2 : (((n+2-k:ℕ)):ℝ) = (n:ℝ)+2-(k:ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n+2)]; push_cast; ring
  have e3 : (((n+3-k:ℕ)):ℝ) = (n:ℝ)+3-(k:ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n+3)]; push_cast; ring
  push_cast at h
  rw [e1, e2, e3] at h
  linarith [h]

private lemma wtc_step_cross_six (n k : ℕ) (hk : k ≤ n) :
    ((n+6).choose k : ℝ) * (((n:ℝ)+1-(k:ℝ)) * ((n:ℝ)+2-(k:ℝ)) * ((n:ℝ)+3-(k:ℝ))
      * ((n:ℝ)+4-(k:ℝ)) * ((n:ℝ)+5-(k:ℝ)) * ((n:ℝ)+6-(k:ℝ)))
      = ((n).choose k : ℝ) * (((n:ℝ)+1) * ((n:ℝ)+2) * ((n:ℝ)+3) * ((n:ℝ)+4) * ((n:ℝ)+5) * ((n:ℝ)+6)) := by
  have h := congrArg (fun x : ℕ => (x:ℝ)) (wtc_step_choose_six n k)
  have e1 : (((n+1-k:ℕ)):ℝ) = (n:ℝ)+1-(k:ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n+1)]; push_cast; ring
  have e2 : (((n+2-k:ℕ)):ℝ) = (n:ℝ)+2-(k:ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n+2)]; push_cast; ring
  have e3 : (((n+3-k:ℕ)):ℝ) = (n:ℝ)+3-(k:ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n+3)]; push_cast; ring
  have e4 : (((n+4-k:ℕ)):ℝ) = (n:ℝ)+4-(k:ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n+4)]; push_cast; ring
  have e5 : (((n+5-k:ℕ)):ℝ) = (n:ℝ)+5-(k:ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n+5)]; push_cast; ring
  have e6 : (((n+6-k:ℕ)):ℝ) = (n:ℝ)+6-(k:ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n+6)]; push_cast; ring
  push_cast at h
  rw [e1, e2, e3, e4, e5, e6] at h
  linarith [h]

private lemma wtc_step_pack (x A A2 B B2 D D2 P1 Q1 P2 Q2 P3 Q3 : ℝ)
    (hx : 0 ≤ x) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) (hD2 : 0 < D2)
    (hP1 : 0 < P1) (hQ3 : 0 < Q3) (hP2 : 0 < P2)
    (hAA : A2 * P1 = A * Q1) (hBB : B2 * P2 = B * Q2) (hDD : D2 * P3 = D * Q3)
    (hQle : Q1 * Q2 * P3 ≤ P1 * P2 * Q3) :
    x * (A2 * B2 / D2) ≤ x * (A * B / D) := by
  have hprod : A2 * B2 * D * (P1*P2*Q3) = A * B * D2 * (Q1*Q2*P3) := by
    calc A2 * B2 * D * (P1*P2*Q3) = (A2*P1)*(B2*P2)*(D*Q3) := by ring
      _ = (A*Q1)*(B*Q2)*(D2*P3) := by rw [hAA, hBB, hDD]
      _ = A * B * D2 * (Q1*Q2*P3) := by ring
  have hpos : 0 < P1*P2*Q3 := by positivity
  have hle : A2 * B2 * D * (P1*P2*Q3) ≤ A * B * D2 * (P1*P2*Q3) := by
    rw [hprod]
    exact mul_le_mul_of_nonneg_left hQle (by positivity)
  have hm : A2 * B2 * D ≤ A * B * D2 := le_of_mul_le_mul_right hle hpos
  have hdiv : A2*B2/D2 ≤ A*B/D := by
    rw [div_le_div_iff₀ hD2 hD]
    linarith [hm]
  exact mul_le_mul_of_nonneg_left hdiv hx

private lemma wtc_step_poly_even (t s : ℝ) (ht : 1 ≤ t) (hs : 0 ≤ s) (hcon : 4*s ≤ 2*t+1) :
    (2*t+2)*(2*t+3) * ((3*t+2)*(3*t+3)*(3*t+4)) *
      ((6*t+4-6*s)*(6*t+5-6*s)*(6*t+6-6*s)*(6*t+7-6*s)*(6*t+8-6*s)*(6*t+9-6*s))
    ≤ (2*t+2-2*s)*(2*t+3-2*s) * ((3*t+2-3*s)*(3*t+3-3*s)*(3*t+4-3*s)) *
      ((6*t+4)*(6*t+5)*(6*t+6)*(6*t+7)*(6*t+8)*(6*t+9)) := by
  have hDEN : 0 < (6*t+6-6*s)*(6*t+5)*(6*t+7) := by
    have h1 : (0:ℝ) < 6*t+6-6*s := by nlinarith
    have h2 : (0:ℝ) < 6*t+5 := by linarith
    have h3 : (0:ℝ) < 6*t+7 := by linarith
    exact mul_pos (mul_pos h1 h2) h3
  have hNUM : (6*t+6)*(6*t+5-6*s)*(6*t+7-6*s) ≤ (6*t+6-6*s)*(6*t+5)*(6*t+7) := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 6*t+6) (by linarith : (0:ℝ) ≤ 6*t+6-6*s)) (by norm_num : (0:ℝ) ≤ 1)]
  have hid : ((2*t+2)*(2*t+3) * ((3*t+2)*(3*t+3)*(3*t+4)) *
      ((6*t+4-6*s)*(6*t+5-6*s)*(6*t+6-6*s)*(6*t+7-6*s)*(6*t+8-6*s)*(6*t+9-6*s)))
      * ((6*t+6-6*s)*(6*t+5)*(6*t+7))
    = ((2*t+2-2*s)*(2*t+3-2*s) * ((3*t+2-3*s)*(3*t+3-3*s)*(3*t+4-3*s)) *
      ((6*t+4)*(6*t+5)*(6*t+6)*(6*t+7)*(6*t+8)*(6*t+9)))
      * ((6*t+6)*(6*t+5-6*s)*(6*t+7-6*s)) := by ring
  have hR : 0 ≤ (2*t+2-2*s)*(2*t+3-2*s) * ((3*t+2-3*s)*(3*t+3-3*s)*(3*t+4-3*s)) *
      ((6*t+4)*(6*t+5)*(6*t+6)*(6*t+7)*(6*t+8)*(6*t+9)) := by
    have h1 : (0:ℝ) < 2*t+2-2*s := by nlinarith
    have h2 : (0:ℝ) < 2*t+3-2*s := by nlinarith
    have h3 : (0:ℝ) < 3*t+2-3*s := by nlinarith
    have h4 : (0:ℝ) < 3*t+3-3*s := by nlinarith
    have h5 : (0:ℝ) < 3*t+4-3*s := by nlinarith
    have g1 : (0:ℝ) < 6*t+4 := by linarith
    have g2 : (0:ℝ) < 6*t+5 := by linarith
    have g3 : (0:ℝ) < 6*t+6 := by linarith
    have g4 : (0:ℝ) < 6*t+7 := by linarith
    have g5 : (0:ℝ) < 6*t+8 := by linarith
    have g6 : (0:ℝ) < 6*t+9 := by linarith
    positivity
  have hstep : ((2*t+2)*(2*t+3) * ((3*t+2)*(3*t+3)*(3*t+4)) *
      ((6*t+4-6*s)*(6*t+5-6*s)*(6*t+6-6*s)*(6*t+7-6*s)*(6*t+8-6*s)*(6*t+9-6*s)))
      * ((6*t+6-6*s)*(6*t+5)*(6*t+7))
      ≤ ((2*t+2-2*s)*(2*t+3-2*s) * ((3*t+2-3*s)*(3*t+3-3*s)*(3*t+4-3*s)) *
      ((6*t+4)*(6*t+5)*(6*t+6)*(6*t+7)*(6*t+8)*(6*t+9)))
      * ((6*t+6-6*s)*(6*t+5)*(6*t+7)) := by
    rw [hid]
    exact mul_le_mul_of_nonneg_left hNUM hR
  exact le_of_mul_le_mul_right hstep hDEN

private lemma wtc_step_poly_odd (t s : ℝ) (ht : 1 ≤ t) (hs : 0 ≤ s) (hcon : 4*s+2 ≤ 2*t+1) :
    (2*t+2)*(2*t+3) * ((3*t+2)*(3*t+3)*(3*t+4)) *
      ((6*t+1-6*s)*(6*t+2-6*s)*(6*t+3-6*s)*(6*t+4-6*s)*(6*t+5-6*s)*(6*t+6-6*s))
    ≤ (2*t+1-2*s)*(2*t+2-2*s) * ((3*t+1-3*s)*(3*t+2-3*s)*(3*t+3-3*s)) *
      ((6*t+4)*(6*t+5)*(6*t+6)*(6*t+7)*(6*t+8)*(6*t+9)) := by
  have hDEN : 0 < (6*t+5)*(6*t+7)*(6*t+6-6*s) := by
    have h1 : (0:ℝ) < 6*t+6-6*s := by nlinarith
    have h2 : (0:ℝ) < 6*t+5 := by linarith
    have h3 : (0:ℝ) < 6*t+7 := by linarith
    exact mul_pos (mul_pos h2 h3) h1
  have hNUM : (6*t+6)*(6*t+1-6*s)*(6*t+5-6*s) ≤ (6*t+5)*(6*t+7)*(6*t+6-6*s) := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 6*t+6) (by linarith : (0:ℝ) ≤ 6*t+1-6*s)) (by linarith : (0:ℝ) ≤ 6*t+5-6*s),
               mul_nonneg (by linarith : (0:ℝ) ≤ 2*s+1) (mul_nonneg (by linarith : (0:ℝ) ≤ 6*t+6) (by linarith : (0:ℝ) ≤ 6*t+3-6*s))]
  have hid : ((2*t+2)*(2*t+3) * ((3*t+2)*(3*t+3)*(3*t+4)) *
      ((6*t+1-6*s)*(6*t+2-6*s)*(6*t+3-6*s)*(6*t+4-6*s)*(6*t+5-6*s)*(6*t+6-6*s)))
      * ((6*t+5)*(6*t+7)*(6*t+6-6*s))
    = ((2*t+1-2*s)*(2*t+2-2*s) * ((3*t+1-3*s)*(3*t+2-3*s)*(3*t+3-3*s)) *
      ((6*t+4)*(6*t+5)*(6*t+6)*(6*t+7)*(6*t+8)*(6*t+9)))
      * ((6*t+6)*(6*t+1-6*s)*(6*t+5-6*s)) := by ring
  have hR : 0 ≤ (2*t+1-2*s)*(2*t+2-2*s) * ((3*t+1-3*s)*(3*t+2-3*s)*(3*t+3-3*s)) *
      ((6*t+4)*(6*t+5)*(6*t+6)*(6*t+7)*(6*t+8)*(6*t+9)) := by
    have h1 : (0:ℝ) < 2*t+1-2*s := by nlinarith
    have h2 : (0:ℝ) < 2*t+2-2*s := by nlinarith
    have h3 : (0:ℝ) < 3*t+1-3*s := by nlinarith
    have h4 : (0:ℝ) < 3*t+2-3*s := by nlinarith
    have h5 : (0:ℝ) < 3*t+3-3*s := by nlinarith
    have g1 : (0:ℝ) < 6*t+4 := by linarith
    have g2 : (0:ℝ) < 6*t+5 := by linarith
    have g3 : (0:ℝ) < 6*t+6 := by linarith
    have g4 : (0:ℝ) < 6*t+7 := by linarith
    have g5 : (0:ℝ) < 6*t+8 := by linarith
    have g6 : (0:ℝ) < 6*t+9 := by linarith
    positivity
  have hstep : ((2*t+2)*(2*t+3) * ((3*t+2)*(3*t+3)*(3*t+4)) *
      ((6*t+1-6*s)*(6*t+2-6*s)*(6*t+3-6*s)*(6*t+4-6*s)*(6*t+5-6*s)*(6*t+6-6*s)))
      * ((6*t+5)*(6*t+7)*(6*t+6-6*s))
      ≤ ((2*t+1-2*s)*(2*t+2-2*s) * ((3*t+1-3*s)*(3*t+2-3*s)*(3*t+3-3*s)) *
      ((6*t+4)*(6*t+5)*(6*t+6)*(6*t+7)*(6*t+8)*(6*t+9)))
      * ((6*t+5)*(6*t+7)*(6*t+6-6*s)) := by
    rw [hid]
    exact mul_le_mul_of_nonneg_left hNUM hR
  exact le_of_mul_le_mul_right hstep hDEN

theorem wild_triple_partition_term_antitone_odd_step
    (q h : ℕ) (hq : 3 ≤ q) (hodd : q%2 = 1)
    (hh : 1 ≤ h) (hhq : 2*h ≤ q) :
    wtc_term (q+2) h ≤ wtc_term q h := by
  obtain ⟨t, ht⟩ : ∃ t, q = 2*t+1 := by
    have ho : Odd q := Nat.odd_iff.mpr hodd
    obtain ⟨t, ht⟩ := ho
    exact ⟨t, by omega⟩
  subst ht
  have ht1 : 1 ≤ t := by omega
  have htR : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht1
  rcases Nat.mod_two_eq_zero_or_one h with hh2 | hh2
  · obtain ⟨s, hs⟩ : ∃ s, h = 2*s := by
      have := Nat.even_iff.mpr hh2
      obtain ⟨s, hs⟩ := this
      exact ⟨s, by omega⟩
    subst hs
    have hsle : 4*s ≤ 2*t+1 := by omega
    have hsleR : 4*(s:ℝ) ≤ 2*(t:ℝ)+1 := by exact_mod_cast hsle
    simp only [wtc_term,
      show 3*(2*t+1+2) = 6*t+9 from by omega,
      show (6*t+9)/2 = 3*t+4 from by omega,
      show 3*(2*t+1) = 6*t+3 from by omega,
      show (6*t+3)/2 = 3*t+1 from by omega,
      show 3*(2*s) = 6*s from by omega, show (6*s)/2 = 3*s from by omega]
    have hAA : ((2*t+3).choose (2*s) : ℝ) * ((2*(t:ℝ)+2-2*(s:ℝ))*(2*(t:ℝ)+3-2*(s:ℝ)))
        = ((2*t+1).choose (2*s) : ℝ) * ((2*(t:ℝ)+2)*(2*(t:ℝ)+3)) := by
      have h := wtc_step_cross_two (2*t+1) (2*s) (by omega)
      rw [show 2*t+1+2 = 2*t+3 from by omega] at h
      have e : ((↑(2*t+1):ℝ)+1-↑(2*s)) * ((↑(2*t+1):ℝ)+2-↑(2*s))
          = (2*(t:ℝ)+2-2*(s:ℝ))*(2*(t:ℝ)+3-2*(s:ℝ)) := by push_cast; ring
      have e2 : ((↑(2*t+1):ℝ)+1) * ((↑(2*t+1):ℝ)+2) = (2*(t:ℝ)+2)*(2*(t:ℝ)+3) := by push_cast; ring
      rw [e, e2] at h
      exact h
    have hBB : ((3*t+4).choose (3*s) : ℝ) *
        ((3*(t:ℝ)+2-3*(s:ℝ))*(3*(t:ℝ)+3-3*(s:ℝ))*(3*(t:ℝ)+4-3*(s:ℝ)))
        = ((3*t+1).choose (3*s) : ℝ) * ((3*(t:ℝ)+2)*(3*(t:ℝ)+3)*(3*(t:ℝ)+4)) := by
      have h := wtc_step_cross_three (3*t+1) (3*s) (by omega)
      rw [show 3*t+1+3 = 3*t+4 from by omega] at h
      have e : ((↑(3*t+1):ℝ)+1-↑(3*s)) * ((↑(3*t+1):ℝ)+2-↑(3*s)) * ((↑(3*t+1):ℝ)+3-↑(3*s))
          = (3*(t:ℝ)+2-3*(s:ℝ))*(3*(t:ℝ)+3-3*(s:ℝ))*(3*(t:ℝ)+4-3*(s:ℝ)) := by push_cast; ring
      have e2 : ((↑(3*t+1):ℝ)+1) * ((↑(3*t+1):ℝ)+2) * ((↑(3*t+1):ℝ)+3)
          = (3*(t:ℝ)+2)*(3*(t:ℝ)+3)*(3*(t:ℝ)+4) := by push_cast; ring
      rw [e, e2] at h
      exact h
    have hDD : ((6*t+9).choose (6*s) : ℝ) *
        ((6*(t:ℝ)+4-6*(s:ℝ))*(6*(t:ℝ)+5-6*(s:ℝ))*(6*(t:ℝ)+6-6*(s:ℝ))*(6*(t:ℝ)+7-6*(s:ℝ))*(6*(t:ℝ)+8-6*(s:ℝ))*(6*(t:ℝ)+9-6*(s:ℝ)))
        = ((6*t+3).choose (6*s) : ℝ) * ((6*(t:ℝ)+4)*(6*(t:ℝ)+5)*(6*(t:ℝ)+6)*(6*(t:ℝ)+7)*(6*(t:ℝ)+8)*(6*(t:ℝ)+9)) := by
      have h := wtc_step_cross_six (6*t+3) (6*s) (by omega)
      rw [show 6*t+3+6 = 6*t+9 from by omega] at h
      have e : ((↑(6*t+3):ℝ)+1-↑(6*s)) * ((↑(6*t+3):ℝ)+2-↑(6*s)) * ((↑(6*t+3):ℝ)+3-↑(6*s))
              * ((↑(6*t+3):ℝ)+4-↑(6*s)) * ((↑(6*t+3):ℝ)+5-↑(6*s)) * ((↑(6*t+3):ℝ)+6-↑(6*s))
          = (6*(t:ℝ)+4-6*(s:ℝ))*(6*(t:ℝ)+5-6*(s:ℝ))*(6*(t:ℝ)+6-6*(s:ℝ))*(6*(t:ℝ)+7-6*(s:ℝ))*(6*(t:ℝ)+8-6*(s:ℝ))*(6*(t:ℝ)+9-6*(s:ℝ)) := by push_cast; ring
      have e2 : ((↑(6*t+3):ℝ)+1) * ((↑(6*t+3):ℝ)+2) * ((↑(6*t+3):ℝ)+3) * ((↑(6*t+3):ℝ)+4) * ((↑(6*t+3):ℝ)+5) * ((↑(6*t+3):ℝ)+6)
          = (6*(t:ℝ)+4)*(6*(t:ℝ)+5)*(6*(t:ℝ)+6)*(6*(t:ℝ)+7)*(6*(t:ℝ)+8)*(6*(t:ℝ)+9) := by push_cast; ring
      rw [e, e2] at h
      exact h
    have hQle := wtc_step_poly_even (t:ℝ) (s:ℝ) htR (by positivity) hsleR
    have hP1 : (0:ℝ) < (2*(t:ℝ)+2-2*(s:ℝ))*(2*(t:ℝ)+3-2*(s:ℝ)) := by
      have a : (0:ℝ) < 2*(t:ℝ)+2-2*(s:ℝ) := by nlinarith
      have b : (0:ℝ) < 2*(t:ℝ)+3-2*(s:ℝ) := by nlinarith
      positivity
    have hP2 : (0:ℝ) < (3*(t:ℝ)+2-3*(s:ℝ))*(3*(t:ℝ)+3-3*(s:ℝ))*(3*(t:ℝ)+4-3*(s:ℝ)) := by
      have a : (0:ℝ) < 3*(t:ℝ)+2-3*(s:ℝ) := by nlinarith
      have b : (0:ℝ) < 3*(t:ℝ)+3-3*(s:ℝ) := by nlinarith
      have c : (0:ℝ) < 3*(t:ℝ)+4-3*(s:ℝ) := by nlinarith
      positivity
    have haux := wtc_step_pack (x := 3*↑(2*s))
      (A := ((2*t+1).choose (2*s) : ℝ)) (A2 := ((2*t+3).choose (2*s) : ℝ))
      (B := ((3*t+1).choose (3*s) : ℝ)) (B2 := ((3*t+4).choose (3*s) : ℝ))
      (D := ((6*t+3).choose (6*s) : ℝ)) (D2 := ((6*t+9).choose (6*s) : ℝ))
      (P1 := (2*(t:ℝ)+2-2*(s:ℝ))*(2*(t:ℝ)+3-2*(s:ℝ)))
      (Q1 := (2*(t:ℝ)+2)*(2*(t:ℝ)+3))
      (P2 := (3*(t:ℝ)+2-3*(s:ℝ))*(3*(t:ℝ)+3-3*(s:ℝ))*(3*(t:ℝ)+4-3*(s:ℝ)))
      (Q2 := (3*(t:ℝ)+2)*(3*(t:ℝ)+3)*(3*(t:ℝ)+4))
      (P3 := (6*(t:ℝ)+4-6*(s:ℝ))*(6*(t:ℝ)+5-6*(s:ℝ))*(6*(t:ℝ)+6-6*(s:ℝ))*(6*(t:ℝ)+7-6*(s:ℝ))*(6*(t:ℝ)+8-6*(s:ℝ))*(6*(t:ℝ)+9-6*(s:ℝ)))
      (Q3 := (6*(t:ℝ)+4)*(6*(t:ℝ)+5)*(6*(t:ℝ)+6)*(6*(t:ℝ)+7)*(6*(t:ℝ)+8)*(6*(t:ℝ)+9))
      (by positivity)
      (wtc_step_choose_pos (2*t+1) (2*s) (by omega))
      (wtc_step_choose_pos (3*t+1) (3*s) (by omega))
      (wtc_step_choose_pos (6*t+3) (6*s) (by omega))
      (wtc_step_choose_pos (6*t+9) (6*s) (by omega))
      hP1 (by positivity) hP2
      hAA hBB hDD hQle
    have h1 : 3*↑(2*s) * ↑((2*t+3).choose (2*s)) * ↑((3*t+4).choose (3*s)) / ↑((6*t+9).choose (6*s))
        = (3*↑(2*s)) * ((((2*t+3).choose (2*s) : ℝ)) * (((3*t+4).choose (3*s) : ℝ)) / (((6*t+9).choose (6*s) : ℝ))) := by ring
    have h2 : 3*↑(2*s) * ↑((2*t+1).choose (2*s)) * ↑((3*t+1).choose (3*s)) / ↑((6*t+3).choose (6*s))
        = (3*↑(2*s)) * ((((2*t+1).choose (2*s) : ℝ)) * (((3*t+1).choose (3*s) : ℝ)) / (((6*t+3).choose (6*s) : ℝ))) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right haux (by positivity)
  · obtain ⟨s, hs⟩ : ∃ s, h = 2*s+1 := by
      have := Nat.odd_iff.mpr hh2
      obtain ⟨s, hs⟩ := this
      exact ⟨s, by omega⟩
    subst hs
    have hsle : 2*(2*s+1) ≤ 2*t+1 := by omega
    have hsleR : 4*(s:ℝ)+2 ≤ 2*(t:ℝ)+1 := by
      have hh : (2*(2*s+1) : ℝ) ≤ (2*t+1 : ℝ) := by exact_mod_cast hsle
      push_cast at hh; linarith
    simp only [wtc_term,
      show 3*(2*t+1+2) = 6*t+9 from by omega,
      show (6*t+9)/2 = 3*t+4 from by omega,
      show 3*(2*t+1) = 6*t+3 from by omega,
      show (6*t+3)/2 = 3*t+1 from by omega,
      show 3*(2*s+1) = 6*s+3 from by omega, show (6*s+3)/2 = 3*s+1 from by omega]
    have hAA : ((2*t+3).choose (2*s+1) : ℝ) * ((2*(t:ℝ)+1-2*(s:ℝ))*(2*(t:ℝ)+2-2*(s:ℝ)))
        = ((2*t+1).choose (2*s+1) : ℝ) * ((2*(t:ℝ)+2)*(2*(t:ℝ)+3)) := by
      have h := wtc_step_cross_two (2*t+1) (2*s+1) (by omega)
      rw [show 2*t+1+2 = 2*t+3 from by omega] at h
      have e : ((↑(2*t+1):ℝ)+1-↑(2*s+1)) * ((↑(2*t+1):ℝ)+2-↑(2*s+1))
          = (2*(t:ℝ)+1-2*(s:ℝ))*(2*(t:ℝ)+2-2*(s:ℝ)) := by push_cast; ring
      have e2 : ((↑(2*t+1):ℝ)+1) * ((↑(2*t+1):ℝ)+2) = (2*(t:ℝ)+2)*(2*(t:ℝ)+3) := by push_cast; ring
      rw [e, e2] at h
      exact h
    have hBB : ((3*t+4).choose (3*s+1) : ℝ) *
        ((3*(t:ℝ)+1-3*(s:ℝ))*(3*(t:ℝ)+2-3*(s:ℝ))*(3*(t:ℝ)+3-3*(s:ℝ)))
        = ((3*t+1).choose (3*s+1) : ℝ) * ((3*(t:ℝ)+2)*(3*(t:ℝ)+3)*(3*(t:ℝ)+4)) := by
      have h := wtc_step_cross_three (3*t+1) (3*s+1) (by omega)
      rw [show 3*t+1+3 = 3*t+4 from by omega] at h
      have e : ((↑(3*t+1):ℝ)+1-↑(3*s+1)) * ((↑(3*t+1):ℝ)+2-↑(3*s+1)) * ((↑(3*t+1):ℝ)+3-↑(3*s+1))
          = (3*(t:ℝ)+1-3*(s:ℝ))*(3*(t:ℝ)+2-3*(s:ℝ))*(3*(t:ℝ)+3-3*(s:ℝ)) := by push_cast; ring
      have e2 : ((↑(3*t+1):ℝ)+1) * ((↑(3*t+1):ℝ)+2) * ((↑(3*t+1):ℝ)+3)
          = (3*(t:ℝ)+2)*(3*(t:ℝ)+3)*(3*(t:ℝ)+4) := by push_cast; ring
      rw [e, e2] at h
      exact h
    have hDD : ((6*t+9).choose (6*s+3) : ℝ) *
        ((6*(t:ℝ)+1-6*(s:ℝ))*(6*(t:ℝ)+2-6*(s:ℝ))*(6*(t:ℝ)+3-6*(s:ℝ))*(6*(t:ℝ)+4-6*(s:ℝ))*(6*(t:ℝ)+5-6*(s:ℝ))*(6*(t:ℝ)+6-6*(s:ℝ)))
        = ((6*t+3).choose (6*s+3) : ℝ) * ((6*(t:ℝ)+4)*(6*(t:ℝ)+5)*(6*(t:ℝ)+6)*(6*(t:ℝ)+7)*(6*(t:ℝ)+8)*(6*(t:ℝ)+9)) := by
      have h := wtc_step_cross_six (6*t+3) (6*s+3) (by omega)
      rw [show 6*t+3+6 = 6*t+9 from by omega] at h
      have e : ((↑(6*t+3):ℝ)+1-↑(6*s+3)) * ((↑(6*t+3):ℝ)+2-↑(6*s+3)) * ((↑(6*t+3):ℝ)+3-↑(6*s+3))
              * ((↑(6*t+3):ℝ)+4-↑(6*s+3)) * ((↑(6*t+3):ℝ)+5-↑(6*s+3)) * ((↑(6*t+3):ℝ)+6-↑(6*s+3))
          = (6*(t:ℝ)+1-6*(s:ℝ))*(6*(t:ℝ)+2-6*(s:ℝ))*(6*(t:ℝ)+3-6*(s:ℝ))*(6*(t:ℝ)+4-6*(s:ℝ))*(6*(t:ℝ)+5-6*(s:ℝ))*(6*(t:ℝ)+6-6*(s:ℝ)) := by push_cast; ring
      have e2 : ((↑(6*t+3):ℝ)+1) * ((↑(6*t+3):ℝ)+2) * ((↑(6*t+3):ℝ)+3) * ((↑(6*t+3):ℝ)+4) * ((↑(6*t+3):ℝ)+5) * ((↑(6*t+3):ℝ)+6)
          = (6*(t:ℝ)+4)*(6*(t:ℝ)+5)*(6*(t:ℝ)+6)*(6*(t:ℝ)+7)*(6*(t:ℝ)+8)*(6*(t:ℝ)+9) := by push_cast; ring
      rw [e, e2] at h
      exact h
    have hQle := wtc_step_poly_odd (t:ℝ) (s:ℝ) htR (by positivity) hsleR
    have hP1 : (0:ℝ) < (2*(t:ℝ)+1-2*(s:ℝ))*(2*(t:ℝ)+2-2*(s:ℝ)) := by nlinarith
    have hP2 : (0:ℝ) < (3*(t:ℝ)+1-3*(s:ℝ))*(3*(t:ℝ)+2-3*(s:ℝ))*(3*(t:ℝ)+3-3*(s:ℝ)) := by
      have a : (0:ℝ) < 3*(t:ℝ)+1-3*(s:ℝ) := by nlinarith
      have b : (0:ℝ) < 3*(t:ℝ)+2-3*(s:ℝ) := by nlinarith
      have c : (0:ℝ) < 3*(t:ℝ)+3-3*(s:ℝ) := by nlinarith
      positivity
    have haux := wtc_step_pack (x := 3*↑(2*s+1))
      (A := ((2*t+1).choose (2*s+1) : ℝ)) (A2 := ((2*t+3).choose (2*s+1) : ℝ))
      (B := ((3*t+1).choose (3*s+1) : ℝ)) (B2 := ((3*t+4).choose (3*s+1) : ℝ))
      (D := ((6*t+3).choose (6*s+3) : ℝ)) (D2 := ((6*t+9).choose (6*s+3) : ℝ))
      (P1 := (2*(t:ℝ)+1-2*(s:ℝ))*(2*(t:ℝ)+2-2*(s:ℝ)))
      (Q1 := (2*(t:ℝ)+2)*(2*(t:ℝ)+3))
      (P2 := (3*(t:ℝ)+1-3*(s:ℝ))*(3*(t:ℝ)+2-3*(s:ℝ))*(3*(t:ℝ)+3-3*(s:ℝ)))
      (Q2 := (3*(t:ℝ)+2)*(3*(t:ℝ)+3)*(3*(t:ℝ)+4))
      (P3 := (6*(t:ℝ)+1-6*(s:ℝ))*(6*(t:ℝ)+2-6*(s:ℝ))*(6*(t:ℝ)+3-6*(s:ℝ))*(6*(t:ℝ)+4-6*(s:ℝ))*(6*(t:ℝ)+5-6*(s:ℝ))*(6*(t:ℝ)+6-6*(s:ℝ)))
      (Q3 := (6*(t:ℝ)+4)*(6*(t:ℝ)+5)*(6*(t:ℝ)+6)*(6*(t:ℝ)+7)*(6*(t:ℝ)+8)*(6*(t:ℝ)+9))
      (by positivity)
      (wtc_step_choose_pos (2*t+1) (2*s+1) (by omega))
      (wtc_step_choose_pos (3*t+1) (3*s+1) (by omega))
      (wtc_step_choose_pos (6*t+3) (6*s+3) (by omega))
      (wtc_step_choose_pos (6*t+9) (6*s+3) (by omega))
      hP1 (by positivity) hP2
      hAA hBB hDD hQle
    have h1 : 3*↑(2*s+1) * ↑((2*t+3).choose (2*s+1)) * ↑((3*t+4).choose (3*s+1)) / ↑((6*t+9).choose (6*s+3))
        = (3*↑(2*s+1)) * ((((2*t+3).choose (2*s+1) : ℝ)) * (((3*t+4).choose (3*s+1) : ℝ)) / (((6*t+9).choose (6*s+3) : ℝ))) := by ring
    have h2 : 3*↑(2*s+1) * ↑((2*t+1).choose (2*s+1)) * ↑((3*t+1).choose (3*s+1)) / ↑((6*t+3).choose (6*s+3))
        = (3*↑(2*s+1)) * ((((2*t+1).choose (2*s+1) : ℝ)) * (((3*t+1).choose (3*s+1) : ℝ)) / (((6*t+3).choose (6*s+3) : ℝ))) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right haux (by positivity)
