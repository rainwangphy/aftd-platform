import AFTD.Prelude

/-!
# boundary_five_blocks_short_c_shore_arithmetic

Topic: graphs   Node: 91b4410eceaa

Provenance: helper lemma. OP-1957: unbounded arithmetic core of the two-five-block boundary classification.

The displayed degree, parity, size and separator counts imply at least two A vertices in the first shore when the opposite shore contains at most one C vertex.
-/

theorem boundary_five_blocks_short_c_shore_arithmetic
    (m r qa qb qc qd wa wb wc wd Q W : ℕ)
    (hm : 5 ≤ m) (hr : r ≤ 2) (hrc : wc ≤ r)
    (hqcapa : qa+wa ≤ 4) (hqcapb : qb+wb ≤ m)
    (hqcapc : qc+wc ≤ 4) (hqcapd : qd+wd ≤ m)
    (hQ : Q=qa+qb+qc+qd) (hW : W=wa+wb+wc+wd)
    (hQe : Even Q) (hWe : Even W) (htotal : Q+W=m+3)
    (hx : wa+wd+r ≤ 2) (hy : qa+qb+qc ≤ 2)
    (hqa : 0<qa → wa+wc+wd+1 ≤ 2)
    (hqb : 0<qb → wb+wc+wd+1+3 ≤ m)
    (hqc : 0<qc → wa+wb+wc+1 ≤ 2)
    (hqd : 0<qd → wa+wb+wd+3 ≤ m)
    (hwa : 0<wa → qa+qc+qd+1 ≤ 2)
    (hwb : 0<wb → qb+qc+qd+3 ≤ m)
    (hwc : 0<wc → qa+qb+qc+1 ≤ 2)
    (hwd : 0<wd → qa+qb+qd+1+3 ≤ m)
    (hsep : 0<qd → qd+wb+wd ≤ m) (hwc1 : wc ≤ 1) : 2 ≤ qa := by
  obtain ⟨i, hi⟩ := hQe
  obtain ⟨j, hj⟩ := hWe
  by_contra hn
  have ha : qa ≤ 1 := by omega
  have hdp : 0 < qd := by
    by_contra hnD
    have hD : qd = 0 := by omega
    have hQ2 : Q = 2 := by omega
    have hB : m-1 ≤ wb := by omega
    by_cases hb : 0 < qb
    · have hh := hqb hb
      omega
    · by_cases hc : 0 < qc
      · have hh := hqc hc
        omega
      · omega
  have hbp : 0 < wb := by
    by_contra hnB
    have hB : wb = 0 := by omega
    have hD : m-1 ≤ qd := by omega
    by_cases h1 : 0 < wa
    · have hh := hwa h1
      omega
    · by_cases h2 : 0 < wd
      · have hh := hwd h2
        omega
      · omega
  have hdW := hqd hdp
  have hbQ := hwb hbp
  have hQ6 : 6 ≤ Q := by omega
  have hW6 : 6 ≤ W := by omega
  have hD4 : 4 ≤ qd := by omega
  have hB4 : 4 ≤ wb := by omega
  have hwa0 : wa=0 := by
    by_contra hnwa
    have hh := hwa (by omega)
    omega
  have hqc0 : qc=0 := by
    by_contra hnqc
    have hh := hqc (by omega)
    omega
  have hs := hsep hdp
  by_cases hc0 : wc = 0
  · omega
  · have hh := hwc (by omega)
    omega
