import AFTD.Prelude
import AFTD.Kb.Tcs.BoundaryFiveBlocksShortCShoreArithmetic

/-!
# boundary_five_blocks_two_defect_shore_arithmetic

Topic: graphs   Node: 8956b6c798a6

Provenance: helper lemma. OP-1957: unbounded arithmetic core of the two-five-block boundary classification.

The displayed degree, parity, size and separator counts force the second shore to contain both C nonneighbors of x, no A vertices on the first shore and exactly one B vertex on the first shore when x has exactly two C nonneighbors.
-/

theorem boundary_five_blocks_two_defect_shore_arithmetic
    (m r qa qb qc qd wa wb wc wd Q W : ℕ)
    (hm : 5 ≤ m) (hr : r = 2) (hrc : wc ≤ r)
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
    (hsep : 0<qd → qd+wb+wd ≤ m) : wc=2 ∧ qa=0 ∧ qb=1 := by
  obtain ⟨i, hi⟩ := hQe
  have hzero : wa=0 ∧ wd=0 := by omega
  have ha1 : qa ≤ 1 := by
    by_contra hna
    have ha2 : qa = 2 := by omega
    have hbc0 : qb=0 ∧ qc=0 := by omega
    by_cases hd : 0 < qd
    · have hs := hsep hd
      have hw : 0 < wc := by omega
      have hh := hwc hw
      omega
    · have hw : 0 < wc := by omega
      have hh := hwc hw
      omega
  have hc2 : wc=2 := by
    by_contra hn
    have hc1 : wc ≤ 1 := by omega
    have ha2 := boundary_five_blocks_short_c_shore_arithmetic m r qa qb qc qd wa wb wc wd Q W hm
      (by omega) hrc hqcapa hqcapb hqcapc hqcapd hQ hW ⟨i,hi⟩ hWe htotal hx hy hqa hqb hqc hqd hwa hwb hwc hwd hsep hc1
    omega
  have ha0 : qa=0 := by
    by_contra hn
    have hh := hqa (by omega)
    omega
  have hc0 : qc=0 := by
    by_contra hn
    have hh := hqc (by omega)
    omega
  have hb1 : qb ≤ 1 := by
    have hh := hwc (by omega)
    omega
  have hd : 0<qd := by
    by_contra hn
    omega
  have hs := hsep hd
  omega
