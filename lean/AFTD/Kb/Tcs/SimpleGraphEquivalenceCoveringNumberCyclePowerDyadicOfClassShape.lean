import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverClassModel
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCoverMono
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicModelDvdOfNoIsland
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCoverCyclePowerDyadicUpper
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# simple_graph_equivalence_covering_number_cycle_power_dyadic_of_class_shape

Topic: combinatorics   Node: 8e016ec19a16

Provenance: helper lemma. Uniform formal assembly for OP-205 / RT-1 following arXiv:2610.15635 Proposition3.2. The explicit upper covers formalize a published construction. The final reduction keeps the still-unproved pure class-shape theorem as an EXPLICIT additional hypothesis. No unconditional graph covering result or research advance is claimed.

Under the numerical hypotheses of OP-205, the equivalence covering number is m+2 PROVIDED that every tight, exactly dyadically covered, fully ordinarily covered integer Boolean model at exponent m with exactly m+1 active classes at each vertex has no selected island. This structural implication is an explicit additional hypothesis; the theorem does not prove it or settle OP-205.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_equivalence_covering_number_cycle_power_dyadic_of_class_shape
    (k m n : ℕ) (hm : 1 ≤ m) (hkm : k+1 = 2^m)
    (hn : max (2*k+2) (k^2*(k+2)) ≤ n) (hev : Even n) (hnd : ¬(k+1) ∣ n)
    (hshape : ∀ (x : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight m (x p) =
        (Finset.range (2^m)).sum (fun a => (x p a).toNat)) →
      (∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^m-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^m)).sum (fun a =>
        (x (v-(a : ℤ)) a).toNat) = m+1) →
      ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^m →
        x p a = false → x p b = true → x p c = true) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n k) = m+2 := by
  have hm1 : m ≠ 1 := by
    intro he
    have hk1 : k=1 := by norm_num [he] at hkm; omega
    have h2 : 2 ∣ n := by
      rcases hev with ⟨a, ha⟩
      exact ⟨a, by omega⟩
    apply hnd
    simpa only [hk1, Nat.reduceAdd] using h2
  have hm2 : 2 ≤ m := by omega
  have hD4 : 4 ≤ 2^m := by
    calc
      4 = 2^2 := by decide
      _ ≤ 2^m := Nat.pow_le_pow_right (by decide) hm2
  have hk3 : 3 ≤ k := by omega
  have hnA : 2*k+2 ≤ n := (le_max_left _ _).trans hn
  have hnB : k^2*(k+2) ≤ n := (le_max_right _ _).trans hn
  have hnB2 : 2*k^2 ≤ n := by
    calc
      2*k^2 = k^2*2 := by ring
      _ ≤ k^2*(k+2) := Nat.mul_le_mul_left (k^2) (by omega)
      _ ≤ n := hnB
  have hnu : max (2*k+2) (2*k^2) ≤ n := max_le_iff.mpr ⟨hnA, hnB2⟩
  have hupper := simple_graph_has_equivalence_cover_cycle_power_dyadic_upper k m n (by omega) hkm hnu
  letI : NeZero n := ⟨by omega⟩
  refine le_antisymm (Nat.sInf_le hupper) (le_csInf ⟨m+2, hupper⟩ fun t ht => ?_)
  by_contra hbad
  have htle : t ≤ m+1 := by omega
  obtain ⟨c, hc, hcov⟩ := simple_graph_has_equivalence_cover_mono
    (simple_graph_cycle_power n k) htle ht
  have hkD : k=2^m-1 := by omega
  have hn3k : 3*k+1 ≤ n := by
    have hsq := Nat.mul_le_mul_right k hk3
    nlinarith [hnB2]
  have hn3 : 3*(2^m-1)+1 ≤ n := by simpa only [← hkD] using hn3k
  rw [hkD] at hc hcov
  obtain ⟨x, ell, hxp, hep, hends, htw, hct, hex, hcv, hfaith, hsep⟩ :=
    simple_graph_cycle_power_dyadic_cover_class_model m n (by omega) hn3 c hc hcov
  have hs := hshape x htw hex hcv hct
  have hdvd := cycle_power_dyadic_model_dvd_of_no_island m n hm2 (by omega) x ell
    hxp hep htw hct hex hcv hsep hs
  apply hnd
  simpa only [hkm] using hdvd
