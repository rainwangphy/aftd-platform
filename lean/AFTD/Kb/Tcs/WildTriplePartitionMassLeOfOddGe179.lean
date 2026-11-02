import AFTD.Prelude
import AFTD.Kb.Tcs.WildTriplePartitionLargeOrderMassBound
import AFTD.Kb.Tcs.WildTriplePartitionTermGeometricTail
import AFTD.Kb.Tcs.WildTriplePartitionTermAntitoneOddStep
import AFTD.Kb.Tcs.WildTriplePartitionMass179Baseline
import AFTD.Kb.Tcs.G

/-!
# wild_triple_partition_mass_le_of_odd_ge_179

Topic: graphs   Node: 87e09ccc8205

Provenance: helper lemma. IN-359 candidate continuation of the existing OP-306 permutation resource criterion. Exact audits8965/8967 locate a finite baseline; uniform monotonicity and tail summation must still be proved. It is not an accepted improved wild-number theorem or a research advance while stated.

For every odd number q of triple blocks with q>=179, the existing sufficient canonical seal-event resource sum wtc_mass(q) is at most1/50. This is an unproved arithmetic helper candidate; it asserts no main-conjecture conclusion.
-/

open Finset
open scoped BigOperators

private lemma wild_triple_partition_mass_le_of_odd_ge_179_sum_Ico_telescope_sub (f : ℕ → ℝ) (a b : ℕ) (h : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (f k - f (k + 1)) = f a - f b := by
  induction' h with b' hb' ih
  · simp
  · rw [Finset.sum_Ico_succ_top hb', ih]
    ring

private lemma wild_triple_partition_mass_le_of_odd_ge_179_sum_Ico_geom_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (a b : ℕ) (hab : a ≤ b) :
    let g : ℕ → ℝ := fun n => ((n : ℝ) / (1 - r) + r / (1 - r)^2) * r^n
    ∑ k ∈ Finset.Ico a b, (k : ℝ) * r^k ≤ g a := by
  intro g
  have hdiff : ∀ k : ℕ, (k : ℝ) * r^k = g k - g (k + 1) := by
    intro k
    dsimp [g]
    rw [pow_succ r k]
    have h1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; rfl
    rw [h1]
    have hr : 1 - r ≠ 0 := by linarith
    have h3 : ((k : ℝ) / (1 - r) + r / (1 - r)^2) - (((k : ℝ) + 1) / (1 - r) + r / (1 - r)^2) * r = (k : ℝ) := by
      field_simp
      ring
    calc
      (k : ℝ) * r^k = (((k : ℝ) / (1 - r) + r / (1 - r)^2) - (((k : ℝ) + 1) / (1 - r) + r / (1 - r)^2) * r) * r^k := by rw [h3]
      _ = ((k : ℝ) / (1 - r) + r / (1 - r)^2) * r^k - (((k : ℝ) + 1) / (1 - r) + r / (1 - r)^2) * (r^k * r) := by ring
  have hcongr : ∑ k ∈ Finset.Ico a b, (k : ℝ) * r^k = ∑ k ∈ Finset.Ico a b, (g k - g (k + 1)) := by
    apply Finset.sum_congr rfl; intro k _; exact hdiff k
  rw [hcongr, wild_triple_partition_mass_le_of_odd_ge_179_sum_Ico_telescope_sub g a b hab]
  have hgb : 0 ≤ g b := by
    dsimp [g]
    have hb1 : 0 ≤ (b:ℝ)/(1-r) := div_nonneg (Nat.cast_nonneg b) (by linarith)
    have hb2 : 0 ≤ r/(1-r)^2 := div_nonneg hr0 (pow_nonneg (by linarith) 2)
    exact mul_nonneg (add_nonneg hb1 hb2) (pow_nonneg hr0 b)
  linarith

private lemma wild_triple_partition_mass_le_of_odd_ge_179_term_iter (h : ℕ) (hh : 1 ≤ h) (hhq : 2*h ≤ 179) :
    ∀ k : ℕ, wtc_term (179 + 2*k) h ≤ wtc_term 179 h := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hmono : wtc_term (179 + 2*k + 2) h ≤ wtc_term (179 + 2*k) h :=
      wild_triple_partition_term_antitone_odd_step (179 + 2*k) h (by omega) (by omega) hh (by omega)
    have heq : 179 + 2*(k+1) = 179 + 2*k + 2 := by ring
    rw [heq]
    exact le_trans hmono ih

theorem wild_triple_partition_mass_le_of_odd_ge_179
    (q : ℕ) (hq : 179 ≤ q) (hodd : q%2 = 1) :
    wtc_mass q ≤ (1/50 : ℝ) := by
  have hmass : wtc_mass q = ∑ h ∈ Finset.Ico 1 (q/2+1), wtc_term q h := by
    unfold wtc_mass
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext h
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨hlt, h1, h2⟩; omega
      · rintro ⟨h1, h2⟩; omega
    · intro h _; rfl
  rw [hmass]
  have hdisj : Disjoint (Finset.Ico 1 40) (Finset.Ico 40 (q/2+1)) :=
    Finset.Ico_disjoint_Ico_consecutive 1 40 (q/2+1)
  have hsplit : Finset.Ico 1 (q/2+1) = Finset.Ico 1 40 ∪ Finset.Ico 40 (q/2+1) := by
    rw [Finset.Ico_union_Ico_eq_Ico]
    · norm_num
    · have : 179/2 ≤ q/2 := Nat.div_le_div_right hq; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hhead : ∑ h ∈ Finset.Ico 1 40, wtc_term q h ≤ (989/50000 : ℝ) := by
    have h1 : ∑ h ∈ Finset.Ico 1 40, wtc_term q h ≤ ∑ h ∈ Finset.Ico 1 40, wtc_term 179 h := by
      obtain ⟨k, hk⟩ : ∃ k : ℕ, q = 179 + 2*k := by
        use (q - 179) / 2
        omega
      rw [hk]
      apply Finset.sum_le_sum
      intro h hh
      simp only [Finset.mem_Ico] at hh
      obtain ⟨h1, h2⟩ := hh
      exact wild_triple_partition_mass_le_of_odd_ge_179_term_iter h (by omega) (by omega) k
    exact le_trans h1 wild_triple_partition_mass_179_baseline
  have htail : ∑ h ∈ Finset.Ico 40 (q/2+1), wtc_term q h ≤ (1/10000 : ℝ) := by
    have h2q : 2*(q/2) ≤ q := by
      have := Nat.div_mul_le_self q 2
      omega
    have h2 : ∑ h ∈ Finset.Ico 40 (q/2+1), wtc_term q h ≤
        ∑ h ∈ Finset.Ico 40 (q/2+1), 3*(h : ℝ)*(27/40 : ℝ)^h := by
      apply Finset.sum_le_sum
      intro h hh
      simp only [Finset.mem_Ico] at hh
      obtain ⟨h40, hlt⟩ := hh
      have hle : h ≤ q/2 := by omega
      exact wild_triple_partition_term_geometric_tail q h (by omega) hodd (by omega) (by omega)
    have h4 : ∑ h ∈ Finset.Ico 40 (q/2+1), (h : ℝ)*(27/40 : ℝ)^h ≤
        ((40:ℝ)/(1-(27/40)) + (27/40)/(1-(27/40))^2) * (27/40)^40 := by
      have hb : 40 ≤ q/2+1 := by
        have : 179/2 ≤ q/2 := Nat.div_le_div_right hq; omega
      exact wild_triple_partition_mass_le_of_odd_ge_179_sum_Ico_geom_le (27/40) (by norm_num) (by norm_num) 40 (q/2+1) hb
    calc
      ∑ h ∈ Finset.Ico 40 (q/2+1), wtc_term q h
          ≤ ∑ h ∈ Finset.Ico 40 (q/2+1), 3*(h : ℝ)*(27/40 : ℝ)^h := h2
      _ = 3 * ∑ h ∈ Finset.Ico 40 (q/2+1), (h : ℝ)*(27/40 : ℝ)^h := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro h _; ring
      _ ≤ 3 * (((40:ℝ)/(1-(27/40)) + (27/40)/(1-(27/40))^2) * (27/40)^40) := by
            apply mul_le_mul_of_nonneg_left h4; norm_num
      _ ≤ 1/10000 := by norm_num
  linarith
