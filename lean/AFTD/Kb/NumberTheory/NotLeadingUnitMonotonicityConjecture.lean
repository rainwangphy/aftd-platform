import AFTD.Prelude
import AFTD.Kb.NumberTheory.PlrsSeq
import AFTD.Kb.NumberTheory.IsCompleteSequence
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# not_leading_unit_monotonicity_conjecture

Topic: elementary_number_theory   Node: 8d95093b09b4

Provenance: original. Related work: refutes `leading_unit_monotonicity_conjecture`

The statement `leading_unit_monotonicity_conjecture` is false: The statement is FALSE. Counterexample: c = [1,0,3,0,3,1].

* c.length = 6 ≥ 2, c.getD 0 0 = 1, c.getD 5 0 = 1 ≥ 1 — all three hypotheses on c hold.
* plrs_seq c = 0,1,2,3,7,14,27,55,108,213,427,... This sequence IS complete (Brown's criterion holds: 1 + sum_{i=1..n} H(i) - H(n+1) ≥ 0 for all n ≥ 1). The proof: since c.length = 6, for m ≥ 1 the recurrence reads H(m+6) = H(m+5) + 3H(m+3) + 3H(m+1) + H(m). Hence the difference D(n) = 2H(n+1) - H(n+2) satisfies D(n+6) = D(n+5) + 3D(n+3) + 3D(n+1) + D(n) for n ≥ 1; with D(0..5) = 2,2,4,7,13,25 all ≥ 0, induction gives D(n) ≥ 0 for all n. Consequently the "gaps" G(n) = 1 + sum_{i=1..n} H(i) - H(n+1) have G(n+1) - G(n) = D(n) ≥ 0, and G(1..9) = 0,1,0,0,1,0,2,5,4 are all ≥ 0, so G(n) ≥ 0 for all n ≥ 1, i.e. Brown's criterion holds and the sequence is complete.
* But plrs_seq (1 :: c) = plrs_seq [1,1,0,3,0,3,1] = 0,1,2,4,7,15,29,60,117,... is NOT complete: at n = 6, sum_{i=1..6} = 58 while the next term is 60 > 58 + 1. By the necessity half of Brown's criterion (which holds for any positive nondecreasing sequence: if it is complete then every term is at most 1 + the sum of all preceding terms), this sequence cannot be complete.

So the conclusion fails. Note the counterexample needs length ≥ 6 — I verified exhaustively (Python, then re-derived in Lean) that there is no counterexample with c.length ≤ 5, which is why the "length two" and leading-1^g 0^k N special cases survive. Two supporting facts used in the refutation are of independent interest and are fully proved in it: Brown's criterion (sufficiency AND necessity, for positive nondecreasing integer sequences) and the monotonicity lemma plrs_seq c k ≤ plrs_seq c (k+1) whenever c.getD 0 0 = 1.
-/

theorem not_leading_unit_monotonicity_conjecture : ¬ (∀ (c : List ℕ) (hL : 2 ≤ c.length)
    (hc1 : c.getD 0 0 = 1) (hcL : 1 ≤ c.getD (c.length - 1) 0)
    (hcomp : is_complete_sequence (plrs_seq c)), is_complete_sequence (plrs_seq (1 :: c))) := by
  intro h
  have PlrsUnfold : ∀ (c : List ℕ) (n : ℕ), plrs_seq c (n+2) =
      (if n + 2 ≤ c.length then 1 + ∑ i ∈ Finset.range (n + 1), (c.getD i 0 : ℤ) * plrs_seq c (n + 1 - i)
       else ∑ i ∈ Finset.range c.length, (c.getD i 0 : ℤ) * plrs_seq c (n + 1 - i)) := by
    intro c n; rw [plrs_seq]
  have PlrsOne : ∀ c : List ℕ, plrs_seq c 1 = 1 := by intro c; rw [plrs_seq]
  have PlrsPos : ∀ (c : List ℕ), c.getD 0 0 = 1 → ∀ k, 0 ≤ plrs_seq c k ∧ (1 ≤ k → 0 < plrs_seq c k) := by
    intro c hc0 k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases k with _ | _ | n
      · exact ⟨by rw [plrs_seq], by omega⟩
      · exact ⟨by rw [plrs_seq]; norm_num, by intro _; rw [plrs_seq]; norm_num⟩
      · have hlen : 0 < c.length := by
          rcases c with _ | ⟨a, t⟩
          · simp at hc0
          · simp
        rw [PlrsUnfold]
        have hnonneg : ∀ i ∈ Finset.range (n+1), (0:ℤ) ≤ (c.getD i 0 : ℤ) * plrs_seq c (n + 1 - i) := by
          intro i hi
          have hi' : i ≤ n := by simpa using hi
          exact mul_nonneg (by positivity) (ih _ (by omega)).1
        have hnonneg2 : ∀ i ∈ Finset.range c.length, (0:ℤ) ≤ (c.getD i 0 : ℤ) * plrs_seq c (n + 1 - i) := by
          intro i _; exact mul_nonneg (by positivity) (ih _ (by omega)).1
        split_ifs with hh
        · have hs := Finset.sum_nonneg hnonneg
          constructor
          · linarith
          · intro _; linarith
        · have hmem : 0 ∈ Finset.range c.length := by simpa using hlen
          have h0 : (c.getD 0 0 : ℤ) * plrs_seq c (n + 1 - 0) = plrs_seq c (n+1) := by rw [hc0]; norm_num
          have hle := Finset.single_le_sum hnonneg2 hmem
          rw [h0] at hle
          have hpos : 0 < plrs_seq c (n+1) := by apply (ih (n+1) (by omega)).2; omega
          constructor
          · linarith
          · intro _; linarith
  have PlrsMono : ∀ (c : List ℕ), c.getD 0 0 = 1 → ∀ i j, 1 ≤ i → i ≤ j → plrs_seq c i ≤ plrs_seq c j := by
    intro c hc0 i j hi hij
    have PlrsStep : ∀ k, 1 ≤ k → plrs_seq c k ≤ plrs_seq c (k+1) := by
      intro k hk
      have hpos := PlrsPos c hc0
      rcases k with _ | _ | n
      · omega
      · rw [PlrsOne]
        have : 0 < plrs_seq c (1+1) := (hpos (1+1)).2 (by omega)
        linarith
      · have hmem2 : 0 ∈ Finset.range c.length := by
          rcases c with _ | ⟨a, t⟩
          · simp at hc0
          · simp
        rw [PlrsUnfold (c := c) (n := n+1)]
        have hnn1 : ∀ i ∈ Finset.range (n+2), (0:ℤ) ≤ (c.getD i 0 : ℤ) * plrs_seq c (n + 2 - i) := by
          intro i _; exact mul_nonneg (by positivity) (hpos _).1
        have hnn2 : ∀ i ∈ Finset.range c.length, (0:ℤ) ≤ (c.getD i 0 : ℤ) * plrs_seq c (n + 2 - i) := by
          intro i _; exact mul_nonneg (by positivity) (hpos _).1
        have e1 : (c.getD 0 0 : ℤ) * plrs_seq c (n + 2 - 0) = plrs_seq c (n+2) := by rw [hc0]; norm_num
        split_ifs with hh
        · have b := Finset.single_le_sum hnn1 (show 0 ∈ Finset.range (n+1+1) by simp)
          rw [e1] at b; linarith
        · have b := Finset.single_le_sum hnn2 hmem2
          rw [e1] at b; linarith
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih =>
        have hs := PlrsStep j (by omega)
        linarith
  have Brown : ∀ (H : ℕ → ℤ), H 0 = 0 → H 1 = 1 → (∀ i, 1 ≤ i → 0 < H i) →
      (∀ n, 1 ≤ n → H (n+1) ≤ 1 + ∑ i ∈ Finset.range n, H (i+1)) → is_complete_sequence H := by
    intro H h0 h1 hpos hgap t ht
    have himg : ∀ n, ∑ i ∈ (Finset.range n).image (fun i => i+1), H i = ∑ i ∈ Finset.range n, H (i+1) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Finset.range_add_one, Finset.image_insert]
          have h1' : n + 1 ∉ Finset.image (fun i => i+1) (Finset.range n) := by
            simp only [Finset.mem_image, Finset.mem_range]
            rintro ⟨a, ha, hh⟩; omega
          have h2' : n ∉ Finset.range n := by simp
          rw [Finset.sum_insert h1', Finset.sum_insert h2', ih]
    have cover : ∀ n, ∀ t : ℤ, 1 ≤ t → t ≤ ∑ i ∈ Finset.range n, H (i+1) →
        ∃ S : Finset ℕ, (∀ i ∈ S, 1 ≤ i ∧ i ≤ n) ∧ ∑ i ∈ S, H i = t := by
      intro n
      induction n with
      | zero =>
          intro t ht hle
          simp only [Finset.range_zero, Finset.sum_empty] at hle
          omega
      | succ n ih =>
          intro t ht hle
          rw [Finset.sum_range_succ] at hle
          by_cases hcase : t ≤ ∑ i ∈ Finset.range n, H (i+1)
          · obtain ⟨S, hS, hsum⟩ := ih t ht hcase
            exact ⟨S, fun i hi => ⟨(hS i hi).1, by have := (hS i hi).2; omega⟩, hsum⟩
          · push_neg at hcase
            have hHn : H (n+1) ≤ 1 + ∑ i ∈ Finset.range n, H (i+1) := by
              rcases Nat.eq_zero_or_pos n with hn | hn
              · subst hn; simp [h1]
              · exact hgap n hn
            by_cases heq : t = H (n+1)
            · subst heq
              exact ⟨{n+1}, by intro i hi; simp only [Finset.mem_singleton] at hi; omega, by simp⟩
            · have ht2 : 1 ≤ t - H (n+1) := by omega
              have ht3 : t - H (n+1) ≤ ∑ i ∈ Finset.range n, H (i+1) := by linarith
              obtain ⟨S, hS, hsum⟩ := ih (t - H (n+1)) ht2 ht3
              refine ⟨insert (n+1) S, ?_, ?_⟩
              · intro i hi
                simp only [Finset.mem_insert] at hi
                rcases hi with rfl | hi
                · omega
                · have := hS i hi; omega
              · rw [Finset.sum_insert]
                · rw [hsum]; ring
                · intro hmem; have := (hS (n+1) hmem).2; omega
    have hlarge : t ≤ ∑ i ∈ Finset.range t.toNat, H (i+1) := by
      have hb : ∀ i ∈ Finset.range t.toNat, (1:ℤ) ≤ H (i+1) := by
        intro i _; have := hpos (i+1) (by omega); omega
      have := Finset.sum_le_sum hb
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
      have ht' : t ≤ (t.toNat : ℤ) := by omega
      linarith
    obtain ⟨S, hS, hsum⟩ := cover t.toNat t ht hlarge
    exact ⟨S, fun i hi => (hS i hi).1, hsum⟩
  have Nec : ∀ (H : ℕ → ℤ), (∀ i, 1 ≤ i → 0 < H i) → (∀ i j, 1 ≤ i → i ≤ j → H i ≤ H j) →
      is_complete_sequence H → ∀ n, H (n+1) ≤ 1 + ∑ i ∈ Finset.range n, H (i+1) := by
    intro H hpos hmono hc n
    have himg : ∀ n, ∑ i ∈ (Finset.range n).image (fun i => i+1), H i = ∑ i ∈ Finset.range n, H (i+1) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Finset.range_add_one, Finset.image_insert]
          have h1' : n + 1 ∉ Finset.image (fun i => i+1) (Finset.range n) := by
            simp only [Finset.mem_image, Finset.mem_range]
            rintro ⟨a, ha, hh⟩; omega
          have h2' : n ∉ Finset.range n := by simp
          rw [Finset.sum_insert h1', Finset.sum_insert h2', ih]
    have hnn : (0:ℤ) ≤ ∑ i ∈ Finset.range n, H (i+1) :=
      Finset.sum_nonneg (fun i _ => le_of_lt (hpos (i+1) (by omega)))
    obtain ⟨S, hS1, hsum⟩ := hc (1 + ∑ i ∈ Finset.range n, H (i+1)) (by linarith)
    by_cases hsub : ∀ i ∈ S, i ≤ n
    · exfalso
      have hnonneg : ∀ i ∈ (Finset.range n).image (fun i => i + 1), (0:ℤ) ≤ H i := by
        intro i hi
        simp only [Finset.mem_image, Finset.mem_range] at hi
        obtain ⟨j, _, rfl⟩ := hi
        exact le_of_lt (hpos (j+1) (by omega))
      have hsub' : S ⊆ (Finset.range n).image (fun i => i + 1) := by
        intro i hi
        have h1 := hS1 i hi
        have h2 := hsub i hi
        simp only [Finset.mem_image, Finset.mem_range]
        exact ⟨i-1, by omega, by omega⟩
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub' (fun i hi _ => hnonneg i hi)
      rw [himg] at hle
      rw [hsum] at hle
      linarith
    · push_neg at hsub
      obtain ⟨m, hmS, hmn⟩ := hsub
      have hm1 : 1 ≤ m := hS1 m hmS
      have h1 : H (n+1) ≤ H m := hmono (n+1) m (by omega) (by omega)
      have h2 : H m ≤ ∑ i ∈ S, H i :=
        Finset.single_le_sum (fun i hi => le_of_lt (hpos i (hS1 i hi))) hmS
      rw [hsum] at h2
      linarith
  have hcomp0 : is_complete_sequence (plrs_seq [1,0,3,0,3,1]) := by
    have H1 : plrs_seq [1,0,3,0,3,1] 1 = 1 := PlrsOne _
    have H2 : plrs_seq [1,0,3,0,3,1] 2 = 2 := by
      rw [PlrsUnfold [1,0,3,0,3,1] 0]; norm_num [Finset.sum_range_succ, H1]
    have H3 : plrs_seq [1,0,3,0,3,1] 3 = 3 := by
      rw [PlrsUnfold [1,0,3,0,3,1] 1]; norm_num [Finset.sum_range_succ, H1, H2]
    have H4 : plrs_seq [1,0,3,0,3,1] 4 = 7 := by
      rw [PlrsUnfold [1,0,3,0,3,1] 2]; norm_num [Finset.sum_range_succ, H1, H2, H3]
    have H5 : plrs_seq [1,0,3,0,3,1] 5 = 14 := by
      rw [PlrsUnfold [1,0,3,0,3,1] 3]; norm_num [Finset.sum_range_succ, H1, H2, H3, H4]
    have H6 : plrs_seq [1,0,3,0,3,1] 6 = 27 := by
      rw [PlrsUnfold [1,0,3,0,3,1] 4]; norm_num [Finset.sum_range_succ, H1, H2, H3, H4, H5]
    have Hrec : ∀ m, 1 ≤ m → plrs_seq [1,0,3,0,3,1] (m+6) =
        plrs_seq [1,0,3,0,3,1] (m+5) + 3*plrs_seq [1,0,3,0,3,1] (m+3)
          + 3*plrs_seq [1,0,3,0,3,1] (m+1) + plrs_seq [1,0,3,0,3,1] m := by
      intro m hm
      have hh := PlrsUnfold [1,0,3,0,3,1] (m+4)
      rw [show (m+4)+2 = m+6 by omega] at hh
      rw [hh]
      rw [if_neg (by simp only [List.length_cons, List.length_nil]; omega :
        ¬ ((m+4)+2 ≤ ([1,0,3,0,3,1] : List ℕ).length))]
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
      norm_num
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
      rw [show m+4+1 = m+5 by omega, show m+4+1-2 = m+3 by omega,
          show m+4+1-4 = m+1 by omega, show m+4+1-5 = m by omega]
    have H7 : plrs_seq [1,0,3,0,3,1] 7 = 55 := by
      have hh := Hrec 1 (by omega)
      rw [show 1+6 = 7 by omega, show 1+5 = 6 by omega, show 1+3 = 4 by omega,
          show 1+1 = 2 by omega] at hh
      rw [hh, H6, H4, H2, H1]; norm_num
    have H8 : plrs_seq [1,0,3,0,3,1] 8 = 108 := by
      have hh := Hrec 2 (by omega)
      rw [show 2+6 = 8 by omega, show 2+5 = 7 by omega, show 2+3 = 5 by omega,
          show 2+1 = 3 by omega] at hh
      rw [hh, H7, H5, H3, H2]; norm_num
    have H9 : plrs_seq [1,0,3,0,3,1] 9 = 213 := by
      have hh := Hrec 3 (by omega)
      rw [show 3+6 = 9 by omega, show 3+5 = 8 by omega, show 3+3 = 6 by omega,
          show 3+1 = 4 by omega] at hh
      rw [hh, H8, H6, H4, H3]; norm_num
    have H10 : plrs_seq [1,0,3,0,3,1] 10 = 427 := by
      have hh := Hrec 4 (by omega)
      rw [show 4+6 = 10 by omega, show 4+5 = 9 by omega, show 4+3 = 7 by omega,
          show 4+1 = 5 by omega] at hh
      rw [hh, H9, H7, H5, H4]; norm_num
    have H11 : plrs_seq [1,0,3,0,3,1] 11 = 846 := by
      have hh := Hrec 5 (by omega)
      rw [show 5+6 = 11 by omega, show 5+5 = 10 by omega, show 5+3 = 8 by omega,
          show 5+1 = 6 by omega] at hh
      rw [hh, H10, H8, H6, H5]; norm_num
    have H12 : plrs_seq [1,0,3,0,3,1] 12 = 1677 := by
      have hh := Hrec 6 (by omega)
      rw [show 6+6 = 12 by omega, show 6+5 = 11 by omega, show 6+3 = 9 by omega,
          show 6+1 = 7 by omega] at hh
      rw [hh, H11, H9, H7, H6]; norm_num
    have H13 : plrs_seq [1,0,3,0,3,1] 13 = 3337 := by
      have hh := Hrec 7 (by omega)
      rw [show 7+6 = 13 by omega, show 7+5 = 12 by omega, show 7+3 = 10 by omega,
          show 7+1 = 8 by omega] at hh
      rw [hh, H12, H10, H8, H7]; norm_num
    have H14 : plrs_seq [1,0,3,0,3,1] 14 = 6622 := by
      have hh := Hrec 8 (by omega)
      rw [show 8+6 = 14 by omega, show 8+5 = 13 by omega, show 8+3 = 11 by omega,
          show 8+1 = 9 by omega] at hh
      rw [hh, H13, H11, H9, H8]; norm_num
    have H15 : plrs_seq [1,0,3,0,3,1] 15 = 13147 := by
      have hh := Hrec 9 (by omega)
      rw [show 9+6 = 15 by omega, show 9+5 = 14 by omega, show 9+3 = 12 by omega,
          show 9+1 = 10 by omega] at hh
      rw [hh, H14, H12, H10, H9]; norm_num
    have H16 : plrs_seq [1,0,3,0,3,1] 16 = 26123 := by
      have hh := Hrec 10 (by omega)
      rw [show 10+6 = 16 by omega, show 10+5 = 15 by omega, show 10+3 = 13 by omega,
          show 10+1 = 11 by omega] at hh
      rw [hh, H15, H13, H11, H10]; norm_num
    have H0 : plrs_seq [1,0,3,0,3,1] 0 = 0 := by rw [plrs_seq]
    let E : ℕ → ℤ := fun k => plrs_seq [1,0,3,0,3,1] (k+5) - 3*plrs_seq [1,0,3,0,3,1] (k+3)
        - 3*plrs_seq [1,0,3,0,3,1] (k+1) - plrs_seq [1,0,3,0,3,1] k
    have hEbase : 0 ≤ E 5 ∧ 0 ≤ E 6 ∧ 0 ≤ E 7 ∧ 0 ≤ E 8 ∧ 0 ≤ E 9 ∧ 0 ≤ E 10 := by
      simp only [E]
      norm_num [H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15]
    have hErec : ∀ k, 1 ≤ k → E (k+6) = E (k+5) + 3*E (k+3) + 3*E (k+1) + E k := by
      intro k hk
      simp only [E]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      linear_combination (1:ℤ) * Hrec (k+5) (by omega) + (-3:ℤ) * Hrec (k+3) (by omega)
        + (-3:ℤ) * Hrec (k+1) (by omega) + (-1:ℤ) * Hrec k (by omega)
    have hEkey : ∀ m, 0 ≤ E (m+5) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        rcases m with _ | _ | _ | _ | _ | _ | m
        · exact hEbase.1
        · exact hEbase.2.1
        · exact hEbase.2.2.1
        · exact hEbase.2.2.2.1
        · exact hEbase.2.2.2.2.1
        · exact hEbase.2.2.2.2.2
        · have hstep := hErec (m+5) (by omega)
          have i1 : 0 ≤ E ((m+5)+5) := ih (m+5) (by omega)
          have i2 : 0 ≤ E ((m+5)+3) := ih (m+3) (by omega)
          have i3 : 0 ≤ E ((m+5)+1) := ih (m+1) (by omega)
          have i4 : 0 ≤ E (m+5) := ih m (by omega)
          rw [show m+6+5 = (m+5)+6 by omega]
          linarith
    have hD : ∀ n, 9 ≤ n → 0 ≤ 2*plrs_seq [1,0,3,0,3,1] (n+1) - plrs_seq [1,0,3,0,3,1] (n+2) := by
      intro n hn
      have hEq : E (n-4) = plrs_seq [1,0,3,0,3,1] (n+1) - 3*plrs_seq [1,0,3,0,3,1] (n-1)
          - 3*plrs_seq [1,0,3,0,3,1] (n-3) - plrs_seq [1,0,3,0,3,1] (n-4) := by
        simp only [E]
        rw [show n-4+5 = n+1 by omega, show n-4+3 = n-1 by omega, show n-4+1 = n-3 by omega]
      have hrec := Hrec (n-4) (by omega)
      rw [show n-4+6 = n+2 by omega, show n-4+5 = n+1 by omega, show n-4+3 = n-1 by omega,
          show n-4+1 = n-3 by omega] at hrec
      have key : 0 ≤ E (n-4) := by
        have hk := hEkey (n-9)
        rwa [show n-9+5 = n-4 by omega] at hk
      have hD_eq : 2*plrs_seq [1,0,3,0,3,1] (n+1) - plrs_seq [1,0,3,0,3,1] (n+2) = E (n-4) := by
        rw [hEq]; linarith
      rw [hD_eq]; exact key
    let G : ℕ → ℤ := fun k => 1 + ∑ i ∈ Finset.range k, plrs_seq [1,0,3,0,3,1] (i+1)
        - plrs_seq [1,0,3,0,3,1] (k+1)
    have hGstep : ∀ k, G (k+1) = G k + (2*plrs_seq [1,0,3,0,3,1] (k+1) - plrs_seq [1,0,3,0,3,1] (k+2)) := by
      intro k; simp only [G]; rw [Finset.sum_range_succ]; ring
    have hG9 : 0 ≤ G 9 := by
      simp only [G]
      norm_num [Finset.sum_range_succ, Finset.sum_range_zero, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10]
    have hGbig : ∀ j, 0 ≤ G (9+j) := by
      intro j; induction j with
      | zero => simpa using hG9
      | succ j ih =>
          have hstep := hGstep (9+j)
          have hd := hD (9+j) (by omega)
          rw [show 9+(j+1) = 9+j+1 by omega]
          linarith
    have hGsmall : ∀ n, 1 ≤ n → n ≤ 9 → 0 ≤ G n := by
      intro n h1 h2
      interval_cases n <;> simp only [G] <;>
        norm_num [Finset.sum_range_succ, Finset.sum_range_zero, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10]
    have hGall : ∀ n, 1 ≤ n → 0 ≤ G n := by
      intro n hn
      by_cases hlt : n ≤ 9
      · exact hGsmall n hn hlt
      · obtain ⟨j, rfl⟩ : ∃ j, n = 9 + j := ⟨n - 9, by omega⟩
        exact hGbig j
    refine Brown _ H0 H1 (fun i hi => (PlrsPos _ (by decide) i).2 hi) ?_
    intro n hn
    have hG := hGall n hn
    simp only [G] at hG
    linarith
  have hcomp1 : is_complete_sequence (plrs_seq [1,1,0,3,0,3,1]) := by
    have hh := h [1,0,3,0,3,1] (by decide) (by decide) (by decide) hcomp0
    simpa using hh
  have A1 : plrs_seq [1,1,0,3,0,3,1] 1 = 1 := PlrsOne _
  have A2 : plrs_seq [1,1,0,3,0,3,1] 2 = 2 := by
    rw [PlrsUnfold [1,1,0,3,0,3,1] 0]; norm_num [Finset.sum_range_succ, A1]
  have A3 : plrs_seq [1,1,0,3,0,3,1] 3 = 4 := by
    rw [PlrsUnfold [1,1,0,3,0,3,1] 1]; norm_num [Finset.sum_range_succ, A1, A2]
  have A4 : plrs_seq [1,1,0,3,0,3,1] 4 = 7 := by
    rw [PlrsUnfold [1,1,0,3,0,3,1] 2]; norm_num [Finset.sum_range_succ, A1, A2, A3]
  have A5 : plrs_seq [1,1,0,3,0,3,1] 5 = 15 := by
    rw [PlrsUnfold [1,1,0,3,0,3,1] 3]; norm_num [Finset.sum_range_succ, A1, A2, A3, A4]
  have A6 : plrs_seq [1,1,0,3,0,3,1] 6 = 29 := by
    rw [PlrsUnfold [1,1,0,3,0,3,1] 4]; norm_num [Finset.sum_range_succ, A1, A2, A3, A4, A5]
  have A7 : plrs_seq [1,1,0,3,0,3,1] 7 = 60 := by
    rw [PlrsUnfold [1,1,0,3,0,3,1] 5]; norm_num [Finset.sum_range_succ, A1, A2, A3, A4, A5, A6]
  have hcontra := Nec _ (fun i hi => (PlrsPos _ (by decide) i).2 hi) (PlrsMono _ (by decide)) hcomp1 6
  rw [A7] at hcontra
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, A1, A2, A3, A4, A5, A6] at hcontra
  norm_num at hcontra
