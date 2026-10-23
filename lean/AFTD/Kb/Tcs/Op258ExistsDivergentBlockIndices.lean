import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op_258_exists_divergent_block_indices

Topic: combinatorics   Node: 46c6145a66fb

Provenance: helper lemma. step towards op_258_exists_divergent_capacity_covering

For any positive antitone sequence a : ℕ+ → ℝ with divergent sum and any n₀, there exist l ≥ 3 with 2^l ≥ n₀ and strictly increasing r : Fin (l+1) → ℕ+ such that a(r(l)) ≥ 1 / 2^{l-1} and the sum of a on each interval (r(j), r(j+1)] is at least 1 / 2^j.
-/

/-- A sum over an interval of `ℕ+` is the sum over the interval of `ℕ` of `a ∘ toPNat'`. -/
theorem op258b_sum_Ioc_pnat (a : ℕ+ → ℝ) (x y : ℕ+) :
    ∑ i ∈ Finset.Ioc x y, a i = ∑ n ∈ Finset.Ioc (x : ℕ) (y : ℕ), a n.toPNat' := by
  refine Finset.sum_nbij' (fun i => (i : ℕ)) (fun n => n.toPNat') ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Ioc] at hi ⊢
    exact ⟨PNat.coe_lt_coe _ _ |>.mpr hi.1, PNat.coe_le_coe _ _ |>.mpr hi.2⟩
  · intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn.1
    refine ⟨?_, ?_⟩
    · rw [← PNat.coe_lt_coe, PNat.toPNat'_coe hn0]; exact hn.1
    · rw [← PNat.coe_le_coe, PNat.toPNat'_coe hn0]; exact hn.2
  · intro i _
    exact PNat.coe_toPNat' i
  · intro n hn
    rw [Finset.mem_Ioc] at hn
    exact PNat.toPNat'_coe (lt_of_le_of_lt (Nat.zero_le _) hn.1)
  · intro i _
    rw [PNat.coe_toPNat']

/-- Greedy blocks over `ℕ`: if all tail sums of a positive sequence are unbounded, then for
every `L₀` there are `l ≥ L₀` and strictly increasing `r` with `r 0 = 1`, block sums at least
`1 / 2^j` and `1 / 2^(l-1) ≤ b (r l)`. -/
theorem op258b_greedy (b : ℕ → ℝ) (hpos : ∀ n, 0 < b n)
    (hunb : ∀ m : ℕ, ∀ C : ℝ, ∃ k, C ≤ ∑ n ∈ Finset.Ioc m k, b n) (L₀ : ℕ) :
    ∃ l, L₀ ≤ l ∧ ∃ r : ℕ → ℕ, r 0 = 1 ∧ StrictMono r ∧ 1 / (2 : ℝ) ^ (l - 1) ≤ b (r l) ∧
      ∀ j, j < l → 1 / (2 : ℝ) ^ j ≤ ∑ n ∈ Finset.Ioc (r j) (r (j + 1)), b n := by
  classical
  have hex : ∀ m j : ℕ, ∃ k, 1 / (2 : ℝ) ^ j ≤ ∑ n ∈ Finset.Ioc m k, b n :=
    fun m j => hunb m _
  let r : ℕ → ℕ := fun j => Nat.rec 1 (fun j rj => Nat.find (hex rj j)) j
  have hr0 : r 0 = 1 := rfl
  have hrs : ∀ j, r (j + 1) = Nat.find (hex (r j) j) := fun j => rfl
  have hspec : ∀ j, 1 / (2 : ℝ) ^ j ≤ ∑ n ∈ Finset.Ioc (r j) (r (j + 1)), b n := by
    intro j; rw [hrs]; exact Nat.find_spec (hex (r j) j)
  have hlt : ∀ j, r j < r (j + 1) := by
    intro j
    by_contra hc
    rw [not_lt] at hc
    have := hspec j
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty] at this
    have : (0 : ℝ) < 1 / 2 ^ j := by positivity
    linarith
  have hmono : StrictMono r := strictMono_nat_of_lt_succ hlt
  -- the block sum overshoots by at most its last term
  have hover : ∀ j, ∑ n ∈ Finset.Ioc (r j) (r (j + 1)), b n < 1 / (2 : ℝ) ^ j + b (r (j + 1)) := by
    intro j
    obtain ⟨k, hk⟩ : ∃ k, r (j + 1) = k + 1 := ⟨r (j + 1) - 1, by have := hlt j; omega⟩
    have hjk : r j ≤ k := by have := hlt j; omega
    have hmin : ¬ (1 / (2 : ℝ) ^ j ≤ ∑ n ∈ Finset.Ioc (r j) k, b n) := by
      have := Nat.find_min (hex (r j) j) (m := k) (by rw [← hrs]; omega)
      exact this
    rw [hk, Finset.sum_Ioc_succ_top hjk]
    linarith [not_le.mp hmin]
  suffices hl : ∃ l, L₀ ≤ l ∧ 1 / (2 : ℝ) ^ (l - 1) ≤ b (r l) by
    obtain ⟨l, hl, hb⟩ := hl
    exact ⟨l, hl, r, hr0, hmono, hb, fun j _ => hspec j⟩
  by_contra hcon
  push_neg at hcon
  -- every block from `L₀` on is small
  have hsmall : ∀ i, ∑ n ∈ Finset.Ioc (r (L₀ + i)) (r (L₀ + i + 1)), b n ≤ 2 / (2 : ℝ) ^ i := by
    intro i
    have h1 := hover (L₀ + i)
    have h2 := hcon (L₀ + i + 1) (by omega)
    rw [show L₀ + i + 1 - 1 = L₀ + i by omega] at h2
    have h3 : 1 / (2 : ℝ) ^ (L₀ + i) ≤ 1 / 2 ^ i := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : 2 / (2 : ℝ) ^ i = 1 / 2 ^ i + 1 / 2 ^ i := by ring
    linarith
  have htot : ∀ k, ∑ n ∈ Finset.Ioc (r L₀) (r (L₀ + k)), b n ≤ 4 - 4 / (2 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← Finset.sum_Ioc_consecutive _ (hmono.monotone (Nat.le_add_right L₀ k))
        (hmono.monotone (by omega : L₀ + k ≤ L₀ + (k + 1)))]
      have := hsmall k
      rw [show L₀ + k + 1 = L₀ + (k + 1) by omega] at this
      have h5 : 4 - 4 / (2 : ℝ) ^ (k + 1) = 4 - 4 / 2 ^ k + 2 / 2 ^ k := by
        rw [pow_succ]; field_simp; ring
      linarith
  obtain ⟨k, hk⟩ := hunb (r L₀) 5
  have hkle : k ≤ r (L₀ + k) := by have := hmono.id_le (L₀ + k); simp only [id] at this; omega
  have hsub : ∑ n ∈ Finset.Ioc (r L₀) k, b n ≤ ∑ n ∈ Finset.Ioc (r L₀) (r (L₀ + k)), b n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hkle)
      (fun n _ _ => (hpos n).le)
  have h6 := htot k
  have h7 : 0 < 4 / (2 : ℝ) ^ k := by positivity
  linarith

/-- For any positive antitone sequence with divergent ENNReal sum and threshold n_0, there exists l >= 3 with 2^l >= n_0 and strictly increasing block endpoints r : Fin (l+1) -> PNat such that a(r(l)) >= 1 / 2^{l-1} and each block has sum >= 1 / 2^j. -/
theorem op_258_exists_divergent_block_indices
    (a : ℕ+ → ℝ) (hpos : ∀ i, 0 < a i) (hanti : Antitone a)
    (hsum : (∑' i : ℕ+, ENNReal.ofReal (a i)) = ⊤) (n₀ : ℕ) :
    ∃ (l : ℕ) (hl : 3 ≤ l) (r : Fin (l + 1) → ℕ+),
      n₀ ≤ 2^l ∧
      (StrictMono r) ∧
      (1 / (2 : ℝ)^(l - 1) ≤ a (r ⟨l, by omega⟩)) ∧
      (∀ j : Fin l, 1 / (2 : ℝ)^(j : ℕ) ≤ ∑ i ∈ Finset.Ioc (r ⟨j.1, by omega⟩) (r ⟨j.1 + 1, by omega⟩), a i) := by
  classical
  set b : ℕ → ℝ := fun n => a n.toPNat' with hb
  have hbpos : ∀ n, 0 < b n := fun n => hpos _
  have hns : ¬ Summable a := by
    intro hs
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (hpos i).le) hs] at hsum
    exact ENNReal.ofReal_ne_top hsum
  have hunb : ∀ m : ℕ, ∀ C : ℝ, ∃ k, C ≤ ∑ n ∈ Finset.Ioc m k, b n := by
    intro m C
    by_contra hcon
    push_neg at hcon
    apply hns
    refine summable_of_sum_le (c := ∑ n ∈ Finset.Ioc 0 m, b n + C) (fun i => (hpos i).le) ?_
    intro u
    set e : ℕ+ ↪ ℕ := ⟨fun i => (i : ℕ), PNat.coe_injective⟩
    set K := max m (u.sup fun i => (i : ℕ))
    have h1 : ∑ i ∈ u, a i = ∑ n ∈ u.map e, b n := by
      rw [Finset.sum_map]
      exact Finset.sum_congr rfl (fun i _ => by simp [hb, e, PNat.coe_toPNat'])
    have h2 : u.map e ⊆ Finset.Ioc 0 K := by
      intro n hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hn
      simp only [Finset.mem_Ioc, e, Function.Embedding.coeFn_mk]
      exact ⟨i.pos, le_trans (Finset.le_sup (f := fun i : ℕ+ => (i : ℕ)) hi) (le_max_right _ _)⟩
    have h3 : ∑ n ∈ u.map e, b n ≤ ∑ n ∈ Finset.Ioc 0 K, b n :=
      Finset.sum_le_sum_of_subset_of_nonneg h2 (fun n _ _ => (hbpos n).le)
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le m) (le_max_left m _)] at h3
    have h4 := hcon K
    linarith
  obtain ⟨l, hl, r, hr0, hmono, hend, hblk⟩ := op258b_greedy b hbpos hunb (max 3 n₀)
  have hrpos : ∀ j, 0 < r j := fun j => lt_of_lt_of_le (by omega) (hr0 ▸ hmono.monotone (Nat.zero_le j))
  refine ⟨l, le_trans (le_max_left _ _) hl, fun j => ⟨r j, hrpos j⟩, ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_trans (le_max_right _ _) hl) (Nat.lt_two_pow_self).le
  · intro x y hxy
    show r x < r y
    exact hmono hxy
  · show 1 / (2 : ℝ) ^ (l - 1) ≤ a ⟨r l, hrpos l⟩
    have : b (r l) = a ⟨r l, hrpos l⟩ := by
      simp only [hb]; congr 1; exact PNat.eq (PNat.toPNat'_coe (hrpos l))
    rw [← this]; exact hend
  · intro j
    have h := op258b_sum_Ioc_pnat a ⟨r j, hrpos j⟩ ⟨r (j + 1), hrpos _⟩
    have h2 := hblk j.1 j.2
    rw [← PNat.mk_coe (r j) (hrpos j), ← PNat.mk_coe (r (j + 1)) (hrpos _)] at h2
    exact le_of_le_of_eq h2 h.symm
