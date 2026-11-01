import AFTD.Prelude

/-!
# embedding_range_contains_fraction

Topic: quantum   Node: 284981a8f28d

Provenance: helper lemma. arXiv:2610.34762 Lemma 6 proof (Step 4)

For any fixed element m of Fin n and any 0 < k <= n, the fraction of embeddings from Fin k into Fin n whose range contains m equals k / n.
-/

open Finset

def embedding_range_contains_fraction_swapEmbed {k n : ℕ} (m m' : Fin n)
    (f : Fin k ↪ Fin n) : Fin k ↪ Fin n :=
  f.trans (Equiv.swap m m').toEmbedding

lemma embedding_range_contains_fraction_swapEmbed_involutive {k n : ℕ}
    (m m' : Fin n) (f : Fin k ↪ Fin n) :
    embedding_range_contains_fraction_swapEmbed m m'
      (embedding_range_contains_fraction_swapEmbed m m' f) = f := by
  ext x
  simp [embedding_range_contains_fraction_swapEmbed]

lemma embedding_range_contains_fraction_swapEmbed_bijective {k n : ℕ} (m m' : Fin n) :
    Function.Bijective (embedding_range_contains_fraction_swapEmbed (k := k) m m') :=
  Function.bijective_iff_has_inverse.mpr
    ⟨embedding_range_contains_fraction_swapEmbed m m',
     embedding_range_contains_fraction_swapEmbed_involutive m m',
     embedding_range_contains_fraction_swapEmbed_involutive m m'⟩

lemma embedding_range_contains_fraction_mem_range_swapEmbed {k n : ℕ}
    (m m' : Fin n) (f : Fin k ↪ Fin n) :
    m' ∈ Set.range (embedding_range_contains_fraction_swapEmbed m m' f) ↔ m ∈ Set.range f := by
  simp [embedding_range_contains_fraction_swapEmbed, Set.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    use x
    have h := congr_arg (Equiv.swap m m') hx
    simp only [Equiv.swap_apply_right, Equiv.swap_apply_self] at h
    exact h
  · rintro ⟨x, hx⟩
    use x
    simp [hx]

lemma embedding_range_contains_fraction_card_filter_range_eq {k n : ℕ} (m m' : Fin n) :
    (Finset.univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f)).card =
    (Finset.univ.filter (fun f : Fin k ↪ Fin n => m' ∈ Set.range f)).card := by
  apply Finset.card_bijective
    (embedding_range_contains_fraction_swapEmbed m m')
    (embedding_range_contains_fraction_swapEmbed_bijective m m')
  intro f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (embedding_range_contains_fraction_mem_range_swapEmbed m m' f).symm

lemma embedding_range_contains_fraction_sum_card_filter_eq {k n : ℕ} :
    (∑ m : Fin n, (univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f)).card) =
    (Fintype.card (Fin k ↪ Fin n)) * k := by
  have h1 : ∀ m : Fin n, (univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f)).card =
      ∑ f : Fin k ↪ Fin n, if m ∈ Set.range f then 1 else 0 := by
    intro m
    exact card_filter _ univ
  simp_rw [h1]
  rw [sum_comm]
  have h2 : ∀ f : Fin k ↪ Fin n, (∑ m : Fin n, if m ∈ Set.range f then 1 else 0) = k := by
    intro f
    have h3 : (∑ m : Fin n, if m ∈ Set.range f then 1 else 0) =
        (univ.filter (fun m : Fin n => m ∈ Set.range f)).card := by
      exact (card_filter (fun m => m ∈ Set.range f) univ).symm
    rw [h3]
    have h4 : (univ.filter (fun m : Fin n => m ∈ Set.range f)) = univ.map f := by
      ext x
      simp
    rw [h4, card_map, card_univ, Fintype.card_fin]
  simp_rw [h2]
  rw [sum_const, card_univ, smul_eq_mul]

/-- For any fixed element `m : Fin n`, the fraction of embeddings `f : Fin k ↪ Fin n` whose range contains `m` is `k / n`. -/
theorem embedding_range_contains_fraction {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (m : Fin n) :
    ((Finset.univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f)).card : ℝ) /
      (Fintype.card (Fin k ↪ Fin n) : ℝ) = (k : ℝ) / (n : ℝ) := by
  have hsum : (Finset.sum Finset.univ fun m' : Fin n => (Finset.univ.filter (fun f : Fin k ↪ Fin n => m' ∈ Set.range f)).card) =
      n * (Finset.univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f)).card := by
    have : (Finset.sum Finset.univ fun m' : Fin n => (Finset.univ.filter (fun f : Fin k ↪ Fin n => m' ∈ Set.range f)).card) =
        Finset.sum Finset.univ fun m' : Fin n => (Finset.univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f)).card := by
      apply Finset.sum_congr rfl
      intro m' _
      exact (embedding_range_contains_fraction_card_filter_range_eq m m').symm
    rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h_nat : n * (Finset.univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f)).card =
      (Fintype.card (Fin k ↪ Fin n)) * k := by
    rw [← hsum, embedding_range_contains_fraction_sum_card_filter_eq]
  have h_real : (n : ℝ) * ((Finset.univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f)).card : ℝ) =
      (Fintype.card (Fin k ↪ Fin n) : ℝ) * (k : ℝ) := by
    exact_mod_cast congr_arg (fun x : ℕ => (x : ℝ)) h_nat
  have hn : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := by omega
    positivity
  have hcard : (Fintype.card (Fin k ↪ Fin n) : ℝ) ≠ 0 := by
    have : Nonempty (Fin k ↪ Fin n) := Fin.nonempty_embedding_iff.mpr hkn
    have : Fintype.card (Fin k ↪ Fin n) ≠ 0 := Fintype.card_ne_zero
    positivity
  apply (div_eq_div_iff hcard hn).mpr
  linarith
