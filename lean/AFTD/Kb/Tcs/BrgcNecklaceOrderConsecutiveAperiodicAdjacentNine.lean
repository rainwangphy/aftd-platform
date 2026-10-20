import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BrgcNecklaceFirstRank
import AFTD.Kb.Tcs.BitwordNecklaceAdjacent
import AFTD.Kb.Tcs.BitwordIsAperiodic
import AFTD.Kb.Tcs.BitwordRotate
import AFTD.Kb.Tcs.BitwordIsRotation

/-!
# brgc_necklace_order_consecutive_aperiodic_adjacent_nine

Topic: combinatorics   Node: eeda04d229ea

Provenance: helper lemma. case n = 9 of brgc_necklace_order_consecutive_aperiodic_adjacent (exp 1939)

The case n = 9 (composite, with periodic necklaces that break the adjacency) of the aperiodic adjacency conjecture: consecutive aperiodic necklaces of D_9 are adjacent in Q_9.
-/

def brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks : List ℕ :=
  [1, 2, 5, 6, 9, 10, 13, 14, 17, 18, 21, 22, 25, 26, 29, 30, 33, 34, 37, 38,
   41, 42, 45, 46, 49, 50, 53, 54, 57, 58, 69, 70, 73, 74, 77, 78, 81, 82, 85, 86,
   89, 90, 101, 102, 105, 106, 109, 110, 113, 146, 149, 150, 153, 154, 165, 166, 169, 170]

instance brgc_necklace_order_consecutive_aperiodic_adjacent_nine_dec_rot (n x y : ℕ) :
    Decidable (bitword_is_rotation n x y) := by
  unfold bitword_is_rotation
  infer_instance

instance brgc_necklace_order_consecutive_aperiodic_adjacent_nine_dec_rank (n t : ℕ) :
    Decidable (brgc_necklace_first_rank n t) := by
  unfold brgc_necklace_first_rank
  infer_instance

instance brgc_necklace_order_consecutive_aperiodic_adjacent_nine_dec_adj (n x y : ℕ) :
    Decidable (bitword_necklace_adjacent n x y) := by
  unfold bitword_necklace_adjacent
  infer_instance

instance brgc_necklace_order_consecutive_aperiodic_adjacent_nine_dec_aperiodic (n x : ℕ) :
    Decidable (bitword_is_aperiodic n x) :=
  decidable_of_iff (∀ r < n, 0 < r → (bitword_rotate n)^[r] x ≠ x) ⟨
    fun h r hr0 hrn => h r hrn hr0,
    fun h r hrn hr0 => h r hr0 hrn
  ⟩

theorem brgc_necklace_order_consecutive_aperiodic_adjacent_nine_lt_171 :
    ∀ s ∈ brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks, s < 171 := by
  decide

theorem brgc_necklace_order_consecutive_aperiodic_adjacent_nine_rot_bound :
    ∀ (t : Fin 512), 171 ≤ ↑t → brgc_word ↑t ≠ 2 ^ 9 - 1 →
      ∃ s ∈ brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks,
        bitword_is_rotation 9 (brgc_word s) (brgc_word ↑t) := by
  decide

theorem brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks_iff :
    ∀ (s : Fin 171), brgc_necklace_first_rank 9 ↑s ↔
      ↑s ∈ brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks := by
  decide

theorem brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks_prop :
    ∀ t ∈ brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks,
    bitword_is_aperiodic 9 (brgc_word t) →
    ∀ t' ∈ brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks,
    t < t' →
    bitword_is_aperiodic 9 (brgc_word t') →
    (∀ s ∈ brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks, ¬ (t < s ∧ s < t')) →
    bitword_necklace_adjacent 9 (brgc_word t) (brgc_word t') := by
  decide

theorem brgc_necklace_order_consecutive_aperiodic_adjacent_nine :
    ∀ t t' : ℕ, brgc_necklace_first_rank 9 t → brgc_necklace_first_rank 9 t' → t < t' →
      (∀ s, t < s → s < t' → ¬ brgc_necklace_first_rank 9 s) →
      bitword_is_aperiodic 9 (brgc_word t) → bitword_is_aperiodic 9 (brgc_word t') →
      bitword_necklace_adjacent 9 (brgc_word t) (brgc_word t') := by
  intro t t' ht ht' hlt hbetween hap hap'
  have ht'_lt : t' < 171 := by
    by_contra hnot
    have hge : 171 ≤ t' := by omega
    have ht'_512 : t' < 512 := ht'.1
    have hne : brgc_word t' ≠ 2 ^ 9 - 1 := ht'.2.2.1
    rcases brgc_necklace_order_consecutive_aperiodic_adjacent_nine_rot_bound ⟨t', ht'_512⟩ hge hne with ⟨s, hs_in, hs_rot⟩
    have hs_lt_171 : s < 171 := brgc_necklace_order_consecutive_aperiodic_adjacent_nine_lt_171 s hs_in
    have hs_lt_t' : s < t' := by omega
    exact ht'.2.2.2 s hs_lt_t' hs_rot
  have ht_lt : t < 171 := by omega
  have ht_in : t ∈ brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks :=
    (brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks_iff ⟨t, ht_lt⟩).mp ht
  have ht'_in : t' ∈ brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks :=
    (brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks_iff ⟨t', ht'_lt⟩).mp ht'
  have hno_between : ∀ s ∈ brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks, ¬ (t < s ∧ s < t') := by
    intro s hs_in ⟨hts, hst'⟩
    have hs_lt : s < 171 := by omega
    have hs_rank : brgc_necklace_first_rank 9 s :=
      (brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks_iff ⟨s, hs_lt⟩).mpr hs_in
    exact hbetween s hts hst' hs_rank
  exact brgc_necklace_order_consecutive_aperiodic_adjacent_nine_ranks_prop t ht_in hap t' ht'_in hlt hap' hno_between
