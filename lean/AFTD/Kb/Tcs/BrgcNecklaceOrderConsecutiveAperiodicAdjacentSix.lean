import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BrgcNecklaceFirstRank
import AFTD.Kb.Tcs.BitwordNecklaceAdjacent
import AFTD.Kb.Tcs.BitwordIsAperiodic
import AFTD.Kb.Tcs.BitwordIsRotation
import AFTD.Kb.Tcs.BitwordRotate

/-!
# brgc_necklace_order_consecutive_aperiodic_adjacent_six

Topic: combinatorics   Node: a66390a369ce

Provenance: helper lemma. case n = 6 of brgc_necklace_order_consecutive_aperiodic_adjacent (exp 1939)

The case n = 6 (composite, with periodic necklaces that break the adjacency) of the aperiodic adjacency conjecture: consecutive aperiodic necklaces of D_6 are adjacent in Q_6.
-/

instance brgc_necklace_order_consecutive_aperiodic_adjacent_six_dec_rot (n x y : ℕ) :
    Decidable (bitword_is_rotation n x y) := by
  unfold bitword_is_rotation
  infer_instance

instance brgc_necklace_order_consecutive_aperiodic_adjacent_six_dec_rank (n t : ℕ) :
    Decidable (brgc_necklace_first_rank n t) := by
  unfold brgc_necklace_first_rank
  infer_instance

instance brgc_necklace_order_consecutive_aperiodic_adjacent_six_dec_adj (n x y : ℕ) :
    Decidable (bitword_necklace_adjacent n x y) := by
  unfold bitword_necklace_adjacent
  infer_instance

instance brgc_necklace_order_consecutive_aperiodic_adjacent_six_dec_aperiodic (n x : ℕ) :
    Decidable (bitword_is_aperiodic n x) :=
  decidable_of_iff (∀ r < n, 0 < r → (bitword_rotate n)^[r] x ≠ x) ⟨
    fun h r hr0 hrn => h r hrn hr0,
    fun h r hrn hr0 => h r hr0 hrn
  ⟩

theorem brgc_necklace_order_consecutive_aperiodic_adjacent_six_fin :
    ∀ t t' : Fin 64,
      brgc_necklace_first_rank 6 t.1 → brgc_necklace_first_rank 6 t'.1 → t.1 < t'.1 →
      (∀ s : Fin 64, t.1 < s.1 → s.1 < t'.1 → ¬ brgc_necklace_first_rank 6 s.1) →
      bitword_is_aperiodic 6 (brgc_word t.1) → bitword_is_aperiodic 6 (brgc_word t'.1) →
      bitword_necklace_adjacent 6 (brgc_word t.1) (brgc_word t'.1) := by
  decide

theorem brgc_necklace_order_consecutive_aperiodic_adjacent_six :
    ∀ t t' : ℕ, brgc_necklace_first_rank 6 t → brgc_necklace_first_rank 6 t' → t < t' →
      (∀ s, t < s → s < t' → ¬ brgc_necklace_first_rank 6 s) →
      bitword_is_aperiodic 6 (brgc_word t) → bitword_is_aperiodic 6 (brgc_word t') →
      bitword_necklace_adjacent 6 (brgc_word t) (brgc_word t') := by
  intro t t' ht ht' hlt hbetween hap hap'
  have ht_lt : t < 64 := ht.1
  have ht'_lt : t' < 64 := ht'.1
  exact brgc_necklace_order_consecutive_aperiodic_adjacent_six_fin
    ⟨t, ht_lt⟩ ⟨t', ht'_lt⟩ ht ht' hlt
    (fun s hs1 hs2 => hbetween s.1 hs1 hs2) hap hap'
