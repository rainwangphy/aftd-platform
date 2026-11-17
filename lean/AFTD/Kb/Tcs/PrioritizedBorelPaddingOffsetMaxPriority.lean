import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelPaddingOffsetNonzeroFrequently
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# prioritized_borel_padding_offset_max_priority

Topic: automata   Node: f189738f1094

Provenance: helper lemma. Priority padding for the state-history reduction of arXiv:2611.10136, Conjecture 19.

For any three-priority sequence and fixed offset r within blocks of positive length L, replacing each value by a block with that value at offset r and the lowest priority elsewhere preserves the maximal priority occurring infinitely often.
-/

open Filter

def pad1385 (L r : ℕ) (f : ℕ → Fin 3) (n : ℕ) : Fin 3 :=
  if n % L = r then f (n / L) else 0

def maxInf1385 (f : ℕ → Fin 3) (p : Fin 3) : Prop :=
  Filter.Frequently (fun n => f n = p) Filter.atTop ∧
  ∀ q : Fin 3, p < q → ¬ Filter.Frequently (fun n => f n = q) Filter.atTop

lemma freqZero1385 (f : ℕ → Fin 3)
    (h : ∀ q : Fin 3, 0 < q → ¬ Filter.Frequently (fun n => f n = q) Filter.atTop) :
    Filter.Frequently (fun n => f n = 0) Filter.atTop := by
  have he : ∃ q : Fin 3, Filter.Frequently (fun n => f n = q) Filter.atTop := by
    apply Filter.frequently_exists.mp
    exact Filter.Frequently.of_forall (fun n => ⟨f n, rfl⟩)
  obtain ⟨q, hq⟩ := he
  by_cases hz : q = 0
  · simpa [hz] using hq
  · have hpos : (0 : Fin 3) < q := by fin_cases q <;> simp_all
    exact False.elim (h q hpos hq)

theorem prioritized_borel_padding_offset_max_priority (L r : ℕ) (hr : r < L) (f : ℕ → Fin 3) (p : Fin 3) :
  (Filter.Frequently (fun n => (if n % L = r then f (n / L) else 0) = p) Filter.atTop ∧
    ∀ q : Fin 3, p < q → ¬ Filter.Frequently (fun n => (if n % L = r then f (n / L) else 0) = q) Filter.atTop) ↔
  (Filter.Frequently (fun n => f n = p) Filter.atTop ∧
    ∀ q : Fin 3, p < q → ¬ Filter.Frequently (fun n => f n = q) Filter.atTop) := by
  change maxInf1385 (pad1385 L r f) p ↔ maxInf1385 f p
  have heq (q : Fin 3) (hq : q ≠ 0) :
      Filter.Frequently (fun n => pad1385 L r f n = q) Filter.atTop ↔
      Filter.Frequently (fun n => f n = q) Filter.atTop := by
    exact prioritized_borel_padding_offset_nonzero_frequently L r hr f q hq
  by_cases hp : p = 0
  · subst p
    constructor
    · rintro ⟨_, h⟩
      have h' : ∀ q : Fin 3, 0 < q → ¬ Filter.Frequently (fun n => f n = q) Filter.atTop := by
        intro q hq hf
        have hne : q ≠ 0 := ne_of_gt hq
        exact h q hq ((heq q hne).mpr hf)
      exact ⟨freqZero1385 f h', h'⟩
    · rintro ⟨_, h⟩
      have h' : ∀ q : Fin 3, 0 < q → ¬ Filter.Frequently (fun n => pad1385 L r f n = q) Filter.atTop := by
        intro q hq hf
        have hne : q ≠ 0 := ne_of_gt hq
        exact h q hq ((heq q hne).mp hf)
      exact ⟨freqZero1385 (pad1385 L r f) h', h'⟩
  · constructor
    · rintro ⟨hf, h⟩
      refine ⟨(heq p hp).mp hf, ?_⟩
      intro q hq hfreq
      have hne : q ≠ 0 := by
        intro hz
        subst q
        exact (not_lt_of_ge (Fin.zero_le p)) hq
      exact h q hq ((heq q hne).mpr hfreq)
    · rintro ⟨hf, h⟩
      refine ⟨(heq p hp).mpr hf, ?_⟩
      intro q hq hfreq
      have hne : q ≠ 0 := by
        intro hz
        subst q
        exact (not_lt_of_ge (Fin.zero_le p)) hq
      exact h q hq ((heq q hne).mp hfreq)
