import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPosGrundy
import AFTD.Kb.GameTheoryEconomics.ArrowsLegalMove
import AFTD.Kb.GameTheoryEconomics.NatMexSetEqZeroOfNotMem
import AFTD.Kb.GameTheoryEconomics.NatMexSetEqOneOfMem
import AFTD.Kb.GameTheoryEconomics.NatMexSetNeOfMem
import AFTD.Kb.GameTheoryEconomics.ArrowsPosGrundyOptionsFinite
import AFTD.Kb.GameTheoryEconomics.NatMexSet
import AFTD.Kb.GameTheoryEconomics.ArrowsPos

/-!
# arrows_pos_grundy_eq_mod_two_of_class

Topic: combinatorial_games   Node: 191023cf78af

Provenance: helper lemma. Helper for arrows_parity_of_threads_le_two, arXiv:2610.15145 Theorem 10.3 / Corollary 10.4 (the induction in the proof of Theorem 10.3: every option has value (e-1) mod 2 or an option of value e mod 2), done directly on positions of T without the sum decomposition

Strategy lemma for parity in the Game of Arrows: let e be a function on positions that drops by exactly one along every legal move, and S a class of positions such that from every position in S with e >= 1 some legal move stays in S, and every legal move from a position in S lands in S or admits a legal reply back into S. Then every position p in S has fuel-bounded Grundy value e(p) mod 2 at every fuel greater than e(p).
-/

theorem arrows_pos_grundy_eq_mod_two_of_class {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : ArrowsPos V → Prop) (e : ArrowsPos V → ℕ)
    (he : ∀ p q, ArrowsLegalMove G p q → e q + 1 = e p)
    (hex : ∀ p, S p → 1 ≤ e p → ∃ q, ArrowsLegalMove G p q ∧ S q)
    (hcl : ∀ p q, S p → ArrowsLegalMove G p q → S q ∨ ∃ r, ArrowsLegalMove G q r ∧ S r) :
    ∀ fuel p, S p → e p < fuel → arrows_pos_grundy G fuel p = e p % 2 := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    intro p hp hlt
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    have hnot : e p % 2 ∉ { m : ℕ | ∃ q, ArrowsLegalMove G p q ∧ m = arrows_pos_grundy G n q } := by
      rintro ⟨q, hq, hm⟩
      have heq := he p q hq
      rcases hcl p q hp hq with hS | ⟨r, hr, hSr⟩
      · rw [ih n (by omega) q hS (by omega)] at hm; omega
      · have her := he q r hr
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        have hrv : arrows_pos_grundy G n' r = e p % 2 := by
          rw [ih n' (by omega) r hSr (by omega)]; omega
        have hg : arrows_pos_grundy G (n' + 1) q = nat_mex_set
            { m : ℕ | ∃ q', ArrowsLegalMove G q q' ∧ m = arrows_pos_grundy G n' q' } := rfl
        exact nat_mex_set_ne_of_mem (arrows_pos_grundy_options_finite G n' q)
          ⟨r, hr, hrv.symm⟩ (hg ▸ hm.symm)
    show nat_mex_set _ = _
    rcases Nat.mod_two_eq_zero_or_one (e p) with h0 | h1
    · rw [h0] at hnot ⊢; exact nat_mex_set_eq_zero_of_not_mem hnot
    · rw [h1] at hnot ⊢
      obtain ⟨q, hq, hSq⟩ := hex p hp (by omega)
      have heq := he p q hq
      exact nat_mex_set_eq_one_of_mem ⟨q, hq, by rw [ih n (by omega) q hSq (by omega)]; omega⟩ hnot
