import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaElementaryLexicalMeet
import AFTD.Kb.Tcs.AlphaElementaryCellStep
import AFTD.Kb.Tcs.AlphaLexicalMeet
import AFTD.Kb.Tcs.AlphaIsLexical

/-!
# alpha_prime_elementary_meet_nondvd

Topic: combinatorics   Node: 98ec8bf8f522

Provenance: helper lemma. Arithmetic helper for the published prime-degree lexical adjacency criterion, arXiv:0810.5205v2, Theorem 3.1 and Corollary 3.3. The existing elementary-meet theorem gives proper degree; primality excludes divisibility. This does not prove the structural adjacency criterion and is not a research advance.

For a lexical elementary negative-cell step of prime degree, the meet degree cannot divide the ambient prime degree.
-/

theorem alpha_prime_elementary_meet_nondvd
    (p : ℕ) (hp : p.Prime) (a b : List ℕ) (i : ℕ)
    (ha : alpha_is_lexical a) (hb : alpha_is_lexical b)
    (hsa : a.sum + 1 = p) (hi : i % 2 = 1)
    (hstep : alpha_elementary_cell_step a b i) :
    ¬ ((alpha_lexical_meet a b).sum + 1) ∣ p := by
  obtain ⟨_, hpos, hlt⟩ := alpha_elementary_lexical_meet a b i ha hb hi hstep
  rw [hsa] at hlt
  intro hd
  rcases hp.eq_one_or_self_of_dvd _ hd with he | he <;> omega
