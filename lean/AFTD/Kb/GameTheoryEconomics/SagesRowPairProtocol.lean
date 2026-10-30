import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SagesRowOtherThan
import AFTD.Kb.GameTheoryEconomics.RowLocalView

/-!
# sages_row_pair_protocol

Topic: combinatorial_games   Node: 67333bf55bb1

Provenance: helper lemma. step towards sages_row_upper_bound_binomial

Every sage in a row announces the unordered pair consisting of themselves together with their right neighbour; the rightmost sage, who has no right neighbour, announces the pair with their left neighbour.
-/

/-- Every sage announces the pair consisting of themselves and their right neighbour, or their left neighbour if they have no right neighbour (the rightmost sage), falling back to a canonical partner on neighbourless views. -/
def sages_row_pair_protocol {S : ℕ} (hS : 2 ≤ S) (v : RowLocalView (Fin S)) : {s : Finset (Fin S) // s.card = 2} := let x := v.1
   let y := match v.2.2, v.2.1 with
     | some y, _ => y
     | none, some y => y
     | none, none => sages_row_other_than hS x
   if hy : y = x then
     ⟨{x, sages_row_other_than hS x}, by
       apply Finset.card_pair
       intro h
       have hv : (sages_row_other_than hS x).val = x.val := congrArg Fin.val h.symm
       simp only [sages_row_other_than] at hv
       split_ifs at hv with h0 <;> omega⟩
   else
     ⟨{x, y}, Finset.card_pair (Ne.symm hy)⟩
