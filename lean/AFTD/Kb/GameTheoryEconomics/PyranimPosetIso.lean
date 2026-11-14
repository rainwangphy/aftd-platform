import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PyranimChipSub

/-!
# pyranim_poset_iso

Topic: combinatorial_games   Node: 47ad866ff1e3

Provenance: helper lemma. step towards pyranim_game_iso_iff_graph_iso

Positions X and Y are isomorphic as chip posets if there is a bijection of their chips preserving the containment order in both directions.
-/

/-- Order isomorphism of the chip posets (X, containment) and (Y, containment): a bijection reflecting pyranim_chip_sub both ways. -/
def pyranim_poset_iso (X Y : Finset (ℕ × ℕ)) : Prop := ∃ e : {c : ℕ × ℕ // c ∈ X} ≃ {d : ℕ × ℕ // d ∈ Y},
    ∀ a b : {c : ℕ × ℕ // c ∈ X},
      (pyranim_chip_sub a.1 b.1 ↔ pyranim_chip_sub (e a).1 (e b).1)
