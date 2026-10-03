import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TemporalSat

/-!
# is_temporal_droop_fjr

Topic: social_choice   Node: 7ae19962678d

Droop-FJR for temporal elections (Phillips, Elkind, Teh, Wąs, arXiv:2505.22513, Def. A.6): for every nonempty group S and set of rounds T there is R ⊆ T of size ⌈(|T|+1)|S|/n⌉ - 1 such that for every outcome o′ some i ∈ S has sat_i(o) ≥ min over j ∈ S of sat_j(o′ restricted to R).
-/

/-- Droop-FJR for temporal elections (Phillips–Elkind–Teh–Wąs, Def. A.6): for every nonempty group `S` and every set of rounds `T` there is `R ⊆ T` with `|R| = ⌈(|T|+1)|S|/n⌉ - 1` such that for every outcome `o'` some `i ∈ S` has `sat_i(o) ≥ min_{j ∈ S} sat_j(o'_R)`. -/
def is_temporal_droop_fjr {n ℓ m : ℕ} (a : Fin n → Fin ℓ → Finset (Fin m))
    (o : Fin ℓ → Fin m) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → ∀ T : Finset (Fin ℓ),
    ∃ R ⊆ T, R.card = ((T.card + 1) * S.card + n - 1) / n - 1 ∧
      ∀ o' : Fin ℓ → Fin m, ∃ i ∈ S, ∃ j ∈ S,
        temporal_sat a j o' R ≤ temporal_sat a i o Finset.univ
