import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_full_prune_fractional_counterexample

Topic: combinatorics   Node: 69cb3b9a77e4

Provenance: helper lemma. Uniform OP-205 / RT-1 route audit following arXiv:2610.15635. Experiments7281/7291 recover a rational feasible mixture for the new full-prune density objective. The statement refutes only a sufficient linear-relaxation route and claims no graph covering value or research advance.

Seventeen genuine tight radius-64 dyadic rooted profiles with positive integer multiplicities totaling1192 have expected size7, exact weighted dyadic pair counts1192 at every rank, and ordinary pair counts at least1192 at every distance1 through63, but every profile has a missing offset in its compressed outer quarters. Thus no positive full-pruned-class density follows from the independent single-class expectation constraints alone. This is an auxiliary fractional obstruction and is not an actual integer class model or a counterexample to OP-205.
-/

open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cycle_power_dyadic_full_prune_fractional_counterexample :
    ∃ (b : Fin 17 → ℕ → Bool) (w : Fin 17 → ℕ),
      (∑ i, w i) = 1192 ∧
      (∀ i, 0 < w i) ∧
      (∀ i, b i 0 = true ∧ b i 63 = true) ∧
      (∀ i, cycle_power_dyadic_class_weight 6 (b i) =
        (Finset.range 64).sum (fun a => (b i a).toNat)) ∧
      (∑ i, w i * (Finset.range 64).sum (fun a => (b i a).toNat)) = 8344 ∧
      (∀ j : Fin 6, (∑ i, w i * (Finset.range (2^(j : ℕ))).sum
        (fun a => (b i a && b i (a+64-2^(j : ℕ))).toNat)) = 1192) ∧
      (∀ d : Fin 63, 1192 ≤ ∑ i, w i * (Finset.range (64-((d : ℕ)+1))).sum
        (fun a => (b i a && b i (a+((d : ℕ)+1))).toNat)) ∧
      (∀ i, ∃ a : Fin 32, cycle_power_dyadic_b_lift 4 (b i) (a : ℕ) = false) := by
  let masks : Fin 17 → ℕ := ![9223372036854775809, 13835058055282163715, 17293822569102704655, 18374686479671623935, 18442240474082185215, 18446462598732873727, 18446532961034551295, 18446480174812684287, 18410574545644814079, 18446726491188231167, 18444281149942726655, 18446714404645895679, 18446475740526460927, 18442203211885707263, 18442239243696734207, 18437487261123149823, 18446739786778541823]
  let b : Fin 17 → ℕ → Bool := fun i a => (masks i).testBit a
  let w : Fin 17 → ℕ := ![596, 298, 149, 69, 1, 12, 1, 11, 1, 8, 1, 8, 11, 9, 6, 4, 7]
  refine ⟨b, w, ?_⟩
  decide
