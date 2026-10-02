import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DeferredAcceptance
import AFTD.Kb.GameTheoryEconomics.WomanWeaklyPrefers
import AFTD.Kb.GameTheoryEconomics.WomanStrictlyPrefers

/-!
# da_woman_k_known_safely_manipulable

Topic: matching_markets   Node: 21e57f8c55d2

In men-proposing deferred acceptance with nm men, nw women and complete rankings (no truncation), some woman who knows the rankings of k other agents has a misreport that is safe (never worse, whatever the unknown agents rank) and profitable (strictly better for some rankings of the unknown agents); Hartman-Segal-Halevi-Tao Def. 3.1.
-/

/-- Hartman, Segal-Halevi and Tao (arXiv:2502.18805, Def. 3.1), for men-proposing deferred acceptance in a market of `nm` men and `nw` women with complete rankings (no truncation), and a woman as the manipulator: some woman `w0`, knowing the rankings of `k` other agents (men `Km`, women `Kw`), has a report `P` instead of her true ranking `T` that is safe (never worse, whatever the unknown agents rank) and profitable (strictly better for some rankings of the unknown agents). -/
def da_woman_k_known_safely_manipulable (nm nw k : ℕ) : Prop :=
  ∃ (w0 : Fin nw) (Km : Finset (Fin nm)) (Kw : Finset (Fin nw)), w0 ∉ Kw ∧ Km.card + Kw.card = k ∧
  ∃ (km : Fin nm → Fin nw → Fin nw) (kw : Fin nw → Fin nm → Fin nm) (T P : Fin nm → Fin nm),
    (∀ m ∈ Km, Function.Injective (km m)) ∧ (∀ w ∈ Kw, Function.Injective (kw w)) ∧
    Function.Injective T ∧ Function.Injective P ∧
    (∀ (rm : Fin nm → Fin nw → Fin nw) (rw : Fin nw → Fin nm → Fin nm),
      (∀ m, Function.Injective (rm m)) → (∀ w, Function.Injective (rw w)) →
      (∀ m ∈ Km, rm m = km m) → (∀ w ∈ Kw, rw w = kw w) →
      woman_weakly_prefers T (deferred_acceptance rm (Function.update rw w0 P) w0)
        (deferred_acceptance rm (Function.update rw w0 T) w0)) ∧
    (∃ (rm : Fin nm → Fin nw → Fin nw) (rw : Fin nw → Fin nm → Fin nm),
      (∀ m, Function.Injective (rm m)) ∧ (∀ w, Function.Injective (rw w)) ∧
      (∀ m ∈ Km, rm m = km m) ∧ (∀ w ∈ Kw, rw w = kw w) ∧
      woman_strictly_prefers T (deferred_acceptance rm (Function.update rw w0 P) w0)
        (deferred_acceptance rm (Function.update rw w0 T) w0))
