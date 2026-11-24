import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationLocalStatesStrongColoringIff
import AFTD.Kb.Tcs.TruncationExposedPair
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring

/-!
# truncation_no_three_common_missing_colors

Topic: graphs   Node: aa69b188891a

Provenance: helper lemma. OP-874: local port-cover obstruction, experiments 38442–38443.

For any edge of a loopless cubic multigraph, the two endpoint palettes of a strong six-color truncation coloring cannot have three distinct missing external colors in common.
-/

set_option maxHeartbeats 1000000

theorem truncation_no_three_common_missing_colors {V E Ω : Type*}
    [Fintype Ω] (hΩ : Fintype.card Ω = 6)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hcubic : ∀ v, Set.ncard {e | v ∈ ends e} = 3)
    (c h : V → E → Ω)
    (hc : ∀ v e f, v ∈ ends e → v ∈ ends f → c v e = c v f → e = f)
    (hh : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e = f)
    (hch : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ c v f)
    (hs : truncation_local_states_define_strong_coloring ends c h)
    (u v : V) (e : E) (he : ends e = s(u,v)) (a b d : Ω)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hua : ∀ f, u ∈ ends f → c u f ≠ a)
    (hub : ∀ f, u ∈ ends f → c u f ≠ b)
    (hud : ∀ f, u ∈ ends f → c u f ≠ d)
    (hva : ∀ f, v ∈ ends f → c v f ≠ a)
    (hvb : ∀ f, v ∈ ends f → c v f ≠ b)
    (hvd : ∀ f, v ∈ ends f → c v f ≠ d) : False := by
  classical
  have compat := (truncation_local_states_strong_coloring_iff
    hΩ ends hloop hcubic c h hc hh hch).1 hs
  have cover (z : Ω) (huz : ∀ f, u ∈ ends f → c u f ≠ z)
      (hvz : ∀ f, v ∈ ends f → c v f ≠ z) :
      h u e = z ∨ h v e = z := by
    by_contra hn
    push_neg at hn
    have huP : z ∈ truncation_exposed_pair ends c h u e :=
      ⟨huz, fun heq => hn.1 heq.symm⟩
    have hvP : z ∈ truncation_exposed_pair ends c h v e :=
      ⟨hvz, fun heq => hn.2 heq.symm⟩
    exact Set.disjoint_left.mp (compat e u v he).2 huP hvP
  have ha := cover a hua hva
  have hb := cover b hub hvb
  have hd := cover d hud hvd
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases hd with hd | hd <;> simp_all
