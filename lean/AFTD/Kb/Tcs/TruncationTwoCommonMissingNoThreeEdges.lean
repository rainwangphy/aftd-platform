import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationLocalStatesStrongColoringIff
import AFTD.Kb.Tcs.TruncationExposedPair
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring

/-!
# truncation_two_common_missing_no_three_edges

Topic: graphs   Node: 4c13acaed5e7

Provenance: helper lemma. OP-874: necessary two-color local port-cover bound motivated by experiment 38417.

In a strong six-color truncation coloring represented by local states, a vertex and three distinct incident neighbors cannot all miss the same two distinct external colors.
-/

set_option maxHeartbeats 1000000

theorem truncation_two_common_missing_no_three_edges {V E Ω : Type*}
    [Fintype Ω] (hΩ : Fintype.card Ω = 6)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hcubic : ∀ v, Set.ncard {e | v ∈ ends e} = 3)
    (c h : V → E → Ω)
    (hc : ∀ v e f, v ∈ ends e → v ∈ ends f → c v e = c v f → e = f)
    (hh : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e = f)
    (hch : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ c v f)
    (hs : truncation_local_states_define_strong_coloring ends c h)
    (v w₁ w₂ w₃ : V) (e₁ e₂ e₃ : E) (a b : Ω) (hab : a ≠ b)
    (he₁ : ends e₁ = s(v,w₁)) (he₂ : ends e₂ = s(v,w₂))
    (he₃ : ends e₃ = s(v,w₃))
    (hne₁₂ : e₁ ≠ e₂) (hne₁₃ : e₁ ≠ e₃) (hne₂₃ : e₂ ≠ e₃)
    (hva : ∀ f, v ∈ ends f → c v f ≠ a)
    (hvb : ∀ f, v ∈ ends f → c v f ≠ b)
    (hw₁a : ∀ f, w₁ ∈ ends f → c w₁ f ≠ a)
    (hw₁b : ∀ f, w₁ ∈ ends f → c w₁ f ≠ b)
    (hw₂a : ∀ f, w₂ ∈ ends f → c w₂ f ≠ a)
    (hw₂b : ∀ f, w₂ ∈ ends f → c w₂ f ≠ b)
    (hw₃a : ∀ f, w₃ ∈ ends f → c w₃ f ≠ a)
    (hw₃b : ∀ f, w₃ ∈ ends f → c w₃ f ≠ b) : False := by
  classical
  have compat := (truncation_local_states_strong_coloring_iff
    hΩ ends hloop hcubic c h hc hh hch).1 hs
  have cover (e : E) (w : V) (z : Ω) (he : ends e = s(v,w))
      (hvz : ∀ f, v ∈ ends f → c v f ≠ z)
      (hwz : ∀ f, w ∈ ends f → c w f ≠ z) :
      h v e = z ∨ h w e = z := by
    by_contra hn
    push_neg at hn
    have hvP : z ∈ truncation_exposed_pair ends c h v e :=
      ⟨hvz, fun heq => hn.1 heq.symm⟩
    have hwP : z ∈ truncation_exposed_pair ends c h w e :=
      ⟨hwz, fun heq => hn.2 heq.symm⟩
    exact Set.disjoint_left.mp (compat e v w he).2 hvP hwP
  have force (e : E) (w : V) (he : ends e = s(v,w))
      (hwa : ∀ f, w ∈ ends f → c w f ≠ a)
      (hwb : ∀ f, w ∈ ends f → c w f ≠ b) :
      h v e = a ∨ h v e = b := by
    rcases cover e w a he hva hwa with hv | hw
    · exact Or.inl hv
    · rcases cover e w b he hvb hwb with hv | hw'
      · exact Or.inr hv
      · exact False.elim (hab (hw.symm.trans hw'))
  have h₁ := force e₁ w₁ he₁ hw₁a hw₁b
  have h₂ := force e₂ w₂ he₂ hw₂a hw₂b
  have h₃ := force e₃ w₃ he₃ hw₃a hw₃b
  have hv₁ : v ∈ ends e₁ := by rw [he₁]; simp
  have hv₂ : v ∈ ends e₂ := by rw [he₂]; simp
  have hv₃ : v ∈ ends e₃ := by rw [he₃]; simp
  have h₁₂ : h v e₁ ≠ h v e₂ := fun eq => hne₁₂ (hh v e₁ e₂ hv₁ hv₂ eq)
  have h₁₃ : h v e₁ ≠ h v e₃ := fun eq => hne₁₃ (hh v e₁ e₃ hv₁ hv₃ eq)
  have h₂₃ : h v e₂ ≠ h v e₃ := fun eq => hne₂₃ (hh v e₂ e₃ hv₂ hv₃ eq)
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ <;> simp_all
