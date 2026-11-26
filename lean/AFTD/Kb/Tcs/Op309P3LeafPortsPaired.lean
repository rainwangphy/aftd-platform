import AFTD.Prelude

/-!
# op309_p3_leaf_ports_paired

Topic: graphs   Node: 7e9dc57fc29c

Provenance: helper lemma. OP-309; leaf-port identifications in experiments 41785–41788 and 41806–41807.

The two other edge colors at the leaves of every selected P3 agree as an unordered pair.
-/

def op309_p3_leaf_ports_paired {V α : Type*} [DecidableEq V]
    (G : SimpleGraph V) (R : Finset G.edgeSet) (c : G.edgeSet → α) : Prop := ∀ a b d : V, [a,b,d].Nodup →
  ∀ e ∈ R, ∀ f ∈ R, e.1 = s(a,b) → f.1 = s(b,d) →
    ∃ p₁ p₂ q₁ q₂ : G.edgeSet,
      p₁ ≠ p₂ ∧ q₁ ≠ q₂ ∧ p₁ ≠ e ∧ p₂ ≠ e ∧ q₁ ≠ f ∧ q₂ ≠ f ∧
      a ∈ p₁.1 ∧ a ∈ p₂.1 ∧ d ∈ q₁.1 ∧ d ∈ q₂.1 ∧
      ((c p₁ = c q₁ ∧ c p₂ = c q₂) ∨ (c p₁ = c q₂ ∧ c p₂ = c q₁))
