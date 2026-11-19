import AFTD.Prelude

/-!
# simple_graph_um_selector_extension

Topic: graphs   Node: 13f28277b5ab

Provenance: formalization of a published result. Source: arXiv:2611.23478, Lemma 5

Given a type V, a subset S : Set V, natural numbers p and q, a function φ : S → Fin p, a function ψ : Sᶜ → Fin q, and an element v : V, simple_graph_um_selector_extension S φ ψ v is the element of Fin (q + p) defined by Fin.natAdd q (φ ⟨v, h⟩) if v ∈ S, and Fin.castAdd p (ψ ⟨v, h⟩) if v ∉ S.
-/

/-- Extension of a colouring ψ of Sᶜ by a selector colouring φ on S into a colouring of V using q + p colours. -/
noncomputable def simple_graph_um_selector_extension {V : Type*} (S : Set V) {p q : ℕ}
    (φ : ↥S → Fin p) (ψ : ↥(Sᶜ) → Fin q) (v : V) : Fin (q + p) := by
  classical
  exact if h : v ∈ S then
    Fin.natAdd q (φ ⟨v, h⟩)
  else
    Fin.castAdd p (ψ ⟨v, h⟩)
