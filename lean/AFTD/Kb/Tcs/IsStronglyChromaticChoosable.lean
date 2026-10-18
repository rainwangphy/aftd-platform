import AFTD.Prelude

/-!
# IsStronglyChromaticChoosable

Topic: graphs   Node: ac11ecc2d0bb

Provenance: formalization of a published result. Source: arXiv:2610.14241 (Restricting odd antiholes in critical graphs via list coloring), Sec. 2, before Conjecture 9 (definition of strong ℓ-chromatic-choosability)

A graph G is strongly ℓ-chromatic-choosable if χ(G) = ℓ and every (ℓ-1)-assignment L for which G is not L-colorable has all lists equal; equivalently, every (ℓ-1)-assignment whose lists are not all identical admits a proper coloring c with c(v) ∈ L(v). Colours are natural numbers, which loses no generality since the lists are finite.
-/

/-- `G` is strongly `ℓ`-chromatic-choosable: `χ(G) = ℓ`, and every assignment of lists of size `ℓ - 1` (colours in `ℕ`) under which `G` is not list-colourable gives every vertex the same list. -/
def IsStronglyChromaticChoosable {V : Type*} (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  G.chromaticNumber = ℓ ∧
    ∀ L : V → Finset ℕ, (∀ v, (L v).card = ℓ - 1) → (∃ u v, L u ≠ L v) →
      ∃ c : V → ℕ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v
