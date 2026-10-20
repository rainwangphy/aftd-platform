import AFTD.Prelude

/-!
# simple_graph_is_multi_radio_labeling

Topic: graphs   Node: 55b327d6a651

Provenance: formalization of a published result. Source: arXiv:2610.25863 (On Multi-label radio Labelings of Graphs), Sec. 1 (definition of (m,k)-radio labelings)

An (m,k)-radio labeling of G: each vertex gets a set of m nonnegative integer labels, and for any (possibly equal) vertices x, y and labels a of x, b of y with (x, a) ≠ (y, b), |a - b| >= k + 1 - d(x, y).
-/

/-- An (m,k)-radio labeling of G: each vertex gets a set of m nonnegative integer labels, and for any (possibly equal) vertices x, y and labels a of x, b of y with (x, a) ≠ (y, b), |a - b| >= k + 1 - d(x, y). -/
def simple_graph_is_multi_radio_labeling {V : Type*} (G : SimpleGraph V) (m k : ℕ)
    (f : V → Finset ℕ) : Prop :=
  (∀ v, (f v).card = m) ∧ ∀ x y, ∀ a ∈ f x, ∀ b ∈ f y, (x, a) ≠ (y, b) →
    (k + 1 : ℤ) - G.dist x y ≤ |(a : ℤ) - b|
