import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# wild_closed_cut_of_additive_translation

Topic: graphs   Node: 522ca9ddb615

Provenance: helper lemma. OP-306 / IN-338 general-route helpers for the strict prescribed-coloring conjecture in arXiv:2610.22142, Sections3.3.2 and6. Structural analysis of binary factorizations and exact finite averaging in experiments8399,8400,8402,8414. These are conditional certificate or method-diagnostic lemmas, not a new wild-number bound or research advance.

Let a proper complete-graph edge coloring have an injective labeling of its vertices and colors in an exponent-two commutative group, with each edge color label equal to the sum of its endpoint labels. If the labels of a vertex set are stable under translation by one color label, that vertex set is closed under edges of that color.
-/

open Finset
set_option maxHeartbeats 2500000

theorem wild_closed_cut_of_additive_translation
    {G : Type*} [AddCommGroup G] [DecidableEq G] {n : ℕ}
    (h2 : ∀ a : G, a + a = 0)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n))
    (lab : Fin n → G) (hinj : Function.Injective lab)
    (hcol : ∀ u v (h : u ≠ v),
      lab (c ⟨s(u,v), wild_kn_mem h⟩) = lab u + lab v)
    (i : Fin n) (U : Finset (Fin n))
    (htrans : ∀ u ∈ U, lab u + lab i ∈ U.image lab) :
    w279_closed c i U := by
  intro u hu v huv hc
  have hv : lab v = lab u + lab i := by
    calc
      _ = (lab u + lab u) + lab v := by rw [h2, zero_add]
      _ = lab u + (lab u + lab v) := by abel
      _ = lab u + lab i := by rw [← hcol u v huv, hc]
  obtain ⟨w, hw, hweq⟩ := mem_image.mp (htrans u hu)
  have : w = v := hinj (hweq.trans hv.symm)
  simpa only [this] using hw
