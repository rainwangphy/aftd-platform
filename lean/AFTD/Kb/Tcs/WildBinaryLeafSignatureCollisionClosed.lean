import AFTD.Prelude
import AFTD.Kb.Tcs.WildTwoLeafSignatureTranslationSeal
import AFTD.Kb.Tcs.WildClosedCutOfAdditiveTranslation
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# wild_binary_leaf_signature_collision_closed

Topic: graphs   Node: ff4a44d9ab48

Provenance: helper lemma. OP-306 / IN-338 general-route helpers for the strict prescribed-coloring conjecture in arXiv:2610.22142, Sections3.3.2 and6. Structural analysis of binary factorizations and exact finite averaging in experiments8399,8400,8402,8414. These are conditional certificate or method-diagnostic lemmas, not a new wild-number bound or research advance.

For a properly colored complete graph whose vertex/color labels bijectively enumerate the nonzero elements of an exponent-two commutative group and whose edge labels add, take two disjoint triples each containing a pair separated by the same e. A collision of their leaf signatures modulo {0,e} forces their six-vertex union to be closed for some color whose missing vertex lies outside that union.
-/

open Finset
set_option maxHeartbeats 2500000

theorem wild_binary_leaf_signature_collision_closed
    {G : Type*} [AddCommGroup G] [DecidableEq G] {n : ℕ}
    (h2 : ∀ a : G, a + a = 0)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n))
    (lab : Fin n → G) (hinj : Function.Injective lab)
    (hnz : ∀ u, lab u ≠ 0) (hsurj : ∀ g : G, g ≠ 0 → ∃ u, lab u = g)
    (hcol : ∀ u v (h : u ≠ v),
      lab (c ⟨s(u,v), wild_kn_mem h⟩) = lab u + lab v)
    (e : G) (a b z d f w : Fin n)
    (hb : lab b = lab a + e) (hf : lab f = lab d + e)
    (hA : ({a,b,z} : Finset (Fin n)).card = 3)
    (hB : ({d,f,w} : Finset (Fin n)).card = 3)
    (hdis : Disjoint ({a,b,z} : Finset (Fin n)) {d,f,w})
    (hsig : lab a + lab z = lab d + lab w ∨
      lab a + lab z = lab d + lab w + e) :
    let U := ({a,b,z} : Finset (Fin n)) ∪ {d,f,w}
    U.card = 6 ∧ ∃ i : Fin n, i ∉ U ∧ w279_closed c i U := by
  classical
  let A : Finset (Fin n) := {a,b,z}
  let B : Finset (Fin n) := {d,f,w}
  let U := A ∪ B
  have hAI : A.image lab = {lab a, lab a + e, lab z} := by simp [A, hb]
  have hBI : B.image lab = {lab d, lab d + e, lab w} := by simp [B, hf]
  have hcardAI : ({lab a, lab a + e, lab z} : Finset G).card = 3 := by
    rw [← hAI, card_image_of_injective _ hinj]
    exact hA
  have hcardBI : ({lab d, lab d + e, lab w} : Finset G).card = 3 := by
    rw [← hBI, card_image_of_injective _ hinj]
    exact hB
  have hdisI : Disjoint ({lab a, lab a + e, lab z} : Finset G)
      {lab d, lab d + e, lab w} := by
    rw [← hAI, ← hBI]
    apply disjoint_left.mpr
    intro g hgA hgB
    obtain ⟨u, hu, he⟩ := mem_image.mp hgA
    obtain ⟨v, hv, he'⟩ := mem_image.mp hgB
    have huv := hinj (he.trans he'.symm)
    exact disjoint_left.mp hdis hu (huv ▸ hv)
  have hUI : U.image lab = ({lab a, lab a + e, lab z} : Finset G) ∪
      {lab d, lab d + e, lab w} := by
    change (A ∪ B).image lab = _
    rw [image_union, hAI, hBI]
  have hzero : (0 : G) ∉ ({lab a, lab a + e, lab z} : Finset G) ∪
      {lab d, lab d + e, lab w} := by
    rw [← hUI]
    rintro hz
    obtain ⟨v, hv, he⟩ := mem_image.mp hz
    exact hnz v he
  obtain ⟨_, hc, hcU, ht⟩ := wild_two_leaf_signature_translation_seal h2 e
    (lab a) (lab d) (lab z) (lab w) hcardAI hcardBI hdisI hzero hsig
  obtain ⟨i, hi⟩ := hsurj (lab z + lab w) hc
  refine ⟨?_, i, ?_, ?_⟩
  · rw [card_union_of_disjoint hdis, hA, hB]
  · intro hiU
    apply hcU
    rw [← hUI, ← hi]
    exact mem_image.mpr ⟨i, hiU, rfl⟩
  · apply wild_closed_cut_of_additive_translation h2 c lab hinj hcol i U
    intro u hu
    rw [hi, hUI]
    apply ht
    rw [← hUI]
    exact mem_image.mpr ⟨u, hu, rfl⟩
