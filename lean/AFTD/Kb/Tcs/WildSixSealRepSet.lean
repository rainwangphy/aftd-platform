import AFTD.Prelude
import AFTD.Kb.Tcs.WildSixSealPartner

/-!
# wild_six_seal_rep_set

Topic: graphs   Node: 85bd98160739

Provenance: helper lemma. step towards wild_normalized_array_disjoint_six_seal_mass_bound

The orbit-representative set of the (fixed-point-free) i-partner involution on W = univ \ (S ∪ {i} ∪ S.image (partner i)): one representative x (with x < partner i x) per 2-element orbit.
-/

/-- Representatives (one per 2-orbit) of the i-partner involution outside S, i and the partners of S. -/
noncomputable def wild_six_seal_rep_set {N : ℕ} (A : Fin N → Fin N → Fin N)
    (hinj : ∀ x, Function.Injective (A x)) (S : Finset (Fin N)) (i : Fin N) : Finset (Fin N) := (Finset.univ \ (S ∪ {i} ∪ S.image (wild_six_seal_partner A hinj i))).filter
    (fun x => x < wild_six_seal_partner A hinj i x)
