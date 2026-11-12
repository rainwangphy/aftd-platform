import AFTD.Prelude

/-!
# hellinger_mutual_information

Topic: information   Node: 15d2cbfc2bda

Provenance: formalization of a published result. Source: scout/2610-21231-on-the-subadditivity-of-mutual-f-information.md:94

For finite types U and V, the Hellinger mutual information of a joint distribution p on U × V is defined as ∑ u, ∑ v, (Real.sqrt (p u v) - Real.sqrt ((∑ v', p u v') * (∑ u', p u' v)))^2, the squared Hellinger distance between p and the product of its marginals.
-/

/-- The Hellinger mutual information of a joint distribution on finite sets. -/
noncomputable def hellinger_mutual_information {U V : Type*} [Fintype U] [Fintype V]
    (p : U → V → ℝ) : ℝ := ∑ u, ∑ v, (Real.sqrt (p u v) - Real.sqrt ((∑ v', p u v') * (∑ u', p u' v))) ^ 2
