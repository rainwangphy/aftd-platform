import AFTD.Prelude

/-!
# graphon_hom_density

Topic: graphs   Node: 9fe15272e0cc

Provenance: formalization of a published result. Source: arXiv:2611.17885 Section 1

The homomorphism density t(H, W) of a finite simple graph H in a graphon W is the integral over [0, 1]^(V(H)) of the product of W(x_u, x_v) over all edges uv of H.
-/

/-- The homomorphism density t(H, W) of a finite simple graph H in a graphon W. -/
noncomputable def graphon_hom_density {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [Fintype H.edgeSet] (W : ℝ → ℝ → ℝ) : ℝ := ∫ x in Set.pi Set.univ (fun _ : V => Set.Icc (0 : ℝ) 1),
    ∏ e ∈ H.edgeFinset, W (x (Quot.out e).1) (x (Quot.out e).2)
