import AFTD.Prelude
import AFTD.Kb.Tcs.CslibProbabilityPMFUniformOfFintypeMapEquiv

/-!
# pmf_uniform_group_convolution_eq_uniform

Topic: randomness   Node: e741263165c4

Provenance: formalization of a published result. Source: Shannon (1949), 'Communication Theory of Secrecy Systems', Theorem 6

Let G be a finite nonempty additive commutative group. For any probability mass function p on G, the convolution of p with the uniform distribution PMF.uniformOfFintype G, defined as p.bind (fun m => (PMF.uniformOfFintype G).map (fun k => m + k)), is equal to PMF.uniformOfFintype G.
-/

/-- The convolution of any probability distribution with the uniform distribution on a finite additive group is the uniform distribution. -/
theorem pmf_uniform_group_convolution_eq_uniform {G : Type*} [AddCommGroup G] [Fintype G] [Nonempty G]
    (p : PMF G) :
    p.bind (fun m => (PMF.uniformOfFintype G).map (fun k => m + k)) = PMF.uniformOfFintype G := by
  have h (m : G) : (PMF.uniformOfFintype G).map (fun k => m + k) = PMF.uniformOfFintype G :=
    Cslib.Probability.PMF.uniformOfFintype_map_equiv (Equiv.addLeft m)
  simp_rw [h]
  exact PMF.bind_const p (PMF.uniformOfFintype G)
