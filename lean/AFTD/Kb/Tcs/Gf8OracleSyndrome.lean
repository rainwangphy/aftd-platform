import AFTD.Prelude
import AFTD.Kb.Tcs.Gf8MultCoeff

/-!
# gf8_oracle_syndrome

Topic: quantum   Node: 979896773ed6

Provenance: formalization of a published result. Source: Exact T-counts of Toffoli Layers from an Isotropy Bound, arXiv:2610.01024, Proposition 55 and Fact 21 (the GF(8) multiplication phase oracle and its syndrome)

The syndrome s_A of the GF(8) multiplication phase oracle U_3 |x, y, z> = (-1)^{z . (x * y)} |x, y, z> on nine qubits: s_A = 1 iff A = {x_q, y_r, z_l} (qubit q, qubit 3 + r, qubit 6 + l) and bit l of alpha^q * alpha^r in GF(8) = F_2[alpha]/(alpha^3 + alpha + 1) is 1; s_A = 0 for every other subset A (the oracle is pure-cubic). By the moment form of the Amy-Mosca correspondence, the T-count of U_3 is the least size of a set of nonzero parities whose order-1, 2, 3 moments equal this syndrome.
-/

/-- The order-at-most-three syndrome of the GF(8) multiplication phase oracle on nine qubits (qubits 0-2 hold x, 3-5 hold y, 6-8 hold z, polynomial basis with alpha^3 = alpha + 1): 1 exactly on the triples {x_q, y_r, z_l} for which bit l of alpha^q * alpha^r is 1, and 0 on every other set. -/
def gf8_oracle_syndrome (A : Finset (Fin 9)) : ZMod 2 :=
  if ∃ q r l : Fin 3, gf8_mult_coeff q r l = 1 ∧
      A = {⟨q.val, by omega⟩, ⟨3 + r.val, by omega⟩, ⟨6 + l.val, by omega⟩} then 1 else 0
