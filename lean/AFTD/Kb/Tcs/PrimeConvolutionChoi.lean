import AFTD.Prelude

/-!
# prime_convolution_choi

Topic: quantum   Node: 2d31fc56000a

Provenance: formalization of a published result. Source: OP-2466 (proposed here; it builds on the qutrit convolution channels of arXiv:2609.16200, whose Theorem 8 gives the exact PPT and entanglement-breaking threshold 2/5 on a balanced two-level qutrit slice, and on arXiv:2611.09594, which shows PPT and entanglement breaking differ for another convolution environment). The Choi matrix of the convolution channel, written out from the unitary U_r: the standard Choi matrix, normalised by 1/d.

With d : ℕ, r : ZMod d and σ : Matrix (Fin d) (Fin d) ℂ (no hypotheses), returns the complex matrix indexed by Fin d × Fin d whose entry at row (a, b) and column (a', b') equals (1/d) times the sum over j, l in Fin d of σ j l restricted to the pairs with b = r·a + j, b' = r·a' + l and a + j = a' + l, all three equations read in ZMod d (elements of Fin d cast to ZMod d through their natural-number values). This is the normalised Choi matrix J = (1/d) Σ_{a,a'} |a⟩⟨a'| ⊗ N(|a⟩⟨a'|) of the channel N(ρ) = Tr_2[U_r (ρ ⊗ σ) U_r†] with U_r|i,j⟩ = |r·i + j, i + j⟩ over ZMod d: the first index is the reference system, the second the channel output.
-/

/-- The normalised Choi matrix of the convolution channel `ρ ↦ Tr₂[U_r (ρ ⊗ σ) U_r†]`, `U_r|i,j⟩ = |r i + j, i + j⟩` over `ZMod d`. -/
noncomputable def prime_convolution_choi (d : ℕ) (r : ZMod d) (σ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun x y => (1 / (d : ℂ)) * ∑ j : Fin d, ∑ l : Fin d,
    if ((x.2 : ℕ) : ZMod d) = r * ((x.1 : ℕ) : ZMod d) + ((j : ℕ) : ZMod d) ∧
        ((y.2 : ℕ) : ZMod d) = r * ((y.1 : ℕ) : ZMod d) + ((l : ℕ) : ZMod d) ∧
        ((x.1 : ℕ) : ZMod d) + ((j : ℕ) : ZMod d) = ((y.1 : ℕ) : ZMod d) + ((l : ℕ) : ZMod d)
    then σ j l else 0
