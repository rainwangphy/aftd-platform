import AFTD.Prelude
import AFTD.Kb.Tcs.CodewordSupp

/-!
# card_codeword_supp

Topic: information   Node: ecb127d52be9

Provenance: helper lemma. arXiv:2610.30613, Section 2

The cardinality of the support $\mathrm{codeword\_supp}(x)$ of a codeword $x : \mathrm{Fin}\, n \to \alpha$ equals its Hamming weight $\mathrm{hammingNorm}(x)$.
-/

/-- The cardinality of the support of a codeword is its Hamming weight (hammingNorm). -/
theorem card_codeword_supp {n : ℕ} {α : Type*} [DecidableEq α] [Zero α] (x : Fin n → α) :
    (codeword_supp x).card = hammingNorm x := rfl
