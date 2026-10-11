import AFTD.Prelude

/-!
# finset_contains_trace

Topic: combinatorics   Node: c70a255bc372

Provenance: formalization of a published result. Source: arXiv:2610.08151 (Polynomial-in-r bounds for forbidden traces of uniform hypergraphs), Sec. 1.1 (containing F as a trace; an induced Berge copy). The ground set of H is Fin h; the distinctness of the witnesses H_e is implied by H_e ∩ Y = e and is not stated separately.

A set system F contains the set system H on the ground set {0,…,h−1} as a trace if there is an injection φ of the ground set of H into that of F such that every edge e of H equals A ∩ φ(V(H)) (transported by φ) for some A ∈ F. Distinct edges of H automatically get distinct witnesses A, since A ∩ Y determines e.
-/

/-- `𝓕` contains the set system `𝓗` on `Fin h` as a trace: some embedding `φ` of `Fin h` and, for every edge `e` of `𝓗`, some `A ∈ 𝓕` with `A ∩ φ(Fin h) = φ(e)`. -/
def finset_contains_trace {α : Type*} [DecidableEq α] {h : ℕ}
    (𝓕 : Finset (Finset α)) (𝓗 : Finset (Finset (Fin h))) : Prop :=
  ∃ φ : Fin h ↪ α, ∀ e ∈ 𝓗, ∃ A ∈ 𝓕, A ∩ Finset.univ.map φ = e.map φ
