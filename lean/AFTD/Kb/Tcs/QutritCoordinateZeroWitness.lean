import AFTD.Prelude

/-!
# qutrit_coordinate_zero_witness

Topic: quantum   Node: dc5e33a355a7

Provenance: helper lemma. OP-2299 coordinate product-zero local-jet analysis, exact computation 41027; shift-orbit structure is standard, see https://arxiv.org/abs/quant-ph/0606083.

The general Hermitian Bell-diagonal qutrit operator with product expectation zero at the coordinate product |0,0>, represented by its three circulant shift blocks.
-/

noncomputable def qutrit_coordinate_zero_witness
    (a b : ℝ) (t u v : ℂ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := Matrix.of fun p q =>
    if p.2 - p.1 ≠ q.2 - q.1 then 0 else
    let k := p.2 - p.1
    let d : ℂ := if k = 0 then 0 else if k = 1 then a else b
    let z : ℂ := if k = 0 then t else if k = 1 then u else v
    if p.1 = q.1 then d else if q.1 = p.1 + 1 then z else star z
