import AFTD.Prelude
import AFTD.Kb.Tcs.YoungDiagramSameLenRowsBelow

/-!
# block_latin_filling

Topic: combinatorics   Node: c795b85f6339

Provenance: formalization of a published result. Source: arXiv:2610.29291 Theorem 3.4 proof

The filling assigning to cell $(i, j)$ in row $i$ the value $(\lambda_i - w \cdot (j/w + 1)) + 1 + ((t_i + (j \bmod w)) \bmod w)$, where $t_i$ is the number of rows below $i$ of the same length.
-/

/-- The explicit block Latin filling function for cell (i, j) with block width w. -/
def block_latin_filling (μ : YoungDiagram) (w : ℕ) (i j : ℕ) : ℕ := (μ.rowLen i - w * (j / w + 1)) + 1 + ((young_diagram_same_len_rows_below μ i + (j % w)) % w)
