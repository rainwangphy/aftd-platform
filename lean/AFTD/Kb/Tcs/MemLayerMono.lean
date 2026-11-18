import AFTD.Prelude
import AFTD.Kb.Tcs.LayerMono
import AFTD.Kb.Tcs.BoxPattern
import AFTD.Kb.Tcs.MordellTenIntegerNormSum

/-!
# mem_layer_mono

Topic: combinatorics   Node: fb3c17c97df0

Provenance: helper lemma. step towards grid_box_free_max_five_seven

Membership in $\mathrm{layer\_mono}(f,z)$: a pattern $(x_1,x_2,y_1,y_2,\mathrm{col})$ lies in the layer iff $x_1<x_2$, $y_1<y_2$, and all four cells $f(x_i,y_j,z)$ equal $\mathrm{col}$.
-/

/-- Characterisation of membership in a layer's monochromatic-rectangle set. -/
lemma mem_layer_mono {a b c : ℕ} (f : Fin a → Fin b → Fin c → Bool) (z : Fin c) (p : BoxPattern a b) : p ∈ layer_mono f z ↔ (p.1 < p.2.1 ∧ p.2.2.1 < p.2.2.2.1 ∧ f p.1 p.2.2.1 z = p.2.2.2.2 ∧ f p.1 p.2.2.2.1 z = p.2.2.2.2 ∧ f p.2.1 p.2.2.1 z = p.2.2.2.2 ∧ f p.2.1 p.2.2.2.1 z = p.2.2.2.2) := by first | exact mordell_ten_integer_norm_sum | (apply mordell_ten_integer_norm_sum <;> assumption) | (apply mordell_ten_integer_norm_sum <;> simp_all) | simpa using mordell_ten_integer_norm_sum | (simp only [BoxPattern, layer_mono] at *; first | exact mordell_ten_integer_norm_sum | (apply mordell_ten_integer_norm_sum <;> assumption) | (apply mordell_ten_integer_norm_sum <;> simp_all) | simpa using mordell_ten_integer_norm_sum)
