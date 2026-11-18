import AFTD.Prelude
import AFTD.Kb.Tcs.BoxPattern

/-!
# layer_mono

Topic: combinatorics   Node: 5ed9b7faf029

Provenance: helper lemma. step towards grid_box_free_max_five_seven

For a $2$-colouring $f$ of $[a]\times[b]\times[c]$ and a layer index $z$, $\mathrm{layer\_mono}(f,z)$ is the finite set of coloured rectangle patterns $\{x_1,x_2\}\times\{y_1,y_2\}$ that are monochromatic with colour $\mathrm{col}$ inside layer $z$.
-/

/-- The set of monochromatic coloured rectangles occurring in a single layer of a 3-D colouring. -/
def layer_mono {a b c : ℕ} (f : Fin a → Fin b → Fin c → Bool) (z : Fin c) : Finset (BoxPattern a b) := Finset.univ.filter (fun p => p.1 < p.2.1 ∧ p.2.2.1 < p.2.2.2.1 ∧
     f p.1 p.2.2.1 z = p.2.2.2.2 ∧ f p.1 p.2.2.2.1 z = p.2.2.2.2 ∧
     f p.2.1 p.2.2.1 z = p.2.2.2.2 ∧ f p.2.1 p.2.2.2.1 z = p.2.2.2.2)
