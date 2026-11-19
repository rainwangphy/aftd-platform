import AFTD.Prelude

/-!
# overlapping_five_windows_force_middle_pair

Topic: graphs   Node: db64f78dac33

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign; the concrete instance is independently checked in experiments 33309, 33310, 33320, 33321 and 33322.

If each of two overlapping five-element sets contains the element excluded by the other and those excluded elements avoid their common outside positions, the two middle elements form exactly the excluded pair.
-/

theorem overlapping_five_windows_force_middle_pair
    {α : Type*} [DecidableEq α] (a b c d e f : α)
    (hea : e ≠ a) (hed : e ≠ d) (hef : e ≠ f)
    (hfa : f ≠ a) (hfd : f ≠ d)
    (he : e ∈ ({f, a, b, c, d} : Finset α))
    (hf : f ∈ ({a, b, c, d, e} : Finset α)) :
    ({b, c} : Finset α) = {e, f} := by
  have he' : e = b ∨ e = c := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    aesop
  have hf' : f = b ∨ f = c := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    aesop
  rcases he' with hb | hc <;> rcases hf' with hb' | hc' <;>
    subst_vars <;> simp_all [Finset.pair_comm]
