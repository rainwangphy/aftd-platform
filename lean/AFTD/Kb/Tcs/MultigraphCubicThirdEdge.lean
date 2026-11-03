import AFTD.Prelude

/-!
# multigraph_cubic_third_edge

Topic: graphs   Node: 14f5c1d9fceb

Provenance: helper lemma. helper for truncation_local_states_strong_coloring_iff (arXiv:2610.41950 Lemma 2.1, PR-677)

In a multigraph (ends : E → Sym2 V) where every vertex lies on exactly three edges, two distinct edges e ≠ f at v leave a third edge g at v, distinct from both, and every edge at v is e, f or g.
-/

theorem multigraph_cubic_third_edge {V E : Type*} {ends : E → Sym2 V}
    (hcubic : ∀ v, Set.ncard {e | v ∈ ends e} = 3) {v : V} {e f : E}
    (he : v ∈ ends e) (hf : v ∈ ends f) (hef : e ≠ f) :
    ∃ g, v ∈ ends g ∧ g ≠ e ∧ g ≠ f ∧ ∀ k, v ∈ ends k → k = e ∨ k = f ∨ k = g := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := Set.ncard_eq_three.mp (hcubic v)
  have mem : ∀ k, v ∈ ends k ↔ k = x ∨ k = y ∨ k = z := fun k => by
    have := Set.ext_iff.mp hs k
    simpa using this
  have hx := (mem x).2 (Or.inl rfl)
  have hy := (mem y).2 (Or.inr (Or.inl rfl))
  have hz := (mem z).2 (Or.inr (Or.inr rfl))
  rcases (mem e).1 he with rfl | rfl | rfl <;> rcases (mem f).1 hf with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hef
    | (refine ⟨_, hx, ?_, ?_, ?_⟩ <;>
        first
        | (intro h; subst h; contradiction)
        | (intro k hk; rcases (mem k).1 hk with h | h | h <;> simp [h]))
    | (refine ⟨_, hy, ?_, ?_, ?_⟩ <;>
        first
        | (intro h; subst h; contradiction)
        | (intro k hk; rcases (mem k).1 hk with h | h | h <;> simp [h]))
    | (refine ⟨_, hz, ?_, ?_, ?_⟩ <;>
        first
        | (intro h; subst h; contradiction)
        | (intro k hk; rcases (mem k).1 hk with h | h | h <;> simp [h]))
