import AFTD.Prelude
import AFTD.Kb.Optimization.TriangleHomothet
import AFTD.Kb.Optimization.TriangleRegion

/-!
# triangle_homothet_mem_iff_avoid_regions

Topic: convex_analysis   Node: 70b91aab7fda

Provenance: helper lemma. arXiv:2611.08835 Lemma 8 proof, Step 1

For a finite set $P \subset \mathbb{R}^2$ and points $p, q, r \in \mathbb{R}^2$ with $p, q \in P$, $r \in \text{triangle\_homothet}(p, q)$ if and only if for each index $i \in \{0, 1, 2\}$, it is not the case that both $p \in \text{triangle\_region}(P, r, i)$ and $q \in \text{triangle\_region}(P, r, i)$.
-/

/-- Characterization of containment in T(p,q) via avoiding the regions Aᵢ(r). -/
theorem triangle_homothet_mem_iff_avoid_regions (P : Finset (ℝ × ℝ)) (p q r : ℝ × ℝ)
    (hp : p ∈ P) (hq : q ∈ P) :
    r ∈ triangle_homothet p q ↔
      ∀ i : Fin 3, ¬(p ∈ triangle_region P r i ∧ q ∈ triangle_region P r i) := by
  have h_forall (A : Fin 3 → Prop) : (∀ i, A i) ↔ A 0 ∧ A 1 ∧ A 2 := by
    constructor
    · intro h; exact ⟨h 0, h 1, h 2⟩
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i <;> assumption
  rw [h_forall]
  dsimp [triangle_homothet, triangle_region]
  simp only [Finset.mem_filter, hp, hq, true_and]
  rw [← not_lt, lt_min_iff]
  rw [← not_lt, lt_min_iff]
  rw [← not_lt, max_lt_iff]
