import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTChromaticPrincipalSpecialization

/-!
# simple_graph_t_chromatic_ps_coloring_count_rev

Topic: graphs   Node: 079d5897572d

Provenance: helper lemma. arXiv:2610.31785 (Principal specializations of the t-chromatic symmetric function), Proposition 3.16: the color-reversal involution of its proof

For a finite simple graph G, natural numbers n, k and j ≤ (n-1)|V|, the number of proper colorings c : V → Fin n with exactly k colors and weight j equals the number with exactly k colors and weight (n-1)|V| - j.
-/

theorem simple_graph_t_chromatic_ps_coloring_count_rev {V : Type*} [Fintype V] (G : SimpleGraph V) (n k j : ℕ)
    (hj : j ≤ (n - 1) * Fintype.card V) :
    Fintype.card {c : G.Coloring (Fin n) //
        (Finset.univ.image c).card = k ∧ ∑ v : V, (c v : ℕ) = j} =
    Fintype.card {c : G.Coloring (Fin n) //
        (Finset.univ.image c).card = k ∧ ∑ v : V, (c v : ℕ) = (n - 1) * Fintype.card V - j} := by
  classical
  let r : G.Coloring (Fin n) → G.Coloring (Fin n) := fun c =>
    SimpleGraph.Coloring.mk (fun v => Fin.rev (c v)) (fun h e => c.valid h (Fin.rev_injective e))
  have hr : ∀ c, r (r c) = c := fun c => by ext v; exact congrArg Fin.val (Fin.rev_rev (c v))
  have hL : ∀ c : G.Coloring (Fin n), (Finset.univ.image (r c)).card = (Finset.univ.image c).card := by
    intro c
    have : Finset.univ.image (r c) = (Finset.univ.image c).image Fin.rev := by
      rw [Finset.image_image]; rfl
    rw [this, Finset.card_image_of_injective _ Fin.rev_injective]
  have hW : ∀ c : G.Coloring (Fin n), ∑ v : V, ((r c) v : ℕ) + ∑ v : V, (c v : ℕ) = (n - 1) * Fintype.card V := by
    intro c
    rw [← Finset.sum_add_distrib]
    have : ∀ v, ((r c) v : ℕ) + (c v : ℕ) = n - 1 := by
      intro v
      show ((Fin.rev (c v) : Fin n) : ℕ) + (c v : ℕ) = n - 1
      rw [Fin.val_rev]; have := (c v).isLt; omega
    simp only [this, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  refine Fintype.card_congr
    { toFun := fun c => ⟨r c.1, by rw [hL]; refine ⟨c.2.1, ?_⟩; have := hW c.1; omega⟩
      invFun := fun c => ⟨r c.1, by rw [hL]; refine ⟨c.2.1, ?_⟩; have := hW c.1; have := hW (r c.1); rw [hr] at this; omega⟩
      left_inv := fun c => by simp [hr]
      right_inv := fun c => by simp [hr] }
