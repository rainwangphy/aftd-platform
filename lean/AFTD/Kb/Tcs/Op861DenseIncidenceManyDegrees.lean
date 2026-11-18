import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op861_dense_incidence_many_degrees

Topic: graphs   Node: a13e41562977

Provenance: helper lemma. The many-large-degrees step used in op861_dense_triangle_orientation_sqrt_cover.

If a finite bipartite incidence set with sides totaling at most k vertices has at least k squared divided by 96 edges, then at least k divided by 192 vertices on the first side each have degree at least k divided by 192, with the inequalities interpreted without rounding by multiplying by the stated constants.
-/

theorem op861_dense_incidence_many_degrees (α : Type*) [DecidableEq α]
    (k : ℕ) (U V : Finset α) (E : Finset (α × α))
    (hUV : Disjoint U V) (hsize : U.card + V.card ≤ k)
    (hE : ∀ e ∈ E, e.1 ∈ U ∧ e.2 ∈ V) (hdense : k^2 ≤ 96 * E.card) :
    k ≤ 192 * (U.filter (fun x => k ≤ 192 * (E.filter (fun e => e.1 = x)).card)).card := by
  have hUV' : Disjoint U V := hUV
  clear hUV'
  let deg : α → ℕ := fun x => (E.filter (fun e => e.1 = x)).card
  let S : Finset α := U.filter (fun x => k ≤ 192 * deg x)
  have hgoal : k ≤ 192 * S.card := by
    by_contra hcon
    have hSlt : 192 * S.card < k := by omega
    have hVk : V.card ≤ k := by omega
    have hdegV : ∀ x ∈ U, deg x ≤ V.card := by
      intro x hx
      dsimp [deg]
      apply Finset.card_le_card_of_injOn (fun e : α × α => e.2)
      · intro e he
        exact (hE e (Finset.mem_filter.mp he).1).2
      · intro e he f hf h
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at he hf
        ext
        · exact he.2.trans hf.2.symm
        · exact h
    have hsum : (∑ x ∈ U, deg x) = E.card := by
      dsimp [deg]
      rw [← Finset.card_eq_sum_card_fiberwise]
      · intro e he
        exact (hE e he).1
    have hsplit : E.card = (∑ x ∈ S, deg x) + (∑ x ∈ U \ S, deg x) := by
      rw [← hsum]
      have hsdiff := Finset.sum_sdiff (s₁ := S) (s₂ := U) (f := deg) (Finset.filter_subset _ _)
      omega
    have hhigh : (∑ x ∈ S, deg x) ≤ S.card * k := by
      calc
        (∑ x ∈ S, deg x) ≤ ∑ x ∈ S, k := by
          apply Finset.sum_le_sum
          intro x hx
          exact le_trans (hdegV x (Finset.mem_of_mem_filter x hx)) hVk
        _ = S.card * k := by simp [Finset.sum_const]
    have hlow : 192 * (∑ x ∈ U \ S, deg x) ≤ (U \ S).card * k := by
      calc
        192 * (∑ x ∈ U \ S, deg x) = ∑ x ∈ U \ S, 192 * deg x := by
          rw [Finset.mul_sum]
        _ ≤ ∑ x ∈ U \ S, k := by
          apply Finset.sum_le_sum
          intro x hx
          have hxU : x ∈ U := (Finset.mem_sdiff.mp hx).1
          have hxnot : x ∉ S := (Finset.mem_sdiff.mp hx).2
          have hnot : ¬ k ≤ 192 * deg x := by
            intro hle
            apply hxnot
            dsimp [S]
            exact Finset.mem_filter.mpr ⟨hxU, hle⟩
          omega
        _ = (U \ S).card * k := by simp [Finset.sum_const]
    have hEdense : 192 * E.card ≤ 192 * (S.card * k) + (U \ S).card * k := by
      calc
        192 * E.card = 192 * ((∑ x ∈ S, deg x) + (∑ x ∈ U \ S, deg x)) := by rw [hsplit]
        _ = 192 * (∑ x ∈ S, deg x) + 192 * (∑ x ∈ U \ S, deg x) := by ring
        _ ≤ 192 * (S.card * k) + (U \ S).card * k := by
          apply Nat.add_le_add
          · exact Nat.mul_le_mul_left 192 hhigh
          · exact hlow
    have hpart : (U \ S).card + S.card ≤ k := by
      have h := Finset.card_sdiff_add_card_eq_card (s := S) (t := U) (Finset.filter_subset _ _)
      omega
    nlinarith
  simpa [S, deg] using hgoal
