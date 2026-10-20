import AFTD.Prelude

/-!
# flow_cut_divergence_eq

Topic: information   Node: 5bcd27e6d5ef

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

Summing net vertex divergence of any flow f over a vertex set S equals the cut-crossing flow leaving S minus the cut-crossing flow entering S.
-/

/-- Summing net vertex divergence of any flow f over a vertex set S equals the cut-crossing flow leaving S minus the cut-crossing flow entering S. -/
theorem flow_cut_divergence_eq
    {V : Type} [Fintype V] [DecidableEq V]
    (f : V → V → ℝ) (S : Finset V) :
    ∑ v ∈ S, ((∑ w, f v w) - (∑ u, f u v)) =
    (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f v w)) - (∑ v ∈ S, ∑ u, (if u ∈ S then 0 else f u v)) := by
  have hsplit_out (v : V) :
      (∑ w, f v w) = (∑ w ∈ S, f v w) + (∑ w ∈ Sᶜ, f v w) := by
    exact (Finset.sum_add_sum_compl S (fun w => f v w)).symm
  have hsplit_in (v : V) :
      (∑ u, f u v) = (∑ u ∈ S, f u v) + (∑ u ∈ Sᶜ, f u v) := by
    exact (Finset.sum_add_sum_compl S (fun u => f u v)).symm
  have hcompl_out (v : V) :
      (∑ w, (if w ∈ S then 0 else f v w)) = ∑ w ∈ Sᶜ, f v w := by
    calc
      (∑ w, (if w ∈ S then 0 else f v w))
          = ∑ w, (if w ∈ Sᶜ then f v w else 0) := by
            apply Finset.sum_congr rfl
            intro w _
            by_cases hw : w ∈ S
            · simp [hw]
            · simp [hw]
      _ = ∑ w ∈ Sᶜ, f v w := by
            simpa using (Finset.sum_ite_mem (Finset.univ : Finset V) Sᶜ (fun w => f v w))
  have hcompl_in (v : V) :
      (∑ u, (if u ∈ S then 0 else f u v)) = ∑ u ∈ Sᶜ, f u v := by
    calc
      (∑ u, (if u ∈ S then 0 else f u v))
          = ∑ u, (if u ∈ Sᶜ then f u v else 0) := by
            apply Finset.sum_congr rfl
            intro u _
            by_cases hu : u ∈ S
            · simp [hu]
            · simp [hu]
      _ = ∑ u ∈ Sᶜ, f u v := by
            simpa using (Finset.sum_ite_mem (Finset.univ : Finset V) Sᶜ (fun u => f u v))
  have hL1 : (∑ v ∈ S, ∑ w, f v w) =
      (∑ v ∈ S, ∑ w ∈ S, f v w) + (∑ v ∈ S, ∑ w ∈ Sᶜ, f v w) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact hsplit_out v
  have hL2 : (∑ v ∈ S, ∑ u, f u v) =
      (∑ v ∈ S, ∑ u ∈ S, f u v) + (∑ v ∈ S, ∑ u ∈ Sᶜ, f u v) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact hsplit_in v
  have hA : (∑ v ∈ S, ∑ w ∈ S, f v w) = (∑ v ∈ S, ∑ u ∈ S, f u v) := by
    rw [Finset.sum_comm]
  have hR1 : (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f v w)) =
      ∑ v ∈ S, ∑ w ∈ Sᶜ, f v w := by
    apply Finset.sum_congr rfl
    intro v _
    exact hcompl_out v
  have hR2 : (∑ v ∈ S, ∑ u, (if u ∈ S then 0 else f u v)) =
      ∑ v ∈ S, ∑ u ∈ Sᶜ, f u v := by
    apply Finset.sum_congr rfl
    intro v _
    exact hcompl_in v
  rw [hR1, hR2, Finset.sum_sub_distrib, hL1, hL2, hA]
  ring
