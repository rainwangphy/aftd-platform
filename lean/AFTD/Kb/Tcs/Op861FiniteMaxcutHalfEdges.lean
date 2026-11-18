import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op861_finite_maxcut_half_edges

Topic: graphs   Node: 4436fe32b984

Provenance: helper lemma. The dense crossing-edge cut used in op861_dense_triangle_orientation_sqrt_cover.

For a finite vertex set and any finite set of nonloop ordered edges with endpoints in it, some vertex subset cuts at least half of the edges.
-/

open Finset

def op861_finite_maxcut_half_edges_cut_prop {α : Type*} (e : α × α) (U : Finset α) : Prop :=
  (e.1 ∈ U ∧ e.2 ∉ U) ∨ (e.2 ∈ U ∧ e.1 ∉ U)

instance {α : Type*} [DecidableEq α] (e : α × α) (U : Finset α) :
    Decidable (op861_finite_maxcut_half_edges_cut_prop e U) :=
  inferInstanceAs (Decidable ((e.1 ∈ U ∧ e.2 ∉ U) ∨ (e.2 ∈ U ∧ e.1 ∉ U)))

theorem op861_finite_maxcut_half_edges_symmDiff_subset {α : Type*} [DecidableEq α]
    {S U : Finset α} {u : α} (hU : U ⊆ S) (hu : u ∈ S) :
    symmDiff U {u} ⊆ S := by
  intro x hx
  rw [mem_symmDiff] at hx
  rcases hx with ⟨hxU, _⟩ | ⟨hxu, _⟩
  · exact hU hxU
  · rw [mem_singleton] at hxu; subst hxu; exact hu

theorem op861_finite_maxcut_half_edges_cut_prop_symmDiff_left {α : Type*} [DecidableEq α]
    (U : Finset α) (e : α × α) (hne : e.1 ≠ e.2) :
    op861_finite_maxcut_half_edges_cut_prop e (symmDiff U {e.1}) ↔
      ¬ op861_finite_maxcut_half_edges_cut_prop e U := by
  dsimp [op861_finite_maxcut_half_edges_cut_prop]
  have h1 : e.1 ∈ symmDiff U {e.1} ↔ e.1 ∉ U := by simp [mem_symmDiff]
  have h2 : e.2 ∈ symmDiff U {e.1} ↔ e.2 ∈ U := by simp [mem_symmDiff, hne.symm]
  rw [h1, h2]
  tauto

theorem op861_finite_maxcut_half_edges_card_filter_cut_prop_eq {α : Type*} [DecidableEq α]
    (S : Finset α) (e : α × α) (he1 : e.1 ∈ S) (hne : e.1 ≠ e.2) :
    2 * ((S.powerset).filter (fun U => op861_finite_maxcut_half_edges_cut_prop e U)).card = (S.powerset).card := by
  let A := (S.powerset).filter (fun U => op861_finite_maxcut_half_edges_cut_prop e U)
  let B := (S.powerset).filter (fun U => ¬ op861_finite_maxcut_half_edges_cut_prop e U)
  have hAB : A.card + B.card = (S.powerset).card :=
    card_filter_add_card_filter_not (op861_finite_maxcut_half_edges_cut_prop e)
  have heq : A.card = B.card := by
    refine card_bij' (fun U _ => symmDiff U {e.1}) (fun U _ => symmDiff U {e.1}) ?_ ?_ ?_ ?_
    · intro U hU
      rw [mem_filter, mem_powerset] at hU ⊢
      refine ⟨op861_finite_maxcut_half_edges_symmDiff_subset hU.1 he1, ?_⟩
      rw [op861_finite_maxcut_half_edges_cut_prop_symmDiff_left _ _ hne]
      exact not_not.mpr hU.2
    · intro U hU
      rw [mem_filter, mem_powerset] at hU ⊢
      refine ⟨op861_finite_maxcut_half_edges_symmDiff_subset hU.1 he1, ?_⟩
      rw [op861_finite_maxcut_half_edges_cut_prop_symmDiff_left _ _ hne]
      exact hU.2
    · intro U _
      rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]
    · intro U _
      rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]
  linarith

theorem op861_finite_maxcut_half_edges_sum_cut_card {α : Type*} [DecidableEq α]
    (S : Finset α) (E : Finset (α × α)) :
    ∑ U ∈ S.powerset, (E.filter (op861_finite_maxcut_half_edges_cut_prop · U)).card =
    ∑ e ∈ E, (S.powerset.filter (op861_finite_maxcut_half_edges_cut_prop e)).card := by
  have h1 : ∀ U, (E.filter (op861_finite_maxcut_half_edges_cut_prop · U)).card =
      ∑ e ∈ E, (if op861_finite_maxcut_half_edges_cut_prop e U then 1 else 0) := by
    intro U
    exact (sum_boole (op861_finite_maxcut_half_edges_cut_prop · U) E).symm
  have h2 : ∀ e, (S.powerset.filter (op861_finite_maxcut_half_edges_cut_prop e)).card =
      ∑ U ∈ S.powerset, (if op861_finite_maxcut_half_edges_cut_prop e U then 1 else 0) := by
    intro e
    exact (sum_boole (op861_finite_maxcut_half_edges_cut_prop e) S.powerset).symm
  simp_rw [h1, h2]
  exact sum_comm

theorem op861_finite_maxcut_half_edges_two_mul_sum_cut {α : Type*} [DecidableEq α]
    (S : Finset α) (E : Finset (α × α))
    (hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2) :
    ∑ U ∈ S.powerset, 2 * (E.filter (op861_finite_maxcut_half_edges_cut_prop · U)).card =
      E.card * S.powerset.card := by
  rw [← mul_sum, op861_finite_maxcut_half_edges_sum_cut_card, mul_sum]
  have h : ∀ e ∈ E, 2 * (S.powerset.filter (op861_finite_maxcut_half_edges_cut_prop e)).card =
      S.powerset.card := by
    intro e he
    have he_props := hE e he
    exact op861_finite_maxcut_half_edges_card_filter_cut_prop_eq S e he_props.1 he_props.2.2
  rw [sum_congr rfl h]
  simp

theorem op861_finite_maxcut_half_edges (α : Type*) [DecidableEq α]
    (S : Finset α) (E : Finset (α × α))
    (hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2) :
    ∃ U : Finset α, U ⊆ S ∧ E.card ≤ 2 *
      (E.filter (fun e => (e.1 ∈ U ∧ e.2 ∉ U) ∨ (e.2 ∈ U ∧ e.1 ∉ U))).card := by
  have h_sum : ∑ _ ∈ S.powerset, E.card =
      ∑ U ∈ S.powerset, 2 * (E.filter (op861_finite_maxcut_half_edges_cut_prop · U)).card := by
    rw [op861_finite_maxcut_half_edges_two_mul_sum_cut S E hE]
    simp [mul_comm]
  have h_ex := Finset.exists_le_of_sum_le (Finset.powerset_nonempty S) (le_of_eq h_sum)
  rcases h_ex with ⟨U, hU, hle⟩
  rw [Finset.mem_powerset] at hU
  exact ⟨U, hU, hle⟩
