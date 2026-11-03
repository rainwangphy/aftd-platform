import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteEndomapMissingImageEqNonrepresentatives

/-!
# finite_endomap_local_degree_deficit_le_missing_image

Topic: combinatorics   Node: e3df91c57934

Provenance: helper lemma. Arc-map counting for the four-cycle campaign.

For a finite endomap whose image heads equal the original tails, the sum of positive local tail-count minus head-count deficits is at most the number of elements missing from the image.
-/

theorem finite_endomap_local_degree_deficit_le_missing_image
    (A V : Type) [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
    (f r : A → A) (tail head : A → V)
    (hr : ∀ x, f (r (f x)) = f x)
    (hf : ∀ x, head (f x) = tail x) :
    (∑ v : V, ((Finset.univ.filter fun x : A => tail x = v).card -
      (Finset.univ.filter fun x : A => head x = v).card)) ≤
      ((Finset.univ : Finset A) \ Finset.univ.image f).card := by
  classical
  let N : Finset A := Finset.univ.filter fun x => r (f x) ≠ x
  have hlocal : ∀ v : V,
      (Finset.univ.filter fun x : A => tail x = v).card -
        (Finset.univ.filter fun x : A => head x = v).card ≤
          (N.filter fun x => tail x = v).card := by
    intro v
    let O : Finset A := Finset.univ.filter fun x => tail x = v
    let R : Finset A := O.filter fun x => r (f x) = x
    let I : Finset A := Finset.univ.filter fun x => head x = v
    have hinj : Set.InjOn f (↑R : Set A) := by
      intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      calc
        x = r (f x) := hx'.symm
        _ = r (f y) := congrArg r hxy
        _ = y := hy'
    have hsub : R.image f ⊆ I := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      have hv : tail x = v := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf x).trans hv⟩
    have hc : R.card ≤ I.card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card hsub
    have hp := Finset.card_filter_add_card_filter_not (s := O) (fun x => r (f x) = x)
    have hneg : O.filter (fun x => ¬ r (f x) = x) = N.filter (fun x => tail x = v) := by
      ext x
      simp [O,N, and_comm]
    rw [hneg] at hp
    change R.card + (N.filter fun x => tail x = v).card = O.card at hp
    change O.card - I.card ≤ (N.filter fun x => tail x = v).card
    omega
  have hsum : N.card = ∑ v : V, (N.filter fun x => tail x = v).card := by
    exact Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (fun x hx => Finset.mem_univ _)
  have hbound := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hlocal v)
  rw [← hsum] at hbound
  have hidentity := finite_endomap_missing_image_eq_nonrepresentatives A f r hr
  change ((Finset.univ : Finset A) \ Finset.univ.image f).card = N.card at hidentity
  rw [hidentity]
  exact hbound
