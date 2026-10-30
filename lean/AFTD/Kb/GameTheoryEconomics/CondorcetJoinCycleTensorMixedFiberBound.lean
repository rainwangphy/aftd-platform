import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetPrivateTripleStationarityObstruction
import AFTD.Kb.Tcs.G

/-!
# condorcet_join_cycle_tensor_mixed_fiber_bound

Topic: social_choice   Node: 2969dfd40e15

Provenance: helper lemma. IN-372 supporting structural diagnostic for OP-19, 2026-10-30. Exact finite certificates and source/counting arguments documented in In372Oct30/ResearchNotes.txt. No novelty or research advance is claimed; the main election statement remains unchanged.

For the fixed19-vertex residue tournament, let left and right real fiber masses lie between0 and a common nonnegative bound k. Assume that both sides have a positive entry, some fiber on either side is zero, and whenever a tournament triangle has a positive opposite-side root, the masses at its other two vertices on the chosen side sum to at most k. Then twice the combined mass is at most37*k. This is a certificate for a particular tensor-family obstruction, not a statement about arbitrary S3 relations.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

def condorcet_tensor_triangle (a b c : Fin 19) : Prop :=
  (condorcet_private_stationary_relation a b ∧
    condorcet_private_stationary_relation b c ∧ condorcet_private_stationary_relation c a) ∨
  (condorcet_private_stationary_relation b a ∧
    condorcet_private_stationary_relation a c ∧ condorcet_private_stationary_relation c b)
instance (a b c : Fin 19) : Decidable (condorcet_tensor_triangle a b c) := by
  unfold condorcet_tensor_triangle
  infer_instance

def condorcet_tensor_hamilton_order : Fin 19 → Fin 19 :=
  ![0,2,16,5,14,10,1,18,9,17,3,6,11,7,12,13,4,15,8]
def condorcet_tensor_pair_cycle (r s i : Fin 19) : Fin 19 :=
  if condorcet_private_stationary_relation r s then r+(s-r)*condorcet_tensor_hamilton_order i
  else s+(r-s)*condorcet_tensor_hamilton_order i

theorem condorcet_tensor_pair_cycle_check : ∀ r s : Fin 19, r ≠ s →
    Function.Bijective (condorcet_tensor_pair_cycle r s) ∧
    ∀ i : Fin 19,
      condorcet_tensor_triangle (condorcet_tensor_pair_cycle r s i)
        (condorcet_tensor_pair_cycle r s (i+1)) r ∨
      condorcet_tensor_triangle (condorcet_tensor_pair_cycle r s i)
        (condorcet_tensor_pair_cycle r s (i+1)) s := by
  decide

theorem condorcet_tensor_shift_bijective : ∀ j : Fin 19,
    Function.Bijective (fun i : Fin 19 => i+j) := by decide

theorem condorcet_tensor_single_pairs_check : ∀ r : Fin 19,
    condorcet_tensor_triangle (1+r) (2+r) r ∧
    condorcet_tensor_triangle (3+r) (5+r) r := by decide

theorem condorcet_tensor_odd_cycle_sum_bound (l : Fin 19 → ℝ) (k : ℝ)
    (hedge : ∀ i : Fin 19, l i + l (i+1) ≤ k) :
    2 * (∑ i, l i) ≤ 19*k := by
  have h := sum_le_sum (s := (univ : Finset (Fin 19))) (fun i _ => hedge i)
  rw [sum_add_distrib, (condorcet_tensor_shift_bijective 1).sum_comp l] at h
  simpa [two_mul] using h

theorem condorcet_tensor_odd_cycle_zero_bound (l : Fin 19 → ℝ) (k : ℝ)
    (hedge : ∀ i : Fin 19, l i + l (i+1) ≤ k) (hz : l 0 = 0) :
    2 * (∑ i, l i) ≤ 18*k := by
  have h1 := hedge 1
  have h3 := hedge 3
  have h5 := hedge 5
  have h7 := hedge 7
  have h9 := hedge 9
  have h11 := hedge 11
  have h13 := hedge 13
  have h15 := hedge 15
  have h17 := hedge 17
  change l 1+l 2 ≤ k at h1
  change l 3+l 4 ≤ k at h3
  change l 5+l 6 ≤ k at h5
  change l 7+l 8 ≤ k at h7
  change l 9+l 10 ≤ k at h9
  change l 11+l 12 ≤ k at h11
  change l 13+l 14 ≤ k at h13
  change l 15+l 16 ≤ k at h15
  change l 17+l 18 ≤ k at h17
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change 2 * (l 0+(l 1+(l 2+(l 3+(l 4+(l 5+(l 6+(l 7+(l 8+(l 9+(l 10+(l 11+(l 12+(l 13+(l 14+(l 15+(l 16+(l 17+(l 18))))))))))))))))))) ≤ 18*k
  linarith

theorem condorcet_tensor_two_pair_sum_bound (l : Fin 19 → ℝ) (k : ℝ)
    (hle : ∀ i, l i ≤ k) (h12 : l 1+l 2 ≤ k) (h35 : l 3+l 5 ≤ k) :
    (∑ i, l i) ≤ 17*k := by
  have h0 := hle 0
  have h4 := hle 4
  have h6 := hle 6
  have h7 := hle 7
  have h8 := hle 8
  have h9 := hle 9
  have h10 := hle 10
  have h11 := hle 11
  have h12' := hle 12
  have h13 := hle 13
  have h14 := hle 14
  have h15 := hle 15
  have h16 := hle 16
  have h17 := hle 17
  have h18 := hle 18
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (l 0+(l 1+(l 2+(l 3+(l 4+(l 5+(l 6+(l 7+(l 8+(l 9+(l 10+(l 11+(l 12+(l 13+(l 14+(l 15+(l 16+(l 17+(l 18))))))))))))))))))) ≤ 17*k
  linarith

theorem condorcet_tensor_two_roots_mass_bound (l : Fin 19 → ℝ) (k : ℝ)
    (r s : Fin 19) (hrs : r ≠ s)
    (hpair : ∀ a b, condorcet_tensor_triangle a b r ∨ condorcet_tensor_triangle a b s →
      l a+l b ≤ k) :
    2 * (∑ a, l a) ≤ 19*k ∧
    (∀ a, l a = 0 → 2 * (∑ b, l b) ≤ 18*k) := by
  classical
  obtain ⟨hbij,hcycle⟩ := condorcet_tensor_pair_cycle_check r s hrs
  let f := condorcet_tensor_pair_cycle r s
  have hedge : ∀ i : Fin 19, l (f i)+l (f (i+1)) ≤ k :=
    fun i => hpair _ _ (hcycle i)
  have hsum : (∑ i, l (f i)) = ∑ a, l a := hbij.sum_comp l
  refine ⟨?_,?_⟩
  · have h := condorcet_tensor_odd_cycle_sum_bound (l ∘ f) k hedge
    simpa only [Function.comp_apply, hsum] using h
  · intro a ha
    obtain ⟨j,hj⟩ := hbij.surjective a
    let g : Fin 19 → ℝ := fun i => l (f (i+j))
    have hg : ∀ i : Fin 19, g i+g (i+1) ≤ k := by
      intro i
      simpa only [g, add_assoc, add_comm, add_left_comm] using hedge (i+j)
    have hg0 : g 0 = 0 := by
      change f j = a at hj
      simpa only [g, zero_add, hj] using ha
    have h := condorcet_tensor_odd_cycle_zero_bound g k hg hg0
    have hgsum : (∑ i, g i) = ∑ a, l a := by
      change (∑ i, (l ∘ f) (i+j)) = ∑ a, l a
      rw [(condorcet_tensor_shift_bijective j).sum_comp (l ∘ f)]
      exact hsum
    simpa only [hgsum] using h

theorem condorcet_tensor_one_root_mass_bound (l : Fin 19 → ℝ) (k : ℝ)
    (r : Fin 19) (hle : ∀ i, l i ≤ k)
    (hpair : ∀ a b, condorcet_tensor_triangle a b r → l a+l b ≤ k) :
    (∑ a, l a) ≤ 17*k := by
  let g : Fin 19 → ℝ := fun i => l (i+r)
  have h := condorcet_tensor_two_pair_sum_bound g k (fun i => hle _)
    (hpair _ _ (condorcet_tensor_single_pairs_check r).1)
    (hpair _ _ (condorcet_tensor_single_pairs_check r).2)
  simpa only [g, (condorcet_tensor_shift_bijective r).sum_comp l] using h

theorem condorcet_join_cycle_tensor_mixed_fiber_bound
    (l r : Fin 19 → ℝ) (k : ℝ) (hk : 0 ≤ k)
    (hl : ∀ a, 0 ≤ l a ∧ l a ≤ k) (hr : ∀ a, 0 ≤ r a ∧ r a ≤ k)
    (hlpos : ∃ a, 0 < l a) (hrpos : ∃ a, 0 < r a)
    (hmissing : ∃ a, l a = 0 ∨ r a = 0)
    (htri : ∀ a b c, condorcet_tensor_triangle a b c →
      (0 < r c → l a+l b ≤ k) ∧ (0 < l c → r a+r b ≤ k)) :
    2 * ((∑ a, l a)+(∑ a, r a)) ≤ 37*k := by
  classical
  obtain ⟨a,ha⟩ := hlpos
  obtain ⟨b,hb⟩ := hrpos
  by_cases hltwo : ∃ a', a' ≠ a ∧ 0 < l a'
  · obtain ⟨a',haa',ha'⟩ := hltwo
    obtain ⟨hR,hRzero⟩ := condorcet_tensor_two_roots_mass_bound r k a' a haa' (by
      intro x y h
      rcases h with h | h
      · exact (htri x y a' h).2 ha'
      · exact (htri x y a h).2 ha)
    by_cases hrtwo : ∃ b', b' ≠ b ∧ 0 < r b'
    · obtain ⟨b',hbb',hb'⟩ := hrtwo
      obtain ⟨hL,hLzero⟩ := condorcet_tensor_two_roots_mass_bound l k b' b hbb' (by
        intro x y h
        rcases h with h | h
        · exact (htri x y b' h).1 hb'
        · exact (htri x y b h).1 hb)
      obtain ⟨c,hc|hc⟩ := hmissing
      · have h := hLzero c hc
        linarith
      · have h := hRzero c hc
        linarith
    · have hrzero : ∀ c, c ≠ b → r c = 0 := by
        intro c hc
        have hnot : ¬0 < r c := fun h => hrtwo ⟨c,hc,h⟩
        exact le_antisymm (le_of_not_gt hnot) (hr c).1
      have hsumR : (∑ c, r c) = r b := sum_eq_single b (fun c _ hc => hrzero c hc) (by simp)
      have hL := condorcet_tensor_one_root_mass_bound l k b (fun c => (hl c).2)
        (fun x y h => (htri x y b h).1 hb)
      rw [hsumR]
      linarith [(hr b).2]
  · have hlzero : ∀ c, c ≠ a → l c = 0 := by
      intro c hc
      have hnot : ¬0 < l c := fun h => hltwo ⟨c,hc,h⟩
      exact le_antisymm (le_of_not_gt hnot) (hl c).1
    have hsumL : (∑ c, l c) = l a := sum_eq_single a (fun c _ hc => hlzero c hc) (by simp)
    have hR := condorcet_tensor_one_root_mass_bound r k a (fun c => (hr c).2)
      (fun x y h => (htri x y a h).2 ha)
    rw [hsumL]
    linarith [(hl a).2]
