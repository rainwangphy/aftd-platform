import AFTD.Prelude

/-!
# op1525_equal_block_color_profiles_match

Topic: combinatorics   Node: 62dee01627ce

Provenance: helper lemma. The final profile-to-permutation step in the multipartite coloring-reconstruction route for OP-1525.

If two Boolean colorings of the same finite collection of equally sized blocks have the same number of blocks containing exactly k true vertices for each possible k, then one coloring is obtained from the other by permuting blocks and independently permuting vertices inside every block.
-/

theorem op1525_equal_block_color_profiles_match
    (m r : ℕ) (f g : Fin m → Fin r → Bool)
    (hprofile : ∀ k : Fin (r + 1),
      ((Finset.univ : Finset (Fin m)).filter (fun i =>
        ((Finset.univ : Finset (Fin r)).filter (fun j => f i j = true)).card = k.val)).card =
      ((Finset.univ : Finset (Fin m)).filter (fun i =>
        ((Finset.univ : Finset (Fin r)).filter (fun j => g i j = true)).card = k.val)).card) :
    ∃ σ : Equiv.Perm (Fin m), ∃ τ : Fin m → Equiv.Perm (Fin r),
      ∀ i j, f (σ i) (τ i j) = g i j := by
  classical
  let P (h : Fin m → Fin r → Bool) (i : Fin m) : Fin (r + 1) :=
    ⟨((Finset.univ : Finset (Fin r)).filter (fun j => h i j = true)).card,
      Nat.lt_succ_of_le (by simpa using Finset.card_filter_le (Finset.univ : Finset (Fin r)) (fun j => h i j = true))⟩
  have hcard (k : Fin (r + 1)) : Fintype.card {i // P g i = k} = Fintype.card {i // P f i = k} := by
    simp only [Fintype.card_subtype]
    simpa only [P, Fin.ext_iff, Fin.val_mk] using (hprofile k).symm
  let σ : Equiv.Perm (Fin m) := Equiv.ofFiberEquiv (fun k => Fintype.equivOfCardEq (hcard k))
  have hσ (i : Fin m) : P f (σ i) = P g i := Equiv.ofFiberEquiv_map _ i
  have hc (i : Fin m) :
      ((Finset.univ : Finset (Fin r)).filter (fun j => g i j = true)).card =
      ((Finset.univ : Finset (Fin r)).filter (fun j => f (σ i) j = true)).card := by
    exact (congrArg Fin.val (hσ i)).symm
  have hbool (i : Fin m) (b : Bool) : Fintype.card {j // g i j = b} = Fintype.card {j // f (σ i) j = b} := by
    simp only [Fintype.card_subtype]
    cases b with
    | true => exact hc i
    | false =>
      have hg := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin r))) (fun j => g i j = true)
      have hf := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin r))) (fun j => f (σ i) j = true)
      simp only [Bool.not_eq_true] at hg hf
      have hh := hc i
      omega
  let τ (i : Fin m) : Equiv.Perm (Fin r) := Equiv.ofFiberEquiv (fun b => Fintype.equivOfCardEq (hbool i b))
  refine ⟨σ, τ, ?_⟩
  intro i j
  exact Equiv.ofFiberEquiv_map _ j
