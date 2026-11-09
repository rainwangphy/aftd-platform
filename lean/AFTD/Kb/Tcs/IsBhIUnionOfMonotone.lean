import AFTD.Prelude
import AFTD.Kb.Tcs.IsBh

/-!
# is_bh_iUnion_of_monotone

Topic: combinatorics   Node: cf126d671dd4

Provenance: helper lemma. step towards op_939_optimal_upper_density_strictly_greater

The union of an ascending sequence of sets, each of which is a B_h set, is itself a B_h set.
-/

/-- The union of an ascending sequence of sets, each of which is a B_h set, is itself a B_h set. -/
theorem is_bh_iUnion_of_monotone (h : ℕ) (S : ℕ → Set ℕ) (h_mono : ∀ n, S n ⊆ S (n + 1))
    (h_bh : ∀ n, is_bh h (S n)) : is_bh h (⋃ n, S n) := by
  classical
  have mono : ∀ {m n : ℕ}, m ≤ n → S m ⊆ S n := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact subset_rfl
    | succ n hmn ih => exact fun x hx => h_mono n (ih hx)
  intro s t hs ht hsc htc hsum
  have findN : ∀ (u : Multiset ℕ), (∀ x ∈ u, x ∈ ⋃ n, S n) → ∃ N, ∀ x ∈ u, x ∈ S N := by
    intro u hu
    refine ⟨u.toFinset.sup (fun x => if hx : ∃ n, x ∈ S n then Classical.choose hx else 0), ?_⟩
    intro x hx
    have hxs : x ∈ u.toFinset := Multiset.mem_toFinset.mpr hx
    have hex : ∃ n, x ∈ S n := by
      have := hu x hx
      simpa using this
    have hval : (if hx' : ∃ n, x ∈ S n then Classical.choose hx' else 0) = Classical.choose hex := by
      simp only [dif_pos hex]
    have hle : Classical.choose hex ≤ u.toFinset.sup (fun x => if hx : ∃ n, x ∈ S n then Classical.choose hx else 0) := by
      have := Finset.le_sup (s := u.toFinset) (f := fun x => if hx : ∃ n, x ∈ S n then Classical.choose hx else 0) hxs
      rwa [hval] at this
    exact mono hle (Classical.choose_spec hex)
  obtain ⟨N, hNs⟩ := findN s hs
  obtain ⟨M, hMt⟩ := findN t ht
  refine h_bh (max N M) s t (fun x hx => mono (Nat.le_max_left N M) (hNs x hx))
    (fun x hx => mono (Nat.le_max_right N M) (hMt x hx)) hsc htc hsum
