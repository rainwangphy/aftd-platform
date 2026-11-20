import AFTD.Prelude
import AFTD.Kb.Tcs.Op309IncidenceOverlapFivePeel

/-!
# op309_three_host_dense_core_blocks_overlap_peeling

Topic: graphs   Node: 084d8a04205d

Provenance: helper lemma. OP-309 incidence-selection obstruction, IN-1099.

If a nonempty class set meets each host in zero or three classes and each of its classes meets at least three hosts, overlap-five peeling is impossible.
-/

theorem op309_three_host_dense_core_blocks_overlap_peeling
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (I : SimpleGraph (A ⊕ B)) [DecidableRel I.Adj] (S : Finset A) (hS : S.Nonempty)
    (hhost : ∀ b : B, (S.filter (fun a : A => I.Adj (.inl a) (.inr b))).card = 0 ∨
      (S.filter (fun a : A => I.Adj (.inl a) (.inr b))).card = 3)
    (hclass : ∀ a ∈ S, 3 ≤ (Finset.univ.filter (fun b : B => I.Adj (.inl a) (.inr b))).card) :
    ¬ op309_incidence_overlap_five_peel I := by
  intro hpeel
  obtain ⟨a,ha,_,hw⟩ := hpeel S hS
  have hlocal (b : B) : (if I.Adj (.inl a) (.inr b) then
      (S.filter (fun a' : A => I.Adj (.inl a') (.inr b))).card - 1 else 0) =
      (if I.Adj (.inl a) (.inr b) then 2 else 0) := by
    by_cases hab : I.Adj (.inl a) (.inr b)
    · simp only [hab, if_true]
      have hp : 0 < (S.filter (fun a' : A => I.Adj (.inl a') (.inr b))).card :=
        Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hab⟩⟩
      rcases hhost b with hzero | hthree <;> omega
    · simp [hab]
  have heq : (∑ b : B, if I.Adj (.inl a) (.inr b) then
        (S.filter (fun a' : A => I.Adj (.inl a') (.inr b))).card - 1 else 0) =
      2 * (Finset.univ.filter (fun b : B => I.Adj (.inl a) (.inr b))).card := by
    simp_rw [hlocal]
    rw [← Finset.sum_filter]
    simp [Nat.mul_comm]
  rw [heq] at hw
  have := hclass a ha
  omega
