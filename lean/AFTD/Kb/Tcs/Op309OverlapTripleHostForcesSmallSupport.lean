import AFTD.Prelude
import AFTD.Kb.Tcs.Op309IncidenceOverlapFivePeel

/-!
# op309_overlap_triple_host_forces_small_support

Topic: graphs   Node: c36441740a5e

Provenance: helper lemma. OP-309 incidence-selection obstruction, IN-1099.

If overlap-five peeling holds and each host meets a given nonempty class set in zero or three classes, some class in that set meets at most two hosts.
-/

theorem op309_overlap_triple_host_forces_small_support
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (I : SimpleGraph (A ⊕ B)) [DecidableRel I.Adj] (S : Finset A) (hS : S.Nonempty)
    (hhost : ∀ b : B, (S.filter (fun a : A => I.Adj (.inl a) (.inr b))).card = 0 ∨
      (S.filter (fun a : A => I.Adj (.inl a) (.inr b))).card = 3)
    (hpeel : op309_incidence_overlap_five_peel I) :
    ∃ a ∈ S, (Finset.univ.filter (fun b : B => I.Adj (.inl a) (.inr b))).card ≤ 2 := by
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
  exact ⟨a,ha,by omega⟩
