import AFTD.Prelude
import AFTD.Kb.Tcs.CutCapacity
import AFTD.Kb.Tcs.CausalLinearNetworkCode
import AFTD.Kb.Tcs.UnicastSessions
import AFTD.Kb.Tcs.CapacitatedNetwork

/-!
# code_transmissions_cross_cut_le

Topic: information   Node: 197de709599e

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

In a causal linear network code on net, the number of transmissions whose endpoints are separated by a vertex set S is at most T * cutCapacity net S.
-/

/-- The number of transmissions of a code crossing a cut is at most T times the cut capacity. -/
theorem code_transmissions_cross_cut_le
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (F : Type) [Field F] (net : CapacitatedNetwork V) (sess : UnicastSessions V K)
    (code : CausalLinearNetworkCode V K F net sess) (S : Finset V) :
    ((Finset.univ.filter (fun m : Fin code.M => (code.snd m ∈ S) ≠ (code.rcv m ∈ S))).card : ℝ)
      ≤ (code.T : ℝ) * cutCapacity net S := by
  let A := Finset.univ.filter (fun m : Fin code.M => (code.snd m ∈ S) ≠ (code.rcv m ∈ S))
  let g : Fin code.M → V × V := fun m =>
    (if code.snd m ∈ S then code.snd m else code.rcv m,
     if code.snd m ∈ S then code.rcv m else code.snd m)
  have hmaps : Set.MapsTo g (↑A) (↑(S ×ˢ (Finset.univ : Finset V))) := by
    intro m hm
    rw [Finset.mem_coe] at hm ⊢
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    dsimp [A] at hm
    rw [Finset.mem_filter] at hm
    obtain ⟨_, hdiff⟩ := hm
    dsimp [g]
    split_ifs with hs
    · exact hs
    · by_contra hc
      apply hdiff
      simp [hs, hc]
  have hsum : (A.card : ℝ) = ∑ p ∈ S ×ˢ (Finset.univ : Finset V), ((A.filter (fun m => g m = p)).card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise hmaps
    norm_cast
  rw [hsum, Finset.sum_product]
  have h_le : (∑ u ∈ S, ∑ v : V, ((A.filter (fun m => g m = (u, v))).card : ℝ))
      ≤ ∑ u ∈ S, ∑ v : V, (if v ∈ S then 0 else (code.T : ℝ) * net.cap s(u, v)) := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    split_ifs with hv
    · have hempty : A.filter (fun m => g m = (u, v)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro m hm hgm
        dsimp [A] at hm
        rw [Finset.mem_filter] at hm
        obtain ⟨_, hdiff⟩ := hm
        dsimp [g] at hgm
        split_ifs at hgm with hs
        · injection hgm with _ h2
          rw [← h2] at hv
          apply hdiff
          simp [hs, hv]
        · injection hgm with _ h2
          rw [← h2] at hv
          exact hs hv
      rw [hempty, Finset.card_empty, Nat.cast_zero]
    · have hsub : A.filter (fun m => g m = (u, v)) ⊆
          Finset.univ.filter (fun m => s(code.snd m, code.rcv m) = s(u, v)) := by
        intro m hm
        rw [Finset.mem_filter] at hm ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        obtain ⟨_, hgm⟩ := hm
        dsimp [g] at hgm
        split_ifs at hgm with hs
        · injection hgm with hu hv'
          rw [← hu, ← hv']
        · injection hgm with hu hv'
          rw [← hu, ← hv', Sym2.eq_swap]
      have hcard : ((A.filter (fun m => g m = (u, v))).card : ℝ) ≤
          ((Finset.univ.filter (fun m => s(code.snd m, code.rcv m) = s(u, v))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact le_trans hcard (code.cap_le s(u, v))
  refine le_trans h_le ?_
  dsimp [cutCapacity]
  rw [Finset.mul_sum]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs with hv
  · ring
  · ring
