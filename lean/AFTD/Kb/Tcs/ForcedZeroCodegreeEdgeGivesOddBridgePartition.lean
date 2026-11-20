import AFTD.Prelude
import AFTD.Kb.Tcs.ForcedMatchingEdgeBlocksFourAndSixSwitches
import AFTD.Kb.Tcs.PerfectMatchingSingleCrossingCutSideOdd
import AFTD.Kb.Tcs.MatchingZeroCodegreeBlockedFourSwitchesNeighborhoodsPartition
import AFTD.Kb.Tcs.MatchingZeroCodegreeBlockedSwitchesNeighborhoodsComplete

/-!
# forced_zero_codegree_edge_gives_odd_bridge_partition

Topic: graphs   Node: ec744a25edb9

Provenance: helper lemma. OP-1957 first residual forced-edge structure; the first edge has no common nonneighbors after restricting to the saturated twins' common complement neighbors.

A forced perfect-matching edge with no common nonneighbor is the only edge between two odd vertex sets partitioning the graph.
-/

theorem forced_zero_codegree_edge_gives_odd_bridge_partition {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (P : G.Subgraph) (hP : P.IsPerfectMatching) (u v : V) (huv : P.Adj u v) (hforced : ∀ Q : G.Subgraph, Q.IsPerfectMatching → Q.Adj u v) (hco : ∀ a, ¬ ((Gᶜ).Adj u a ∧ (Gᶜ).Adj v a)) : ∃ A B : Finset V, u ∈ A ∧ v ∈ B ∧ Disjoint A B ∧ A ∪ B = Finset.univ ∧ Odd A.card ∧ Odd B.card ∧ ∀ a ∈ A, ∀ b ∈ B, G.Adj a b → a = u ∧ b = v := by
  classical
  obtain ⟨h4,h6⟩ := forced_matching_edge_blocks_four_and_six_switches G P hP u v huv hforced
  have hpartition := matching_zero_codegree_blocked_four_switches_neighborhoods_partition G P hP u v huv hco h4
  have hcomplete := matching_zero_codegree_blocked_switches_neighborhoods_complete G P hP u v huv hco h4 h6
  let A := insert u ((Gᶜ).neighborFinset v)
  let B := insert v ((Gᶜ).neighborFinset u)
  have huvG : G.Adj u v := P.adj_sub huv
  have huvne : u ≠ v := huvG.ne
  have huA : u ∈ A := by simp [A]
  have hvB : v ∈ B := by simp [B]
  have huB : u ∉ B := by simp [B,huvne]
  have hvA : v ∉ A := by simp [A,huvne.symm]
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    by_cases hau : a = u
    · exact huB (hau ▸ hb)
    · by_cases hav : a = v
      · exact hvA (hav ▸ ha)
      · have hva : (Gᶜ).Adj v a := by
          have ha' : a ∈ (Gᶜ).neighborFinset v := (Finset.mem_insert.mp ha).resolve_left hau
          simpa using ha'
        have hua : (Gᶜ).Adj u a := by
          have hb' : a ∈ (Gᶜ).neighborFinset u := (Finset.mem_insert.mp hb).resolve_left hav
          simpa using hb'
        exact hco a ⟨hua,hva⟩
  have hcover : A ∪ B = Finset.univ := by
    ext a
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hau : a = u
    · left; exact hau.symm ▸ huA
    · by_cases hav : a = v
      · right; exact hav.symm ▸ hvB
      · rcases hpartition a hau hav with hua | hva
        · right
          apply Finset.mem_insert_of_mem
          simpa using hua
        · left
          apply Finset.mem_insert_of_mem
          simpa using hva
  have hcut : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b → a = u ∧ b = v := by
    intro a ha b hb hab
    by_cases hau : a = u
    · by_cases hbv : b = v
      · exact ⟨hau,hbv⟩
      · have hub : (Gᶜ).Adj u b := by
          have hb' : b ∈ (Gᶜ).neighborFinset u := (Finset.mem_insert.mp hb).resolve_left hbv
          simpa using hb'
        exact ((SimpleGraph.compl_adj G u b).mp hub).2 (hau ▸ hab) |>.elim
    · have hva : (Gᶜ).Adj v a := by
        have ha' : a ∈ (Gᶜ).neighborFinset v := (Finset.mem_insert.mp ha).resolve_left hau
        simpa using ha'
      by_cases hbv : b = v
      · exact ((SimpleGraph.compl_adj G v a).mp hva).2 (hbv ▸ hab.symm) |>.elim
      · have hub : (Gᶜ).Adj u b := by
          have hb' : b ∈ (Gᶜ).neighborFinset u := (Finset.mem_insert.mp hb).resolve_left hbv
          simpa using hb'
        have hba := hcomplete b a hub hva
        exact ((SimpleGraph.compl_adj G b a).mp hba).2 hab.symm |>.elim
  have hoddA := perfect_matching_single_crossing_cut_side_odd G P hP A B u v hdis hcover huA hvB huv hcut
  have hflip : ∀ b ∈ B, ∀ a ∈ A, G.Adj b a → b = v ∧ a = u := by
    intro b hb a ha hba
    obtain ⟨hau,hbv⟩ := hcut a ha b hb hba.symm
    exact ⟨hbv,hau⟩
  have hcover' : B ∪ A = Finset.univ := by simpa [Finset.union_comm] using hcover
  have hoddB := perfect_matching_single_crossing_cut_side_odd G P hP B A v u hdis.symm hcover' hvB huA huv.symm hflip
  exact ⟨A,B,huA,hvB,hdis,hcover,hoddA,hoddB,hcut⟩
