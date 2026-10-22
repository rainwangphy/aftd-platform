import AFTD.Prelude
import AFTD.Kb.Tcs.IsFixV0
import AFTD.Kb.Tcs.IsV0
import AFTD.Kb.Tcs.IsVeDominating
import AFTD.Kb.Tcs.GammaVe

/-!
# not_is_fix_v0_of_isolated

Topic: graphs   Node: 1a18fa515c9c

Provenance: helper lemma. arXiv:2610.26912: Theorem 2.22 -- Vertex Removal and Vertex-Edge Domination

An isolated vertex v in a finite simple graph G (with empty neighborhood) does not belong to V_fix^0(G).
-/

/-- An isolated vertex cannot belong to V_fix^0(G). -/
lemma not_is_fix_v0_of_isolated {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (hiso : G.neighborSet v = ∅) :
    ¬ is_fix_v0 G v := by
  intro hfix
  -- Any edge incident to v is impossible.
  have hv_adj : ∀ w, ¬ G.Adj v w := by
    intro w hw
    have h' : w ∈ G.neighborSet v := (SimpleGraph.mem_neighborSet G v w).mpr hw
    rw [hiso] at h'
    exact h'
  -- The full vertex set is vertex-edge dominating, so gamma_ve is attained.
  have huniv : is_ve_dominating G ((Finset.univ : Finset V) : Set V) := by
    intro x y _
    exact ⟨x, Finset.mem_univ x, Or.inl rfl⟩
  have hne : ({k : ℕ | ∃ S : Finset V, is_ve_dominating G (S : Set V) ∧ S.card = k}).Nonempty := by
    exact ⟨Fintype.card V, Finset.univ, huniv, Finset.card_univ⟩
  obtain ⟨S0, hdom0, hcard0⟩ := Nat.sInf_mem hne
  -- Removing the isolated vertex v preserves vertex-edge domination.
  have hdom_erase : is_ve_dominating G ((S0.erase v : Finset V) : Set V) := by
    intro x y hxy
    obtain ⟨u, huS0, hu⟩ := hdom0 hxy
    have hune : u ≠ v := by
      rintro rfl
      rcases hu with h | h | h | h
      · rw [← h] at hxy
        exact hv_adj y hxy
      · exact hv_adj x h
      · rw [← h] at hxy
        exact hv_adj x hxy.symm
      · exact hv_adj y h
    exact ⟨u, Finset.mem_erase.mpr ⟨hune, huS0⟩, hu⟩
  -- Hence S0.erase v is still a minimum vertex-edge dominating set.
  have hcard_erase_mem :
      (S0.erase v).card ∈ ({k : ℕ | ∃ S : Finset V, is_ve_dominating G (S : Set V) ∧ S.card = k}) :=
    ⟨S0.erase v, hdom_erase, rfl⟩
  have hgamma_le : gamma_ve G ≤ (S0.erase v).card := Nat.sInf_le hcard_erase_mem
  have hle1 : (S0.erase v).card ≤ gamma_ve G := by
    calc (S0.erase v).card ≤ S0.card := Finset.card_erase_le
      _ = gamma_ve G := hcard0
  have hcard_erase_eq : (S0.erase v).card = gamma_ve G := le_antisymm hle1 hgamma_le
  -- But is_fix_v0 demands v lie in every minimum set, contradiction.
  have hmem : v ∈ S0.erase v := hfix.2 (S0.erase v) ⟨hdom_erase, hcard_erase_eq⟩
  exact Finset.notMem_erase v S0 hmem
