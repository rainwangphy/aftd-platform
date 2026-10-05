import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAbLinked
import AFTD.Kb.GameTheoryEconomics.Poc8CoverCheck
import AFTD.Kb.GameTheoryEconomics.Poc8CoverOk
import AFTD.Kb.GameTheoryEconomics.Poc8CandsConn
import AFTD.Kb.GameTheoryEconomics.Poc8ConnbSound
import AFTD.Kb.GameTheoryEconomics.Poc8Graph

/-!
# poc8_linked_two_three

Topic: fair_division   Node: 3daa547f2c92

The 8-vertex graph G is (2,3)-linked: any 2 terminals and 3 further terminals are separated by a connected bipartition of G.
-/

theorem poc8_linked_two_three : is_ab_linked poc8_graph 2 3 := by
  intro M1 M2 hdisj h1 h2
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h1
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h2
  have hxa : x ≠ a := fun h =>
    Finset.disjoint_left.mp hdisj (show x ∈ ({x, y} : Finset (Fin 8)) by simp) (by simp [h])
  have hxb : x ≠ b := fun h =>
    Finset.disjoint_left.mp hdisj (show x ∈ ({x, y} : Finset (Fin 8)) by simp) (by simp [h])
  have hxc : x ≠ c := fun h =>
    Finset.disjoint_left.mp hdisj (show x ∈ ({x, y} : Finset (Fin 8)) by simp) (by simp [h])
  have hya : y ≠ a := fun h =>
    Finset.disjoint_left.mp hdisj (show y ∈ ({x, y} : Finset (Fin 8)) by simp) (by simp [h])
  have hyb : y ≠ b := fun h =>
    Finset.disjoint_left.mp hdisj (show y ∈ ({x, y} : Finset (Fin 8)) by simp) (by simp [h])
  have hyc : y ≠ c := fun h =>
    Finset.disjoint_left.mp hdisj (show y ∈ ({x, y} : Finset (Fin 8)) by simp) (by simp [h])
  have hc := poc8_cover_check x y a b c
  have e_hxy : (x == y) = false := by simp [hxy]
  have e_hab : (a == b) = false := by simp [hab]
  have e_hac : (a == c) = false := by simp [hac]
  have e_hbc : (b == c) = false := by simp [hbc]
  have e_hxa : (x == a) = false := by simp [hxa]
  have e_hxb : (x == b) = false := by simp [hxb]
  have e_hxc : (x == c) = false := by simp [hxc]
  have e_hya : (y == a) = false := by simp [hya]
  have e_hyb : (y == b) = false := by simp [hyb]
  have e_hyc : (y == c) = false := by simp [hyc]
  unfold poc8_cover_ok at hc
  rw [e_hxy, e_hab, e_hac, e_hbc, e_hxa, e_hxb, e_hxc, e_hya, e_hyb, e_hyc] at hc
  simp only [Bool.false_or, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨m, hm, ⟨⟨⟨⟨hmx, hmy⟩, hma⟩, hmb⟩, hmc⟩⟩ := hc
  obtain ⟨hc1, hc2⟩ := poc8_cands_conn m hm
  refine ⟨{v | m.testBit v = true}, {v | (!m.testBit v) = true}, ?_, ?_, ?_,
    poc8_connb_sound _ hc1, poc8_connb_sound _ hc2⟩
  · rw [Set.disjoint_left]
    intro v h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    rw [h1] at h2
    exact absurd h2 (by decide)
  · intro v hv
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hmx
    · exact hmy
  · intro v hv
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · simp [hma]
    · simp [hmb]
    · simp [hmc]
