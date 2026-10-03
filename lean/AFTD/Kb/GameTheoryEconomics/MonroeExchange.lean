import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsHareValidAssignment
import AFTD.Kb.GameTheoryEconomics.MonroeScore
import AFTD.Kb.GameTheoryEconomics.MonroeLoadCompPerm
import AFTD.Kb.GameTheoryEconomics.AssignmentExchange

/-!
# monroe_exchange

Topic: social_choice   Node: 223276faa4fe

Exchange step: replacing c ∈ W by c ∉ W approved by all of S (no member of S being satisfied by π) yields a Hare-valid assignment whose score is at least score(π) + min(|π⁻¹(c)|, |S|) - |π⁻¹(c) \ S|.
-/

/-- The exchange step: swapping `c ∈ W` for a candidate `c' ∉ W` approved by everyone in `S` (and with no member of `S` satisfied by `π`) gives a valid assignment whose score is at least `score π + min(|π⁻¹(c)|, |S|) - |π⁻¹(c) \ S|`. -/
theorem monroe_exchange {n m : ℕ} (A : Fin n → Finset (Fin m)) (k : ℕ) (W : Finset (Fin m))
    (π : Fin n → Fin m) (hv : is_hare_valid_assignment k W π) (c c' : Fin m) (hc : c ∈ W)
    (hc' : c' ∉ W) (S : Finset (Fin n)) (hSa : ∀ i ∈ S, c' ∈ A i)
    (hun : ∀ i ∈ S, π i ∉ A i) :
    ∃ π', is_hare_valid_assignment k (insert c' (W.erase c)) π' ∧
      monroe_score A π + min (Finset.univ.filter fun i => π i = c).card S.card ≤
        monroe_score A π' + ((Finset.univ.filter fun i => π i = c).filter fun i => i ∉ S).card := by
  obtain ⟨σ, hσ⟩ := assignment_exchange (fun i b => b ∈ A i) π c c' S hSa hun
  obtain ⟨hW, hmap, hload⟩ := hv
  let ρ : Fin m → Fin m := fun x => if x = c then c' else x
  have hπc' : ∀ v, π v ≠ c' := fun v h => hc' (h ▸ hmap v)
  refine ⟨fun v => ρ (π (σ v)), ⟨?_, ?_, ?_⟩, hσ⟩
  · have : c' ∉ W.erase c := fun h => hc' (Finset.mem_of_mem_erase h)
    rw [Finset.card_insert_of_notMem this, Finset.card_erase_of_mem hc, hW]
    have : 0 < k := hW ▸ Finset.card_pos.2 ⟨c, hc⟩
    omega
  · intro v
    simp only [ρ]
    split_ifs with h
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h, hmap _⟩)
  · intro d hd
    have key : ∃ e ∈ W, (Finset.univ.filter fun v => ρ (π (σ v)) = d) =
        (Finset.univ.filter fun v => π (σ v) = e) := by
      rcases Finset.mem_insert.1 hd with rfl | hd
      · refine ⟨c, hc, Finset.filter_congr fun v _ => ?_⟩
        simp only [ρ]
        split_ifs with h
        · simp [h]
        · simp [h, hπc']
      · obtain ⟨hdc, hdW⟩ := Finset.mem_erase.1 hd
        refine ⟨d, hdW, Finset.filter_congr fun v _ => ?_⟩
        simp only [ρ]
        split_ifs with h
        · constructor
          · intro h'; exact absurd (h' ▸ hdW) hc'
          · intro h'; exact absurd (h.symm.trans h') (Ne.symm hdc)
        · rfl
    obtain ⟨e, he, heq⟩ := key
    rw [heq, monroe_load_comp_perm]
    exact hload e he
