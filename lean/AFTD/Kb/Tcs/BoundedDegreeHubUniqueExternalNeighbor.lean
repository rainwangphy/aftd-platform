import AFTD.Prelude

/-!
# bounded_degree_hub_unique_external_neighbor

Topic: graphs   Node: 86059f507b00

Provenance: helper lemma. OP-1957 saturated singleton hub degree count.

If a vertex of degree at most d has x,y and all but two members of a (d−1)-element set as neighbors, it has at most one neighbor outside that set and x,y.
-/

theorem bounded_degree_hub_unique_external_neighbor {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (d : ℕ) (x y u v : V) (S : Finset V)
    (hxy : x ≠ y) (hxu : x ∉ S) (hyu : y ∉ S)
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) (hS : S.card + 1 = d)
    (hx : H.Adj u x) (hy : H.Adj u y) (hmax : (H.neighborFinset u).card ≤ d)
    (hstar : ∀ a ∈ S, a ≠ u → a ≠ v → H.Adj u a)
    (z₁ z₂ : V) (hz₁ : z₁ ∉ S) (hz₂ : z₂ ∉ S) (hz₁x : z₁ ≠ x) (hz₁y : z₁ ≠ y)
    (hz₂x : z₂ ≠ x) (hz₂y : z₂ ≠ y) (huz₁ : H.Adj u z₁) (huz₂ : H.Adj u z₂) : z₁ = z₂ := by
  classical
  by_contra hzz
  let T := (S.erase u).erase v
  have hvT : v ∈ S.erase u := Finset.mem_erase.mpr ⟨huv.symm,hv⟩
  have hS2 : 2 ≤ S.card := by
    have hpair : ({u,v} : Finset V) ⊆ S := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hu
      · exact hv
    have hc := Finset.card_le_card hpair
    rw [Finset.card_pair huv] at hc
    exact hc
  have hTcard : T.card + 3 = d := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hvT, Finset.card_erase_of_mem hu]
    omega
  have hTsub : T ⊆ S := fun a ha => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha)
  have hxT : x ∉ T := fun h => hxu (hTsub h)
  have hyT : y ∉ T := fun h => hyu (hTsub h)
  have hz₁T : z₁ ∉ T := fun h => hz₁ (hTsub h)
  have hz₂T : z₂ ∉ T := fun h => hz₂ (hTsub h)
  let F := insert x (insert y T)
  have hxF : x ∉ insert y T := by simp [hxy,hxT]
  have hFcard : F.card + 1 = d := by
    dsimp [F]
    rw [Finset.card_insert_of_notMem hxF, Finset.card_insert_of_notMem hyT]
    omega
  have hz₁F : z₁ ∉ F := by simp [F,hz₁x,hz₁y,hz₁T]
  have hz₂F : z₂ ∉ F := by simp [F,hz₂x,hz₂y,hz₂T]
  have hsub : insert z₁ (insert z₂ F) ⊆ H.neighborFinset u := by
    intro a ha
    simp only [Finset.mem_insert] at ha
    rw [H.mem_neighborFinset]
    rcases ha with rfl | rfl | ha
    · exact huz₁
    · exact huz₂
    · dsimp [F] at ha
      simp only [Finset.mem_insert] at ha
      rcases ha with rfl | rfl | ha
      · exact hx
      · exact hy
      · have hs : a ∈ S := hTsub ha
        have hne_v : a ≠ v := Finset.ne_of_mem_erase ha
        have hne_u : a ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ha)
        exact hstar a hs hne_u hne_v
  have hz₁not : z₁ ∉ insert z₂ F := by simp [hzz,hz₁F]
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hz₁not, Finset.card_insert_of_notMem hz₂F] at hc
  omega
