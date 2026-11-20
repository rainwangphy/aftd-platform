import AFTD.Prelude
import AFTD.Kb.Tcs.FactorcriticalCrossingEvenShoreCoversOppositeFirstSide
import AFTD.Kb.Tcs.FactorcriticalCodegreeTwoBridgeShoreForcesSingletonFirstSide
import AFTD.Kb.Tcs.BoundedDegreeHubUniqueExternalNeighbor
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# factorcritical_first_bridge_at_most_one_codegree_two_endpoint

Topic: graphs   Node: 427a877f7416

Provenance: helper lemma. OP-1957 equality-twin branch: factor-critical crossing cuts and saturated hub degree budget.

For saturated complement twins and a factor-critical graph with the stated first bridge partition, at most one external endpoint of complement codegree at most two can have a matching-compatible second bridge-shore certificate.
-/

theorem factorcritical_first_bridge_at_most_one_codegree_two_endpoint (k d : ℕ) (H : SimpleGraph (Fin (2*k+d+3))) [DecidableRel H.Adj]
    (hcrit : is_k_factor_critical Hᶜ (2*k)) (x y u v : Fin (2*k+d+3))
    (hxy : H.Adj x y) (hxdeg : (H.neighborFinset x).card = d)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (htwin : ∀ a, a ≠ x → a ≠ y → (H.Adj x a ↔ H.Adj y a))
    (huv : ¬ H.Adj u v) (hcommon : ∀ a, H.Adj u a → H.Adj v a → a = x ∨ a = y)
    (A B : Finset (Fin (2*k+d+3))) (hAB : Disjoint A B)
    (hS : A ∪ B = (H.neighborFinset x).erase y) (hu : u ∈ A) (hv : v ∈ B)
    (hAodd : Odd A.card) (hBodd : Odd B.card)
    (hcut : ∀ a ∈ A, ∀ b ∈ B, (a ≠ u ∨ b ≠ v) → H.Adj a b) :
    let eligible := fun z => z ≠ x ∧ ¬ H.Adj x z ∧
      ((Finset.univ : Finset (Fin (2*k+d+3))).filter (fun a => H.Adj x a ∧ H.Adj z a)).card ≤ 2 ∧
      ∃ Q W : Finset (Fin (2*k+d+3)), x ∉ Q ∧ y ∉ Q ∧ W ⊆ A ∪ B ∧ W.Nonempty ∧ Q.Nonempty ∧
        Even (W ∩ A).card ∧ Even (W ∩ B).card ∧ Q.card + W.card = d+1 ∧
        (∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) ∧ (∀ q ∈ Q, H.Adj z q)
    ∀ z₁ z₂, eligible z₁ → eligible z₂ → z₁ = z₂ := by
  classical
  dsimp only
  let S := (H.neighborFinset x).erase y
  have hS' : A ∪ B = S := hS
  have hxS : x ∉ S := by
    dsimp [S]
    simp [SimpleGraph.mem_neighborFinset]
  have hyS : y ∉ S := by simp [S]
  have hxAB : x ∉ A ∪ B := by rw [hS']; exact hxS
  have hyAB : y ∉ A ∪ B := by rw [hS']; exact hyS
  have huS : u ∈ S := by rw [←hS']; exact Finset.mem_union_left B hu
  have hvS : v ∈ S := by rw [←hS']; exact Finset.mem_union_right A hv
  have huvne : u ≠ v := by
    intro h; subst v
    exact (Finset.disjoint_left.mp hAB) hu hv
  have hxyne := hxy.ne
  have hyN : y ∈ H.neighborFinset x := (H.mem_neighborFinset x y).mpr hxy
  have hScard : S.card + 1 = d := by
    have hpos : 0 < (H.neighborFinset x).card := Finset.card_pos.mpr ⟨y,hyN⟩
    rw [hxdeg] at hpos
    dsimp [S]
    rw [Finset.card_erase_of_mem hyN, hxdeg]
    omega
  have hxhub : ∀ a ∈ S, H.Adj x a := by
    intro a ha
    exact (H.mem_neighborFinset x a).mp (Finset.mem_of_mem_erase ha)
  have hyhub : ∀ a ∈ S, H.Adj y a := by
    intro a ha
    have hax : a ≠ x := by intro h; subst a; exact hxS ha
    have hay : a ≠ y := by intro h; subst a; exact hyS ha
    exact (htwin a hax hay).mp (hxhub a ha)
  have hxyW : ∀ W, W ⊆ A ∪ B → ∀ w ∈ W, H.Adj x w ∧ H.Adj y w := by
    intro W hW w hw
    have hwS : w ∈ S := by rw [←hS']; exact hW hw
    exact ⟨hxhub w hwS,hyhub w hwS⟩
  have hcut' : ∀ b ∈ B, ∀ a ∈ A, (b ≠ v ∨ a ≠ u) → H.Adj b a := by
    intro b hb a ha h
    apply (hcut a ha b hb ?_).symm
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hhub : ∀ (A' B' Q W : Finset (Fin (2*k+d+3))) (hub other z : Fin (2*k+d+3)),
      Disjoint A' B' → x ∉ A' ∪ B' → y ∉ A' ∪ B' → x ∉ Q → y ∉ Q →
      hub ∈ A' → other ∈ B' → A'.card = 1 →
      (∀ a ∈ A', ∀ b ∈ B', (a ≠ hub ∨ b ≠ other) → H.Adj a b) →
      W ⊆ A' ∪ B' → W.Nonempty → Even (W ∩ A').card → Even (W ∩ B').card →
      Q.card + W.card = d+1 → (∀ w ∈ W, H.Adj x w ∧ H.Adj y w) →
      (∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) → (∀ q ∈ Q, H.Adj z q) → H.Adj hub z := by
    intro A' B' Q W hub other z hdj hx' hy' hqx hqy hh ho hcard hcut0 hW hWne heA heB hsz hxy0 hcross hqz
    have hAeq : A' = {hub} := by
      obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hcard
      have haeq : a = hub := by
        rw [ha] at hh
        have h : hub = a := by simpa using hh
        exact h.symm
      simpa [haeq] using ha
    have hhubW : hub ∉ W := by
      intro h
      have heq : W ∩ A' = {hub} := by rw [hAeq]; simp [h]
      rw [heq] at heA
      norm_num at heA
    have hWB : (W ∩ B').Nonempty := by
      obtain ⟨w,hw⟩ := hWne
      rcases Finset.mem_union.mp (hW hw) with ha | hb
      · rw [hAeq] at ha
        simp only [Finset.mem_singleton] at ha
        subst w
        exact (hhubW hw).elim
      · exact ⟨w,Finset.mem_inter.mpr ⟨hw,hb⟩⟩
    have hcut0' : ∀ b ∈ B', ∀ a ∈ A', (b ≠ other ∨ a ≠ hub) → H.Adj b a := by
      intro b hb a ha h
      apply (hcut0 a ha b hb ?_).symm
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl h
    have hcover := factorcritical_crossing_even_shore_covers_opposite_first_side k d H hcrit x y other hub hxyne B' A' Q W hdj.symm
      (by simpa [Finset.union_comm] using hx') (by simpa [Finset.union_comm] using hy')
      hqx hqy ho hh hcut0' (by simpa [Finset.union_comm] using hW) heB hWB hsz hxy0 hcross
    have hQ : hub ∈ Q := by
      rcases Finset.mem_union.mp (hcover hh) with h | h
      · exact (hhubW h).elim
      · exact h
    exact (hqz hub hQ).symm
  intro z₁ z₂ hz₁ hz₂
  rcases hz₁ with ⟨hz₁x,hz₁not,hz₁co,Q₁,W₁,hq₁x,hq₁y,hw₁,hw₁ne,hq₁ne,he₁A,he₁B,hsz₁,hcr₁,hqz₁⟩
  rcases hz₂ with ⟨hz₂x,hz₂not,hz₂co,Q₂,W₂,hq₂x,hq₂y,hw₂,hw₂ne,hq₂ne,he₂A,he₂B,hsz₂,hcr₂,hqz₂⟩
  have hz₁S : z₁ ∉ S := by intro h; exact hz₁not (hxhub z₁ h)
  have hz₂S : z₂ ∉ S := by intro h; exact hz₂not (hxhub z₂ h)
  have hz₁y : z₁ ≠ y := by intro h; subst z₁; exact hz₁not hxy
  have hz₂y : z₂ ≠ y := by intro h; subst z₂; exact hz₂not hxy
  have hone := factorcritical_codegree_two_bridge_shore_forces_singleton_first_side k d H hcrit x y u v z₁ hxyne huv hcommon A B Q₁ W₁ hAB hxAB hyAB hq₁x hq₁y hu hv hcut hw₁ hw₁ne hq₁ne hAodd hBodd he₁A he₁B hsz₁ (hxyW W₁ hw₁) (by intro a ha; exact hxhub a (by rw [←hS']; exact ha)) hcr₁ hqz₁ hz₁co
  rcases hone with hAone | hBone
  · have hadj₁ : H.Adj u z₁ := hhub A B Q₁ W₁ u v z₁ hAB hxAB hyAB hq₁x hq₁y hu hv hAone hcut hw₁ hw₁ne he₁A he₁B hsz₁ (hxyW W₁ hw₁) hcr₁ hqz₁
    have hadj₂ : H.Adj u z₂ := hhub A B Q₂ W₂ u v z₂ hAB hxAB hyAB hq₂x hq₂y hu hv hAone hcut hw₂ hw₂ne he₂A he₂B hsz₂ (hxyW W₂ hw₂) hcr₂ hqz₂
    have hAeq : A = {u} := by
      obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hAone
      have haeq : a = u := by
        rw [ha] at hu
        have h : u = a := by simpa using hu
        exact h.symm
      simpa [haeq] using ha
    have hstar : ∀ a ∈ S, a ≠ u → a ≠ v → H.Adj u a := by
      intro a ha hau hav
      have haAB : a ∈ A ∪ B := by rw [hS']; exact ha
      rcases Finset.mem_union.mp haAB with haA | haB
      · rw [hAeq] at haA; simp only [Finset.mem_singleton] at haA; exact (hau haA).elim
      · exact hcut u hu a haB (Or.inr hav)
    exact bounded_degree_hub_unique_external_neighbor H d x y u v S hxyne hxS hyS huS hvS huvne hScard (hxhub u huS).symm (hyhub u huS).symm (hmax u) hstar z₁ z₂ hz₁S hz₂S hz₁x hz₁y hz₂x hz₂y hadj₁ hadj₂
  · have hadj₁ : H.Adj v z₁ := hhub B A Q₁ W₁ v u z₁ hAB.symm (by simpa [Finset.union_comm] using hxAB) (by simpa [Finset.union_comm] using hyAB) hq₁x hq₁y hv hu hBone hcut' (by simpa [Finset.union_comm] using hw₁) hw₁ne he₁B he₁A hsz₁ (hxyW W₁ hw₁) hcr₁ hqz₁
    have hadj₂ : H.Adj v z₂ := hhub B A Q₂ W₂ v u z₂ hAB.symm (by simpa [Finset.union_comm] using hxAB) (by simpa [Finset.union_comm] using hyAB) hq₂x hq₂y hv hu hBone hcut' (by simpa [Finset.union_comm] using hw₂) hw₂ne he₂B he₂A hsz₂ (hxyW W₂ hw₂) hcr₂ hqz₂
    have hBeq : B = {v} := by
      obtain ⟨b,hb⟩ := Finset.card_eq_one.mp hBone
      have hbeq : b = v := by
        rw [hb] at hv
        have h : v = b := by simpa using hv
        exact h.symm
      simpa [hbeq] using hb
    have hstar : ∀ a ∈ S, a ≠ v → a ≠ u → H.Adj v a := by
      intro a ha hav hau
      have haAB : a ∈ A ∪ B := by rw [hS']; exact ha
      rcases Finset.mem_union.mp haAB with haA | haB
      · exact (hcut a haA v hv (Or.inl hau)).symm
      · rw [hBeq] at haB; simp only [Finset.mem_singleton] at haB; exact (hav haB).elim
    exact bounded_degree_hub_unique_external_neighbor H d x y v u S hxyne hxS hyS hvS huS huvne.symm hScard (hxhub v hvS).symm (hyhub v hvS).symm (hmax v) hstar z₁ z₂ hz₁S hz₂S hz₁x hz₁y hz₂x hz₂y hadj₁ hadj₂
