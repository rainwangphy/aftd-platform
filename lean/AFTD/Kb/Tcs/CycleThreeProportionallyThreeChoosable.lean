import AFTD.Prelude

/-!
# cycle_three_proportionally_three_choosable

Topic: graphs   Node: aa39abdb789e

Provenance: helper lemma. arXiv:2610.33914 Section 2 (special case n = 3 of OP-593)

The triangle cycle C_3 is proportionally 3-choosable: for every finite color palette α and every assignment L of 3 colors to each vertex, there exists a proper coloring f of C_3 with f(v) ∈ L(v) for all v such that for every color c : α, the number of vertices colored c is either ⌊η_L(c)/3⌋ or ⌈η_L(c)/3⌉, where η_L(c) is the number of vertices whose list contains c.
-/

/-- In a three-element universe, a filtered set has all three elements exactly when its card is three. -/
private lemma cycle_three_proportionally_three_choosable_fin_three_filter_card_eq_three_iff
    {p : Fin 3 → Prop} [DecidablePred p] :
    (Finset.univ.filter p).card = 3 ↔ p 0 ∧ p 1 ∧ p 2 := by
  constructor
  · intro h
    have hs : Finset.univ.filter p = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using h
    have hall : ∀ v : Fin 3, p v := by
      intro v
      have hv : v ∈ Finset.univ.filter p := by
        rw [hs]
        simp
      simpa using hv
    exact ⟨hall 0, hall 1, hall 2⟩
  · rintro ⟨h0, h1, h2⟩
    have hs : Finset.univ.filter p = Finset.univ := by
      ext v
      fin_cases v <;> simp [h0, h1, h2]
    rw [hs]
    simp

/-- From three finite sets of size three one can choose distinct representatives covering their intersection. -/
private lemma cycle_three_proportionally_three_choosable_exists_distinct
    {α : Type} [DecidableEq α] (A B C : Finset α)
    (hA : A.card = 3) (hB : B.card = 3) (hC : C.card = 3) :
    ∃ x y z : α,
      x ∈ A ∧ y ∈ B ∧ z ∈ C ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      ∀ c : α, c ∈ A → c ∈ B → c ∈ C → c = x ∨ c = y ∨ c = z := by
  let U : Finset α := A ∩ B ∩ C
  have hUsubA : U ⊆ A := by
    intro a ha
    simp only [U, Finset.mem_inter] at ha
    exact ha.1.1
  have hUsubB : U ⊆ B := by
    intro a ha
    simp only [U, Finset.mem_inter] at ha
    exact ha.1.2
  have hUsubC : U ⊆ C := by
    intro a ha
    simp only [U, Finset.mem_inter] at ha
    exact ha.2
  have hUcard : U.card ≤ 3 := by
    calc U.card ≤ A.card := Finset.card_le_card hUsubA
      _ = 3 := hA
  have hx_exists : ∃ x, x ∈ A ∧ (U.Nonempty → x ∈ U) := by
    by_cases hUne : U.Nonempty
    · obtain ⟨x, hxU⟩ := hUne.exists_mem
      exact ⟨x, hUsubA hxU, fun _ => hxU⟩
    · have hApos : 0 < A.card := by omega
      obtain ⟨x, hxA⟩ := Finset.card_pos.mp hApos
      exact ⟨x, hxA, fun h => (hUne h).elim⟩
  obtain ⟨x, hxA, hxUcond⟩ := hx_exists
  have hy_base : (B \ {x}).Nonempty := by
    have hle := Finset.le_card_sdiff ({x} : Finset α) B
    rw [Finset.card_singleton, hB] at hle
    have hpos : 0 < (B \ {x}).card := by omega
    exact Finset.card_pos.mp hpos
  have hy_exists : ∃ y, y ∈ B ∧ y ≠ x ∧ ((U.erase x).Nonempty → y ∈ U.erase x) := by
    by_cases hUx : (U.erase x).Nonempty
    · obtain ⟨y, hyUx⟩ := hUx.exists_mem
      exact ⟨y, hUsubB (Finset.mem_of_mem_erase hyUx), Finset.ne_of_mem_erase hyUx,
        fun _ => hyUx⟩
    · obtain ⟨y, hyBdiff⟩ := hy_base
      rw [Finset.mem_sdiff] at hyBdiff
      exact ⟨y, hyBdiff.1, by simpa using hyBdiff.2, fun h => (hUx h).elim⟩
  obtain ⟨y, hyB, hyx, hyUcond⟩ := hy_exists
  have hxy : x ≠ y := hyx.symm
  have hz_base : (C \ ({x, y} : Finset α)).Nonempty := by
    have hle := Finset.le_card_sdiff ({x, y} : Finset α) C
    rw [Finset.card_pair hxy, hC] at hle
    have hpos : 0 < (C \ ({x, y} : Finset α)).card := by omega
    exact Finset.card_pos.mp hpos
  have hz_exists : ∃ z, z ∈ C ∧ z ≠ x ∧ z ≠ y ∧
      ((U \ ({x, y} : Finset α)).Nonempty → z ∈ U \ ({x, y} : Finset α)) := by
    by_cases hUxy : (U \ ({x, y} : Finset α)).Nonempty
    · obtain ⟨z, hzUxy⟩ := hUxy.exists_mem
      rw [Finset.mem_sdiff] at hzUxy
      have hzx : z ≠ x := by
        intro hzx
        exact hzUxy.2 (by simp [hzx])
      have hzy : z ≠ y := by
        intro hzy
        exact hzUxy.2 (by simp [hzy])
      exact ⟨z, hUsubC hzUxy.1, hzx, hzy, fun _ => by
        rw [Finset.mem_sdiff]
        exact hzUxy⟩
    · obtain ⟨z, hzCdiff⟩ := hz_base
      rw [Finset.mem_sdiff] at hzCdiff
      have hzx : z ≠ x := by
        intro hzx
        exact hzCdiff.2 (by simp [hzx])
      have hzy : z ≠ y := by
        intro hzy
        exact hzCdiff.2 (by simp [hzy])
      exact ⟨z, hzCdiff.1, hzx, hzy, fun h => (hUxy h).elim⟩
  obtain ⟨z, hzC, hzx, hzy, hzUcond⟩ := hz_exists
  have hxz : x ≠ z := hzx.symm
  have hyz : y ≠ z := hzy.symm
  have hcard3 : ({x, y, z} : Finset α).card = 3 := by
    exact Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  refine ⟨x, y, z, hxA, hyB, hzC, hxy, hxz, hyz, ?_⟩
  intro c hcA hcB hcC
  have hcU : c ∈ U := by
    simp only [U, Finset.mem_inter]
    exact ⟨⟨hcA, hcB⟩, hcC⟩
  by_cases hcx : c = x
  · exact Or.inl hcx
  · by_cases hcy : c = y
    · exact Or.inr (Or.inl hcy)
    · right; right
      by_contra hcz
      have hUxne : (U.erase x).Nonempty :=
        ⟨c, Finset.mem_erase.mpr ⟨hcx, hcU⟩⟩
      have hyUx := hyUcond hUxne
      have hyU : y ∈ U := Finset.mem_of_mem_erase hyUx
      have hcnotxy : c ∉ ({x, y} : Finset α) := by simp [hcx, hcy]
      have hUxyne : (U \ ({x, y} : Finset α)).Nonempty :=
        ⟨c, Finset.mem_sdiff.mpr ⟨hcU, hcnotxy⟩⟩
      have hzUxy := hzUcond hUxyne
      have hzU : z ∈ U := (Finset.mem_sdiff.mp hzUxy).1
      have hxU : x ∈ U := hxUcond ⟨c, hcU⟩
      have hsub : ({x, y, z} : Finset α) ⊆ U := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl
        · exact hxU
        · exact hyU
        · exact hzU
      have hcnot : c ∉ ({x, y, z} : Finset α) := by simp [hcx, hcy, hcz]
      have hssub : ({x, y, z} : Finset α) ⊂ U :=
        (Finset.ssubset_iff_of_subset hsub).mpr ⟨c, hcU, hcnot⟩
      have hlt := Finset.card_lt_card hssub
      rw [hcard3] at hlt
      omega

/-- A triangle can be properly colored by any three pairwise distinct colors. -/
private lemma cycle_three_proportionally_three_choosable_cycle_three_coloring_of_distinct
    {α : Type} (x y z : α)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ f : (SimpleGraph.cycleGraph 3).Coloring α,
      f 0 = x ∧ f 1 = y ∧ f 2 = z := by
  refine ⟨SimpleGraph.Coloring.mk (![x, y, z] : Fin 3 → α) ?_, ?_, ?_, ?_⟩
  · intro v w h
    rw [SimpleGraph.cycleGraph_three_eq_top] at h
    fin_cases v <;> fin_cases w <;> simp_all [Ne.symm]
  · rfl
  · rfl
  · rfl

/-- The ceiling division of a positive natural at most three by three is one. -/
private lemma cycle_three_proportionally_three_choosable_ceilDiv_three_eq_one
    {n : ℕ} (h0 : 0 < n) (h3 : n ≤ 3) : n ⌈/⌉ 3 = 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  interval_cases n <;> norm_num

/-- The triangle cycle C_3 is proportionally 3-choosable (special case n = 3 of OP-593). -/
theorem cycle_three_proportionally_three_choosable :
    ∀ (α : Type) [Fintype α] [DecidableEq α] (L : Fin 3 → Finset α),
      (∀ v, (L v).card = 3) →
      ∃ f : (SimpleGraph.cycleGraph 3).Coloring α,
        (∀ v, f v ∈ L v) ∧
        ∀ c : α,
          let η := (Finset.univ.filter (fun v => c ∈ L v)).card
          let uses := (Finset.univ.filter (fun v => f v = c)).card
          uses = η / 3 ∨ uses = η ⌈/⌉ 3 := by
  intro α _ _ L hL
  obtain ⟨x, y, z, hxA, hyB, hzC, hxy, hxz, hyz, hcover⟩ :=
    cycle_three_proportionally_three_choosable_exists_distinct (L 0) (L 1) (L 2)
      (hL 0) (hL 1) (hL 2)
  obtain ⟨f, hf0, hf1, hf2⟩ :=
    cycle_three_proportionally_three_choosable_cycle_three_coloring_of_distinct x y z hxy hxz hyz
  refine ⟨f, ?_, ?_⟩
  · intro v
    fin_cases v
    · simpa [hf0] using hxA
    · simpa [hf1] using hyB
    · simpa [hf2] using hzC
  · intro c
    dsimp only
    set η : ℕ := (Finset.univ.filter (fun v : Fin 3 => c ∈ L v)).card with hηdef
    set uses : ℕ := (Finset.univ.filter (fun v : Fin 3 => f v = c)).card with husesdef
    change uses = η / 3 ∨ uses = η ⌈/⌉ 3
    have hηle : η ≤ 3 := by
      rw [hηdef]
      simpa using Finset.card_le_univ (Finset.univ.filter (fun v : Fin 3 => c ∈ L v))
    have hη_three_imp : η = 3 → c ∈ L 0 ∧ c ∈ L 1 ∧ c ∈ L 2 := by
      intro hη3
      have hcard : (Finset.univ.filter (fun v : Fin 3 => c ∈ L v)).card = 3 := by
        rw [hηdef] at hη3
        exact hη3
      exact (cycle_three_proportionally_three_choosable_fin_three_filter_card_eq_three_iff
        (p := fun v : Fin 3 => c ∈ L v)).mp hcard
    have huse_x : (Finset.univ.filter (fun v : Fin 3 => f v = x)).card = 1 := by
      rw [show (Finset.univ.filter (fun v : Fin 3 => f v = x)) = {0} by
        ext v
        fin_cases v <;> simp [hf0, hf1, hf2, Ne.symm hxy, Ne.symm hxz]]
      simp
    have huse_y : (Finset.univ.filter (fun v : Fin 3 => f v = y)).card = 1 := by
      rw [show (Finset.univ.filter (fun v : Fin 3 => f v = y)) = {1} by
        ext v
        fin_cases v <;> simp [hf0, hf1, hf2, hxy, Ne.symm hyz]]
      simp
    have huse_z : (Finset.univ.filter (fun v : Fin 3 => f v = z)).card = 1 := by
      rw [show (Finset.univ.filter (fun v : Fin 3 => f v = z)) = {2} by
        ext v
        fin_cases v <;> simp [hf0, hf1, hf2, hxz, hyz]]
      simp
    by_cases hcx : c = x
    · subst c
      have huse : uses = 1 := by
        rw [husesdef]
        exact huse_x
      have hηpos : 0 < η := by
        rw [hηdef]
        apply Finset.card_pos.mpr
        exact ⟨0, by simp [hxA]⟩
      have hceil : η ⌈/⌉ 3 = 1 :=
        cycle_three_proportionally_three_choosable_ceilDiv_three_eq_one hηpos hηle
      right
      rw [huse, hceil]
    · by_cases hcy : c = y
      · subst c
        have huse : uses = 1 := by
          rw [husesdef]
          exact huse_y
        have hηpos : 0 < η := by
          rw [hηdef]
          apply Finset.card_pos.mpr
          exact ⟨1, by simp [hyB]⟩
        have hceil : η ⌈/⌉ 3 = 1 :=
          cycle_three_proportionally_three_choosable_ceilDiv_three_eq_one hηpos hηle
        right
        rw [huse, hceil]
      · by_cases hcz : c = z
        · subst c
          have huse : uses = 1 := by
            rw [husesdef]
            exact huse_z
          have hηpos : 0 < η := by
            rw [hηdef]
            apply Finset.card_pos.mpr
            exact ⟨2, by simp [hzC]⟩
          have hceil : η ⌈/⌉ 3 = 1 :=
            cycle_three_proportionally_three_choosable_ceilDiv_three_eq_one hηpos hηle
          right
          rw [huse, hceil]
        · have huse : uses = 0 := by
            rw [husesdef, Finset.card_eq_zero]
            apply Finset.filter_false_of_mem
            intro v _
            fin_cases v <;> simp [hf0, hf1, hf2, Ne.symm hcx, Ne.symm hcy, Ne.symm hcz]
          have hηlt3 : η < 3 := by
            by_contra hnot
            have hη3 : η = 3 := by omega
            have huniv := hη_three_imp hη3
            rcases hcover c huniv.1 huniv.2.1 huniv.2.2 with hcx' | hcy' | hcz'
            · exact hcx hcx'
            · exact hcy hcy'
            · exact hcz hcz'
          have hηdiv : η / 3 = 0 := Nat.div_eq_of_lt hηlt3
          left
          rw [huse, hηdiv]
