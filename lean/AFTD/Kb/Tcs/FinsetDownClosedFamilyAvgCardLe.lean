import AFTD.Prelude

/-!
# finset_down_closed_family_avg_card_le

Topic: graphs   Node: f3a48ffe02ff

Provenance: helper lemma. arXiv:2610.11446 (On the local average order of dominating sets), Lemma 2.1 (quoted there from earlier work on the average order of dominating sets, Proposition 2.3), serving Theorem 2.2.

A nonempty downward-closed family I of subsets of a finite set X has average set size at most |X|/2, with equality exactly when I is the whole power set of X.
-/

theorem finset_down_closed_family_avg_card_le {α : Type*} [DecidableEq α] (X : Finset α)
    (I : Finset (Finset α)) (hI : I.Nonempty) (hsub : ∀ S ∈ I, S ⊆ X)
    (hdown : ∀ S ∈ I, ∀ T ⊆ S, T ∈ I) :
    (∑ S ∈ I, (S.card : ℚ)) / I.card ≤ (X.card : ℚ) / 2 ∧
      ((∑ S ∈ I, (S.card : ℚ)) / I.card = (X.card : ℚ) / 2 ↔ I = X.powerset) := by
  classical
  -- `a x` members containing `x`, `b x` members avoiding `x`
  set a : α → ℕ := fun x => (I.filter (fun S => x ∈ S)).card with ha
  set b : α → ℕ := fun x => (I.filter (fun S => x ∉ S)).card with hb
  have hab : ∀ x, a x + b x = I.card := fun x =>
    Finset.card_filter_add_card_filter_not _
  have hsum : ∑ S ∈ I, S.card = ∑ x ∈ X, a x := by
    have h : ∀ S ∈ I, S.card = ∑ x ∈ X, if x ∈ S then 1 else 0 := by
      intro S hS
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.2 (hsub S hS)]
    rw [Finset.sum_congr rfl h, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [ha]; rw [Finset.card_filter]
  -- deleting `x` is injective on the members containing `x`
  have erase_inj : ∀ x, Set.InjOn (fun S : Finset α => S.erase x)
      ↑(I.filter (fun S => x ∈ S)) := by
    intro x S hS T hT h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hS hT
    rw [← Finset.insert_erase hS.2, ← Finset.insert_erase hT.2]
    exact congrArg (insert x) h
  have erase_maps : ∀ x, ∀ S ∈ I.filter (fun S => x ∈ S), S.erase x ∈ I.filter (fun S => x ∉ S) := by
    intro x S hS
    rw [Finset.mem_filter] at hS ⊢
    exact ⟨hdown S hS.1 _ (Finset.erase_subset x S), by simp⟩
  have hle : ∀ x, a x ≤ b x := by
    intro x
    simp only [ha, hb]; rw [← Finset.card_image_of_injOn (erase_inj x)]
    apply Finset.card_le_card
    intro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
    exact erase_maps x S hS
  -- with insertion also closed, the two counts agree
  have hge : (∀ S ∈ I, ∀ x ∈ X, x ∉ S → insert x S ∈ I) → ∀ x ∈ X, b x ≤ a x := by
    intro hup x hx
    have inj : Set.InjOn (fun S : Finset α => insert x S) ↑(I.filter (fun S => x ∉ S)) := by
      intro S hS T hT h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hS hT
      rw [← Finset.erase_insert hS.2, ← Finset.erase_insert hT.2]
      exact congrArg (fun U => Finset.erase U x) h
    simp only [ha, hb]; rw [← Finset.card_image_of_injOn inj]
    apply Finset.card_le_card
    intro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
    rw [Finset.mem_filter] at hS ⊢
    exact ⟨hup S hS.1 x hx hS.2, Finset.mem_insert_self x S⟩
  have htot : ∑ x ∈ X, (a x + b x) = X.card * I.card := by
    rw [Finset.sum_congr rfl fun x _ => hab x, Finset.sum_const, smul_eq_mul]
  have hIpos : (0 : ℚ) < I.card := by exact_mod_cast hI.card_pos
  have havg : (∑ S ∈ I, (S.card : ℚ)) / I.card = ((∑ x ∈ X, a x : ℕ) : ℚ) / I.card := by
    rw [← hsum, Nat.cast_sum]
  have hnat : 2 * ∑ x ∈ X, a x ≤ X.card * I.card := by
    rw [← htot, Finset.sum_add_distrib, two_mul]
    exact Nat.add_le_add_left (Finset.sum_le_sum fun x _ => hle x) _
  refine ⟨?_, ⟨fun heq => ?_, fun hI' => ?_⟩⟩
  · rw [havg, div_le_iff₀ hIpos]
    have : (2 : ℚ) * ((∑ x ∈ X, a x : ℕ) : ℚ) ≤ (X.card : ℚ) * I.card := by exact_mod_cast hnat
    linarith
  · -- equality: every count agrees, so the family is closed under insertion
    rw [havg, div_eq_iff hIpos.ne'] at heq
    have h2 : 2 * ∑ x ∈ X, a x = X.card * I.card := by
      have : (2 : ℚ) * ((∑ x ∈ X, a x : ℕ) : ℚ) = (X.card : ℚ) * I.card := by linarith
      exact_mod_cast this
    have hsab : ∑ x ∈ X, a x = ∑ x ∈ X, b x := by
      rw [← htot, Finset.sum_add_distrib] at h2
      omega
    have hpt := (Finset.sum_eq_sum_iff_of_le fun x _ => hle x).1 hsab
    have hup : ∀ S ∈ I, ∀ x ∈ X, x ∉ S → insert x S ∈ I := by
      intro S hS x hx hxS
      have himg : (I.filter (fun S => x ∈ S)).image (fun S => S.erase x) =
          I.filter (fun S => x ∉ S) := by
        apply Finset.eq_of_subset_of_card_le
        · intro T hT
          obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hT
          exact erase_maps x U hU
        · rw [Finset.card_image_of_injOn (erase_inj x)]
          exact (hpt x hx).ge
      have hmem : S ∈ (I.filter (fun S => x ∈ S)).image (fun S => S.erase x) := by
        rw [himg, Finset.mem_filter]; exact ⟨hS, hxS⟩
      obtain ⟨T, hT, hTS⟩ := Finset.mem_image.1 hmem
      rw [Finset.mem_filter] at hT
      rw [← hTS, Finset.insert_erase hT.2]
      exact hT.1
    have hempty : ∅ ∈ I := by
      obtain ⟨S, hS⟩ := hI
      exact hdown S hS ∅ (Finset.empty_subset S)
    ext T
    rw [Finset.mem_powerset]
    refine ⟨hsub T, fun hT => ?_⟩
    induction T using Finset.induction_on with
    | empty => exact hempty
    | insert x T hxT ih =>
      have hTX : T ⊆ X := (Finset.subset_insert x T).trans hT
      exact hup T (ih hTX) x (hT (Finset.mem_insert_self x T)) hxT
  · -- the whole power set: the two counts agree
    have hup : ∀ S ∈ I, ∀ x ∈ X, x ∉ S → insert x S ∈ I := by
      intro S hS x hx _
      rw [hI', Finset.mem_powerset] at hS ⊢
      exact Finset.insert_subset hx hS
    have hpt : ∀ x ∈ X, a x = b x := fun x hx => le_antisymm (hle x) (hge hup x hx)
    have h2 : 2 * ∑ x ∈ X, a x = X.card * I.card := by
      rw [← htot, Finset.sum_add_distrib, two_mul, Finset.sum_congr rfl hpt]
    rw [havg, div_eq_iff hIpos.ne']
    have : (2 : ℚ) * ((∑ x ∈ X, a x : ℕ) : ℚ) = (X.card : ℚ) * I.card := by exact_mod_cast h2
    linarith
