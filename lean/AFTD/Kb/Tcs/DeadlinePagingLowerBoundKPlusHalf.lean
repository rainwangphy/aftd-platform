import AFTD.Prelude
import AFTD.Kb.Tcs.DeadlineRequest
import AFTD.Kb.Tcs.IsCompetitiveRatio
import AFTD.Kb.Tcs.InstanceHorizon
import AFTD.Kb.Tcs.ScheduleCost
import AFTD.Kb.Tcs.IsOnlineClairvoyantScheduleGen
import AFTD.Kb.Tcs.IsFeasibleSchedule

/-!
# deadline_paging_lower_bound_k_plus_half

Topic: online_algorithms   Node: b8bb48e95b46

Provenance: formalization of a published result. Source: arXiv:2610.18767 Theorem 1.3

For every cache capacity k ≥ 1, every finite page universe α with at least k + 2 pages, every initial cache C₀ of size k, every schedule generator Alg, and every real ρ, if Alg is ρ-competitive starting from C₀ in the sense of IsCompetitiveRatio, then ρ ≥ k + 1/2.
-/

/-- Deterministic lower bound of k + 1/2 on at least two holes. -/
theorem deadline_paging_lower_bound_k_plus_half
    (k : ℕ) (hk : 1 ≤ k) {α : Type*} [Fintype α] [DecidableEq α] (hn : k + 2 ≤ Fintype.card α)
    (C₀ : Finset α) (hC₀ : C₀.card = k)
    (Alg : List (DeadlineRequest α) → (ℕ → Finset α))
    (ρ : ℝ) (hρ : IsCompetitiveRatio k C₀ Alg ρ) :
    (k : ℝ) + 1 / 2 ≤ ρ := by
  classical
  obtain ⟨hgen, hfeas, -⟩ := hρ
  -- an enumeration of k+2 distinct pages
  let e : Fin (k + 2) → α := fun i => (Fintype.equivFin α).symm (Fin.castLE hn i)
  have he_inj : Function.Injective e := by
    intro i j hij
    exact Fin.castLE_injective hn ((Fintype.equivFin α).symm.injective hij)
  let T : Finset α := Finset.univ.image e
  have hTcard : T.card = k + 2 := by
    show (Finset.univ.image e).card = k + 2
    rw [Finset.card_image_of_injective _ he_inj, Finset.card_univ, Fintype.card_fin]
  let h13 : 1 ≤ 3 := by norm_num
  -- the common prefix: every page of `T` is requested with window [1,3]
  let pre : List (DeadlineRequest α) :=
    List.ofFn (fun i : Fin (k+2) => (⟨e i, 1, 3, h13⟩ : DeadlineRequest α))
  -- tight requests for all pages of `S` at time `t`
  let tight : Finset α → ℕ → List (DeadlineRequest α) :=
    fun S t => S.val.toList.map (fun p => (⟨p, t, t, le_refl t⟩ : DeadlineRequest α))
  have hpre_mem : ∀ r ∈ pre, r.page ∈ T ∧ r.arrival = 1 ∧ r.deadline = 3 := by
    intro r hr
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hr
    rw [← hi]
    exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, rfl, rfl⟩
  have hpre_exists : ∀ p ∈ T, ∃ r ∈ pre, r.page = p ∧ r.arrival = 1 ∧ r.deadline = 3 := by
    intro p hp
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hp
    exact ⟨⟨e i, 1, 3, h13⟩, List.mem_ofFn.mpr ⟨i, rfl⟩, hi, rfl, rfl⟩
  have htight_mem : ∀ (S : Finset α) (t : ℕ) {r : DeadlineRequest α}, r ∈ tight S t →
      r.page ∈ S ∧ r.arrival = t ∧ r.deadline = t := by
    intro S t r hr
    obtain ⟨p, hp, hpr⟩ := List.mem_map.mp hr
    have hpS : p ∈ S := by
      rw [← Finset.mem_val, ← Multiset.mem_toList]
      exact hp
    rw [← hpr]
    exact ⟨hpS, rfl, rfl⟩
  have htight_exists : ∀ (S : Finset α) (t : ℕ), ∀ p ∈ S,
      ∃ r ∈ tight S t, r.page = p ∧ r.arrival = t ∧ r.deadline = t := by
    intro S t p hp
    exact ⟨⟨p, t, t, le_refl t⟩,
      List.mem_map.mpr ⟨p, Multiset.mem_toList.mpr (by rwa [Finset.mem_val]), rfl⟩, rfl, rfl, rfl⟩
  have htight_filter : ∀ (S : Finset α) (t : ℕ), 1 < t →
      List.filter (fun r : DeadlineRequest α => decide (r.arrival ≤ 1)) (tight S t) = [] := by
    intro S t ht
    rw [List.filter_eq_nil_iff]
    intro r hr
    obtain ⟨-, h1, -⟩ := htight_mem S t hr
    rw [h1]
    simp
    omega
  have hpre_filter :
      List.filter (fun r : DeadlineRequest α => decide (r.arrival ≤ 1)) pre = pre := by
    rw [List.filter_eq_self]
    intro r hr
    obtain ⟨-, h1, -⟩ := hpre_mem r hr
    rw [h1]
    simp
  -- for each x in T: a feasible instance whose time-1 cache (after the common prefix) holds x
  have key : ∀ x ∈ T, ∃ (L : List (DeadlineRequest α)) (sched : ℕ → Finset α),
      IsFeasibleSchedule k C₀ sched L ∧ x ∈ Alg L 1 ∧
        List.filter (fun r : DeadlineRequest α => decide (r.arrival ≤ 1)) L = pre := by
    intro x hx
    have hexcard : (T.erase x).card = k + 1 := by
      rw [Finset.card_erase_of_mem hx, hTcard]
      omega
    obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp (by omega : 1 < (T.erase x).card)
    let A : Finset α := (T.erase x).erase y
    let B : Finset α := (T.erase x).erase z
    have hAcard : A.card = k := by
      rw [Finset.card_erase_of_mem hy, hexcard]
      omega
    have hBcard : B.card = k := by
      rw [Finset.card_erase_of_mem hz, hexcard]
      omega
    have hxA : x ∉ A := by
      simp only [A, Finset.mem_erase]
      tauto
    have hxB : x ∉ B := by
      simp only [B, Finset.mem_erase]
      tauto
    have hAB : A ∪ B = T.erase x := by
      ext w
      simp only [Finset.mem_union, A, B, Finset.mem_erase]
      constructor
      · rintro (⟨-, hwx, hwT⟩ | ⟨-, hwx, hwT⟩)
        · exact ⟨hwx, hwT⟩
        · exact ⟨hwx, hwT⟩
      · rintro ⟨hwx, hwT⟩
        by_cases hwy : w = y
        · refine Or.inr ⟨?_, hwx, hwT⟩
          intro h
          exact hyz (hwy.symm.trans h)
        · exact Or.inl ⟨hwy, hwx, hwT⟩
    let L : List (DeadlineRequest α) := pre ++ tight A 2 ++ tight B 3
    let sched : ℕ → Finset α := fun t =>
      if t = 0 then C₀ else if t = 1 then {x} else if t = 2 then A else if t = 3 then B else ∅
    have hsched0 : sched 0 = C₀ := by simp [sched]
    have hschcard : ∀ t, (sched t).card ≤ k := by
      intro t
      simp only [sched]
      split_ifs with h0 h1 h2 h3
      · rw [hC₀]
      · simp; omega
      · rw [hAcard]
      · rw [hBcard]
      · simp
    have hserve : ∀ r ∈ L, ∃ t, r.arrival ≤ t ∧ t ≤ r.deadline ∧ r.page ∈ sched t := by
      intro r hr
      simp only [L, List.mem_append] at hr
      rcases hr with (hr | hr) | hr
      · obtain ⟨hpT, h1, h3⟩ := hpre_mem r hr
        by_cases hpx : r.page = x
        · exact ⟨1, by omega, by omega, by simp [sched, hpx]⟩
        · have hmem : r.page ∈ A ∪ B := by
            rw [hAB]
            simp only [Finset.mem_erase]
            exact ⟨hpx, hpT⟩
          rcases Finset.mem_union.mp hmem with hA | hB
          · exact ⟨2, by omega, by omega, by simpa [sched] using hA⟩
          · exact ⟨3, by omega, by omega, by simpa [sched] using hB⟩
      · obtain ⟨hpA, h1, h3⟩ := htight_mem A 2 hr
        exact ⟨2, by omega, by omega, by simpa [sched] using hpA⟩
      · obtain ⟨hpB, h1, h3⟩ := htight_mem B 3 hr
        exact ⟨3, by omega, by omega, by simpa [sched] using hpB⟩
    refine ⟨L, sched, ⟨hsched0, hschcard, hserve⟩, ?_, ?_⟩
    · have hAlg := hfeas L ⟨sched, ⟨hsched0, hschcard, hserve⟩⟩
      obtain ⟨-, hAlgcard, hAlgserve⟩ := hAlg
      have hA2 : Alg L 2 = A := by
        have hsub : A ⊆ Alg L 2 := by
          intro p hp
          obtain ⟨r, hr, hpage, h1, h3⟩ := htight_exists A 2 p hp
          have hrL : r ∈ L := by
            simp only [L]
            exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hr)))
          obtain ⟨t, ht1, ht2, htmem⟩ := hAlgserve r hrL
          rw [hpage] at htmem
          have ht : t = 2 := by omega
          rwa [ht] at htmem
        symm
        exact Finset.eq_of_subset_of_card_le hsub (by rw [hAcard]; exact hAlgcard 2)
      have hB3 : Alg L 3 = B := by
        have hsub : B ⊆ Alg L 3 := by
          intro p hp
          obtain ⟨r, hr, hpage, h1, h3⟩ := htight_exists B 3 p hp
          have hrL : r ∈ L := by
            simp only [L]
            exact List.mem_append.mpr (Or.inr hr)
          obtain ⟨t, ht1, ht2, htmem⟩ := hAlgserve r hrL
          rw [hpage] at htmem
          have ht : t = 3 := by omega
          rwa [ht] at htmem
        symm
        exact Finset.eq_of_subset_of_card_le hsub (by rw [hBcard]; exact hAlgcard 3)
      obtain ⟨r, hr, hpage, h1, h3⟩ := hpre_exists x hx
      have hrL : r ∈ L := by
        simp only [L]
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hr)))
      obtain ⟨t, ht1, ht2, htmem⟩ := hAlgserve r hrL
      rw [hpage] at htmem
      have ht : t = 1 := by
        rcases Nat.lt_or_ge t 2 with h | h
        · omega
        rcases Nat.lt_or_ge t 3 with h' | h'
        · exfalso
          rw [show t = 2 by omega, hA2] at htmem
          exact hxA htmem
        · exfalso
          rw [show t = 3 by omega, hB3] at htmem
          exact hxB htmem
      rwa [ht] at htmem
    · simp only [L, List.filter_append, htight_filter A 2 (by omega), htight_filter B 3 (by omega),
        List.append_nil, hpre_filter]
  -- all instances have the same time-1 cache, so it holds all of `T`
  have hTne : T.Nonempty := Finset.card_pos.mp (by rw [hTcard]; omega)
  obtain ⟨x₀, hx₀⟩ := hTne
  obtain ⟨L₀, sched₀, feas₀, hmem₀, hfilt₀⟩ := key x₀ hx₀
  have hAlgL₀ := hfeas L₀ ⟨sched₀, feas₀⟩
  have hsub : ∀ x ∈ T, x ∈ Alg L₀ 1 := by
    intro x hx
    obtain ⟨L, sched, feas, hmem, hfilt⟩ := key x hx
    have heq : Alg L 1 = Alg L₀ 1 := hgen L L₀ 1 (by rw [hfilt, hfilt₀])
    rw [heq] at hmem
    exact hmem
  have hcardT : T.card ≤ (Alg L₀ 1).card := Finset.card_le_card hsub
  have hkle := hAlgL₀.2.1 1
  have : k + 2 ≤ k := by omega
  omega
