import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingReverseCrossoutValid

/-!
# picking_reverse_crossout_exists

Topic: fair_division   Node: 50cf4706da4a

Provenance: helper lemma. Reverse crossout representation of two-agent sequential picking; see https://cdn.aaai.org/ojs/8697/8697-13-12225-1-2-20201228.pdf Theorem 1.

For any finite number of items, any two real-valued item functions, and any picking sequence of matching length, there is a valid reverse crossout sequence.
-/

lemma picking_reverse_crossout_exists_list_min_order {α : Type*} [DecidableEq α] (k : ℕ) :
    ∀ (s : Finset α) (_hs : s.card = k) (g : ℕ → α → ℝ),
      ∃ l : List α, l.Nodup ∧ l.toFinset = s ∧
        ∀ (t j : ℕ) (htj : t < j) (hj : j < l.length),
          g t (l.get ⟨t, htj.trans hj⟩) ≤ g t (l.get ⟨j, hj⟩) := by
  induction' k with k ih
  · intro s hs g
    rw [Finset.card_eq_zero] at hs
    subst hs
    use []
    simp
  · intro s hs g
    have hne : s.Nonempty := by
      rw [← Finset.card_pos, hs]
      exact Nat.succ_pos k
    obtain ⟨x, hx, hxmin⟩ := Finset.exists_min_image s (g 0) hne
    let s' := s.erase x
    have hs' : s'.card = k := by
      rw [Finset.card_erase_of_mem hx, hs, Nat.succ_sub_one]
    obtain ⟨l', hnodup', htoFinset', horder'⟩ := ih s' hs' (fun t => g (t + 1))
    have hx_not_mem : x ∉ l' := by
      intro h
      have : x ∈ l'.toFinset := List.mem_toFinset.mpr h
      rw [htoFinset', Finset.mem_erase] at this
      exact this.1 rfl
    have htoFinset : (x :: l').toFinset = s := by
      rw [List.toFinset_cons, htoFinset', Finset.insert_erase hx]
    have hnodup : (x :: l').Nodup := List.nodup_cons.mpr ⟨hx_not_mem, hnodup'⟩
    refine ⟨x :: l', hnodup, htoFinset, ?_⟩
    intro t j htj hj
    cases t with
    | zero =>
      obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt htj)
      have hj' : j' < l'.length := Nat.succ_lt_succ_iff.mp hj
      have h1 : (x :: l').get ⟨0, htj.trans hj⟩ = x := rfl
      have h2 : (x :: l').get ⟨j' + 1, hj⟩ = l'.get ⟨j', hj'⟩ := rfl
      rw [h1, h2]
      apply hxmin
      have hmem : l'.get ⟨j', hj'⟩ ∈ l' := List.get_mem l' ⟨j', hj'⟩
      have : l'.get ⟨j', hj'⟩ ∈ l'.toFinset := List.mem_toFinset.mpr hmem
      rw [htoFinset'] at this
      exact Finset.mem_of_mem_erase this
    | succ t' =>
      obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Nat.zero_lt_of_lt htj))
      have htj' : t' < j' := Nat.succ_lt_succ_iff.mp htj
      have hj' : j' < l'.length := Nat.succ_lt_succ_iff.mp hj
      have h1 : (x :: l').get ⟨t' + 1, htj.trans hj⟩ = l'.get ⟨t', htj'.trans hj'⟩ := rfl
      have h2 : (x :: l').get ⟨j' + 1, hj⟩ = l'.get ⟨j', hj'⟩ := rfl
      rw [h1, h2]
      exact horder' t' j' htj' hj'

theorem picking_reverse_crossout_exists (n : ℕ) (u : Fin 2 → Fin n → ℝ) (s : List (Fin 2)) (hs : s.length = n) :
  ∃ π : Fin n → Fin n, picking_reverse_crossout_valid u s π := by
  let g : ℕ → Fin n → ℝ := fun t x => u (if s.reverse.getD t 0 = 0 then 1 else 0) x
  obtain ⟨l, hnodup, htoFinset, horder⟩ :=
    picking_reverse_crossout_exists_list_min_order n (Finset.univ : Finset (Fin n)) (Finset.card_fin n) g
  have hlen : l.length = n := by
    rw [← List.toFinset_card_of_nodup hnodup, htoFinset, Finset.card_fin]
  let π : Fin n → Fin n := fun t => l.get ⟨t.val, hlen.symm ▸ t.isLt⟩
  use π
  refine ⟨hs, ?_, ?_⟩
  · apply Finite.injective_iff_bijective.mp
    intro a b hab
    dsimp [π] at hab
    have hinj := (List.Nodup.get_inj_iff hnodup).mp hab
    exact Fin.ext (Fin.mk.inj hinj)
  · intro t j htj
    have hj : j.val < l.length := by rw [hlen]; exact j.isLt
    have htj_val : t.val < j.val := htj
    have hle := horder t.val j.val htj_val hj
    dsimp [g] at hle
    exact hle
