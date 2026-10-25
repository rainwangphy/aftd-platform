import AFTD.Prelude

/-!
# cycle_power_fifteen_endpoint_layer_period_sixteen

Topic: combinatorics   Node: 38b3ab015ade

Provenance: helper lemma. Conditional helper for RT-1 / OP-205, arXiv:2610.15635, the unresolved k=15 case following Theorem 1.3. The slot-exchange route is the latest RT-1 journal next step and was motivated by experiment 4369. It assumes endpoint/paired alternation, exact active counts and layer separation; it does not prove the six-type classification or a new graph covering bound.

For sixteen-position cyclic class types alternating between endpoint-only types {0,15} and types with equal consecutive membership bits, assume every vertex is active in exactly five classes, the active classes have distinct labels in Fin 5, and every class contains its start. Then the label at every endpoint-only start repeats after sixteen positions. Classification of actual graph-cover classes and label periods at other starts are not conclusions of this helper.
-/

theorem cycle_power_fifteen_endpoint_layer_period_sixteen
    (n : ℕ) [NeZero n]
    (σ : ZMod n → Fin 5) (x : ZMod n → Fin 16 → Bool) (P : ZMod n → Bool)
    (halt : ∀ p, P (p + 1) = !(P p))
    (hend : ∀ p, P p = true → ∀ j : Fin 16,
      x p j = true ↔ j.val = 0 ∨ j.val = 15)
    (hpair : ∀ p, P p = false → ∀ a : Fin 8,
      x p ⟨2 * a.val, by omega⟩ = x p ⟨2 * a.val + 1, by omega⟩)
    (hzero : ∀ p, x p 0 = true)
    (hcount : ∀ v : ZMod n,
      (Finset.univ.filter (fun j : Fin 16 => x (v - (j.val : ZMod n)) j = true)).card = 5)
    (hsep : ∀ (p q : ZMod n) (j k : Fin 16),
      p + (j.val : ZMod n) = q + (k.val : ZMod n) →
      x p j = true → x q k = true → σ p = σ q → j = k) :
    ∀ p, P p = true → σ (p + 16) = σ p := by
  classical
  have htwo : ∀ q, P (q + 2) = P q := by
    intro q
    calc P (q + 2) = P ((q + 1) + 1) := by congr 1; ring
      _ = !P (q + 1) := halt _
      _ = P q := by rw [halt]; simp
  have heven : ∀ (q : ZMod n) (a : ℕ), P (q + ((2 * a : ℕ) : ZMod n)) = P q := by
    intro q a
    induction a with
    | zero => simp
    | succ a ih =>
      calc P (q + ((2 * (a + 1) : ℕ) : ZMod n))
          = P ((q + ((2 * a : ℕ) : ZMod n)) + 2) := by congr 1; push_cast; ring
        _ = P (q + ((2 * a : ℕ) : ZMod n)) := htwo _
        _ = P q := ih
  intro p hp
  have hoff : ∀ d : ℕ, P (p + (d : ZMod n)) = if d % 2 = 0 then true else false := by
    intro d
    by_cases hd : d % 2 = 0
    · have he : 2 * (d / 2) = d := by omega
      simpa [he, hp, hd] using heven p (d / 2)
    · have he : 2 * (d / 2) + 1 = d := by omega
      have hq : p + (d : ZMod n) = (p + 1) + ((2 * (d / 2) : ℕ) : ZMod n) := by
        have hc : ((2 * (d / 2) + 1 : ℕ) : ZMod n) = (d : ZMod n) := by
          exact congrArg (fun z : ℕ => (z : ZMod n)) he
        calc p + (d : ZMod n) = p + ((2 * (d / 2) + 1 : ℕ) : ZMod n) :=
            congrArg (fun z : ZMod n => p + z) hc.symm
          _ = _ := by push_cast; ring
      rw [hq, heven, halt, hp]
      simp [hd]
  let v := p + 15
  let A : Finset (Fin 16) := Finset.univ.filter (fun j => x (v - (j.val : ZMod n)) j = true)
  let f : Fin 16 → Fin 5 := fun j => σ (v - (j.val : ZMod n))
  have hAcard : A.card = 5 := hcount v
  have hfinj : Set.InjOn f (↑A : Set (Fin 16)) := by
    intro j hj k hk heq
    exact hsep _ _ j k (by ring) (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2 heq
  have hfull : A.image f = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hfinj, hAcard, Fintype.card_fin]
  obtain ⟨j, hjA, hlabel⟩ := Finset.mem_image.mp
    (show σ (p + 16) ∈ A.image f by rw [hfull]; exact Finset.mem_univ _)
  have hjx : x (v - (j.val : ZMod n)) j = true := (Finset.mem_filter.mp hjA).2
  by_cases hj15 : j.val = 15
  · simpa [f, v, hj15] using hlabel.symm
  · have hjlt : j.val < 15 := by omega
    let q := v - (j.val : ZMod n)
    have hq : q = p + ((15 - j.val : ℕ) : ZMod n) := by
      dsimp [q, v]
      rw [Nat.cast_sub (by omega : j.val ≤ 15)]
      norm_num <;> ring
    have hjEven : j.val % 2 = 0 := by
      by_contra hodd
      have hd : (15 - j.val) % 2 = 0 := by omega
      have hPq : P q = true := by rw [hq, hoff]; simp [hd]
      have he := (hend q hPq j).mp hjx
      rcases he with he | he
      · omega
      · exact hj15 he
    have hPq : P q = false := by
      have hd : (15 - j.val) % 2 ≠ 0 := by omega
      rw [hq, hoff]
      simp [hd]
    let a : Fin 8 := ⟨j.val / 2, by omega⟩
    let k : Fin 16 := ⟨j.val + 1, by omega⟩
    have hevenj : (⟨2 * a.val, by omega⟩ : Fin 16) = j := by
      apply Fin.ext
      dsimp [a]
      omega
    have hoddj : (⟨2 * a.val + 1, by omega⟩ : Fin 16) = k := by
      apply Fin.ext
      dsimp [a, k]
      omega
    have hkx : x q k = true := by
      have h := hpair q hPq a
      rw [hevenj, hoddj] at h
      exact h.symm.trans hjx
    have hpos := hsep q (p + 16) k 0
      (by dsimp [q, v, k]; push_cast; ring) hkx (hzero _) hlabel
    have hval := congrArg Fin.val hpos
    dsimp [k] at hval
    omega
