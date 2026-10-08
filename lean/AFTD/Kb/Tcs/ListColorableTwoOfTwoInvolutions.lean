import AFTD.Prelude
import AFTD.Kb.Tcs.F

/-!
# list_colorable_two_of_two_involutions

Topic: combinatorics   Node: d8d9debfe680

Provenance: formalization of a published result. Source: The list edge-coloring theorem for bipartite multigraphs (J. Combin. Theory Ser. B 63 (1995)), special case of maximum degree two, in the form used in arXiv:2610.07318 (A note on the list chromatic number of two matroids), proofs of Theorem 1.1 and Corollary 2.3. The proof here differs: a direct induction (a vertex with at most one neighbour is colored last; an edge whose ends have different lists is cut; if all lists agree along edges, a pair is contracted).

Let E be a finite set and p, q two involutions; they define two unit-capacity partition matroids on E with classes {e, p e} and {e, q e} of size at most two, whose common independent sets are the matchings of a bipartite multigraph of maximum degree at most two. From any lists of at least two colors per element one can choose colors so that partners under p, and partners under q, always get different colors.
-/

/-- Recolouring one vertex `v` of a colouring that is proper on `E \ {v}` for the pairing `r`:
it stays proper on `E` when the new colour differs from that of `v`'s partner. -/
theorem involution_coloring_update {α : Type*} [DecidableEq α] (E : Finset α) (v : α)
    (c' : α → ℕ) (t : ℕ) (r : α → α) (hr : Function.Involutive r)
    (hc' : ∀ e ∈ E.erase v, r e ∈ E.erase v → r e ≠ e → c' (r e) ≠ c' e)
    (hv : r v ≠ v → r v ∈ E → c' (r v) ≠ t) :
    ∀ e ∈ E, r e ∈ E → r e ≠ e →
      Function.update c' v t (r e) ≠ Function.update c' v t e := by
  intro e he hre hne
  by_cases hev : e = v
  · subst hev
    rw [Function.update_of_ne hne, Function.update_self]
    exact hv hne hre
  · by_cases hrev : r e = v
    · have : e = r v := by rw [← hrev, hr e]
      subst this
      rw [hrev, Function.update_self, Function.update_of_ne hev]
      exact (hv hev he).symm
    · rw [Function.update_of_ne hrev, Function.update_of_ne hev]
      exact hc' e (Finset.mem_erase.2 ⟨hev, he⟩) (Finset.mem_erase.2 ⟨hrev, hre⟩) hne

theorem two_involutions_list_aux {α : Type*} [DecidableEq α] (n : ℕ) :
    ∀ (E : Finset α), E.card ≤ n → ∀ (p q : α → α), Function.Involutive p →
    Function.Involutive q → ∀ (L : α → Finset ℕ) (zo : Option α),
      (∀ e ∈ E, zo ≠ some e → 2 ≤ (L e).card) →
      (∀ z, zo = some z → z ∈ E → 1 ≤ (L z).card ∧
          ¬ (p z ∈ E ∧ q z ∈ E ∧ p z ≠ z ∧ q z ≠ z ∧ p z ≠ q z)) →
      ∃ c : α → ℕ, (∀ e ∈ E, c e ∈ L e) ∧
        ∀ e ∈ E, (p e ∈ E → p e ≠ e → c (p e) ≠ c e) ∧
          (q e ∈ E → q e ≠ e → c (q e) ≠ c e) := by
  induction n with
  | zero =>
    intro E hE p q hp hq L zo _ _
    have : E = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hE)
    subst this
    exact ⟨fun _ => 0, by simp, by simp⟩
  | succ n ih =>
    intro E hE p q hp hq L zo hL hz
    by_cases hA : ∃ z, zo = some z ∧ z ∈ E
    · -- a vertex with a short list: it has at most one neighbour, colour it first
      obtain ⟨z, rfl, hzE⟩ := hA
      obtain ⟨h1, hfree⟩ := hz z rfl hzE
      obtain ⟨t, ht⟩ := Finset.card_pos.1 h1
      set E' := E.erase z with hE'
      set L' : α → Finset ℕ := fun e =>
        if e ≠ z ∧ (e = p z ∨ e = q z) then (L e).erase t else L e with hL'
      set zo' : Option α :=
        if p z ∈ E' then some (p z) else if q z ∈ E' then some (q z) else none with hzo'
      have hcard : E'.card ≤ n := by rw [hE', Finset.card_erase_of_mem hzE]; omega
      refine (fun H => ?_) (ih E' hcard p q hp hq L' zo' ?_ ?_)
      · obtain ⟨c', hc'L, hc'⟩ := H
        have hpz : p z ≠ z → p z ∈ E → c' (p z) ≠ t := by
          intro h1 h2 h3
          have := hc'L (p z) (Finset.mem_erase.2 ⟨h1, h2⟩)
          rw [hL'] at this
          simp only [ne_eq, h1, not_false_eq_true, true_or, and_self, if_true] at this
          exact (Finset.mem_erase.1 this).1 h3
        have hqz : q z ≠ z → q z ∈ E → c' (q z) ≠ t := by
          intro h1 h2 h3
          have := hc'L (q z) (Finset.mem_erase.2 ⟨h1, h2⟩)
          rw [hL'] at this
          simp only [ne_eq, h1, not_false_eq_true, or_true, and_self, if_true] at this
          exact (Finset.mem_erase.1 this).1 h3
        refine ⟨Function.update c' z t, ?_, ?_⟩
        · intro e he
          by_cases hez : e = z
          · subst hez; simpa using ht
          · rw [Function.update_of_ne hez]
            have := hc'L e (Finset.mem_erase.2 ⟨hez, he⟩)
            rw [hL'] at this
            dsimp only at this
            split_ifs at this with h
            all_goals first | exact Finset.mem_of_mem_erase this | exact this
        · intro e he
          exact ⟨involution_coloring_update E z c' t p hp (fun e he => (hc' e he).1) hpz e he,
            involution_coloring_update E z c' t q hq (fun e he => (hc' e he).2) hqz e he⟩
      · intro e he hne
        have hez : e ≠ z := (Finset.mem_erase.1 he).1
        have heE : e ∈ E := (Finset.mem_erase.1 he).2
        by_cases hm : e = p z ∨ e = q z
        · exfalso
          apply hne
          rcases hm with h | h
          · rw [hzo', if_pos (h ▸ he), h]
          · by_cases hp' : p z ∈ E'
            · rw [hzo', if_pos hp']
              have hpz : p z ≠ z := (Finset.mem_erase.1 hp').1
              by_contra hc
              have hpe : p z ≠ e := fun h' => hc (by rw [h'])
              exact hfree ⟨(Finset.mem_erase.1 hp').2, h ▸ heE, hpz, h ▸ hez,
                fun h'' => hpe (h'' ▸ h.symm)⟩
            · rw [hzo', if_neg hp', if_pos (h ▸ he), h]
        · have : L' e = L e := by
            rw [hL']; dsimp only; rw [if_neg (fun h => hm h.2)]
          rw [this]
          exact hL e heE (by simp only [ne_eq, Option.some.injEq]; exact fun h => hez h.symm)
      · intro y hy hyE
        have hyz : y ≠ z := (Finset.mem_erase.1 hyE).1
        have hyE' : y ∈ E := (Finset.mem_erase.1 hyE).2
        have hym : y = p z ∨ y = q z := by
          rw [hzo'] at hy
          split_ifs at hy <;> simp_all
        have hLy : L' y = (L y).erase t := by
          rw [hL']; dsimp only; rw [if_pos ⟨hyz, hym⟩]
        refine ⟨?_, ?_⟩
        · rw [hLy]
          have := hL y hyE' (by simp only [ne_eq, Option.some.injEq]; exact fun h => hyz h.symm)
          have := Finset.pred_card_le_card_erase (s := L y) (a := t)
          omega
        · rintro ⟨h1, h2, -, -, -⟩
          rcases hym with h | h
          · have : p y = z := by rw [h, hp z]
            exact (Finset.mem_erase.1 h1).1 this
          · have : q y = z := by rw [h, hq z]
            exact (Finset.mem_erase.1 h2).1 this
    · have hL2 : ∀ e ∈ E, 2 ≤ (L e).card := by
        intro e he
        apply hL e he
        intro h
        exact hA ⟨e, h, he⟩
      by_cases hB1 : ∃ v ∈ E, ¬ (p v ∈ E ∧ q v ∈ E ∧ p v ≠ v ∧ q v ≠ v ∧ p v ≠ q v)
      · -- a vertex with at most one neighbour: colour the rest, then it
        obtain ⟨v, hvE, hfree⟩ := hB1
        have hcard : (E.erase v).card ≤ n := by rw [Finset.card_erase_of_mem hvE]; omega
        obtain ⟨c', hc'L, hc'⟩ := ih (E.erase v) hcard p q hp hq L none
          (fun e he _ => hL2 e (Finset.mem_of_mem_erase he)) (by simp)
        set F : Finset ℕ := (({p v, q v} : Finset α).filter (· ∈ E.erase v)).image c' with hF
        have hFc : F.card ≤ 1 := by
          refine (Finset.card_image_le).trans ?_
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at ha hb
          by_contra hab
          apply hfree
          rcases ha with ⟨rfl | rfl, ha⟩ <;> rcases hb with ⟨rfl | rfl, hb⟩
          · exact absurd rfl hab
          · exact ⟨(Finset.mem_erase.1 ha).2, (Finset.mem_erase.1 hb).2,
              (Finset.mem_erase.1 ha).1, (Finset.mem_erase.1 hb).1, hab⟩
          · exact ⟨(Finset.mem_erase.1 hb).2, (Finset.mem_erase.1 ha).2,
              (Finset.mem_erase.1 hb).1, (Finset.mem_erase.1 ha).1, fun h => hab h.symm⟩
          · exact absurd rfl hab
        obtain ⟨t, ht⟩ : (L v \ F).Nonempty := by
          rw [← Finset.card_pos]
          have := Finset.le_card_sdiff F (L v)
          have := hL2 v hvE
          omega
        have hmem : ∀ y, y = p v ∨ y = q v → y ≠ v → y ∈ E → c' y ≠ t := by
          intro y hy hyv hyE h
          apply (Finset.mem_sdiff.1 ht).2
          rw [hF, Finset.mem_image]
          refine ⟨y, Finset.mem_filter.2 ⟨?_, Finset.mem_erase.2 ⟨hyv, hyE⟩⟩, h⟩
          rcases hy with rfl | rfl <;> simp
        refine ⟨Function.update c' v t, ?_, ?_⟩
        · intro e he
          by_cases hev : e = v
          · subst hev; simpa using (Finset.mem_sdiff.1 ht).1
          · rw [Function.update_of_ne hev]; exact hc'L e (Finset.mem_erase.2 ⟨hev, he⟩)
        · intro e he
          exact ⟨involution_coloring_update E v c' t p hp (fun e he => (hc' e he).1)
              (fun h1 h2 => hmem _ (Or.inl rfl) h1 h2) e he,
            involution_coloring_update E v c' t q hq (fun e he => (hc' e he).2)
              (fun h1 h2 => hmem _ (Or.inr rfl) h1 h2) e he⟩
      · have hnf : ∀ v ∈ E, p v ∈ E ∧ q v ∈ E ∧ p v ≠ v ∧ q v ≠ v ∧ p v ≠ q v := by
          intro v hv
          by_contra h
          exact hB1 ⟨v, hv, h⟩
        -- an edge whose ends have different lists
        have key : ∀ (r s : α → α), Function.Involutive r → Function.Involutive s →
            (∀ v ∈ E, r v ∈ E ∧ s v ∈ E ∧ r v ≠ v ∧ s v ≠ v ∧ r v ≠ s v) →
            (∃ v ∈ E, ∃ a ∈ L v, a ∉ L (r v)) →
            ∃ c : α → ℕ, (∀ e ∈ E, c e ∈ L e) ∧
              ∀ e ∈ E, (r e ∈ E → r e ≠ e → c (r e) ≠ c e) ∧
                (s e ∈ E → s e ≠ e → c (s e) ≠ c e) := by
          intro r s hr hs hrs ⟨v, hvE, a, haL, har⟩
          obtain ⟨hrv, hsv, hrvv, hsvv, hrsv⟩ := hrs v hvE
          have hcard : (E.erase v).card ≤ n := by rw [Finset.card_erase_of_mem hvE]; omega
          set L' := Function.update L (s v) ((L (s v)).erase a) with hL'
          refine (fun H => ?_) (ih (E.erase v) hcard r s hr hs L' (some (s v)) ?_ ?_)
          · obtain ⟨c', hc'L, hc'⟩ := H
            have hrv' : c' (r v) ∉ ({a} : Finset ℕ) := by
              have := hc'L (r v) (Finset.mem_erase.2 ⟨hrvv, hrv⟩)
              rw [hL', Function.update_of_ne hrsv] at this
              simp only [Finset.mem_singleton]
              exact fun h => har (h ▸ this)
            have hsv' : c' (s v) ≠ a := by
              have := hc'L (s v) (Finset.mem_erase.2 ⟨hsvv, hsv⟩)
              rw [hL', Function.update_self] at this
              exact (Finset.mem_erase.1 this).1
            refine ⟨Function.update c' v a, ?_, ?_⟩
            · intro e he
              by_cases hev : e = v
              · subst hev; simpa using haL
              · rw [Function.update_of_ne hev]
                have := hc'L e (Finset.mem_erase.2 ⟨hev, he⟩)
                by_cases hes : e = s v
                · rw [hes, hL', Function.update_self] at this
                  rw [hes]; exact Finset.mem_of_mem_erase this
                · rwa [hL', Function.update_of_ne hes] at this
            · intro e he
              exact ⟨involution_coloring_update E v c' a r hr (fun e he => (hc' e he).1)
                  (fun _ _ h => hrv' (Finset.mem_singleton.2 h)) e he,
                involution_coloring_update E v c' a s hs (fun e he => (hc' e he).2)
                  (fun _ _ => hsv') e he⟩
          · intro e he hne
            have hes : e ≠ s v := fun h => hne (by rw [h])
            rw [hL', Function.update_of_ne hes]
            exact hL2 e (Finset.mem_of_mem_erase he)
          · intro y hy hyE
            simp only [Option.some.injEq] at hy
            subst hy
            refine ⟨?_, ?_⟩
            · rw [hL', Function.update_self]
              have := Finset.pred_card_le_card_erase (s := L (s v)) (a := a)
              have := hL2 (s v) hsv
              omega
            · rintro ⟨-, h2, -⟩
              rw [hs v] at h2
              exact (Finset.mem_erase.1 h2).1 rfl
        by_cases hpa : ∃ v ∈ E, ∃ a ∈ L v, a ∉ L (p v)
        · exact key p q hp hq hnf hpa
        by_cases hqa : ∃ v ∈ E, ∃ a ∈ L v, a ∉ L (q v)
        · obtain ⟨c, hcL, hc⟩ := key q p hq hp (fun v hv => by
            obtain ⟨h1, h2, h3, h4, h5⟩ := hnf v hv
            exact ⟨h2, h1, h4, h3, fun h => h5 h.symm⟩) hqa
          exact ⟨c, hcL, fun e he => ⟨(hc e he).2, (hc e he).1⟩⟩
        -- all lists agree along edges: contract one `p`-pair into a `q`-edge
        have hsub : ∀ v ∈ E, L v ⊆ L (p v) ∧ L v ⊆ L (q v) := by
          intro v hv
          refine ⟨fun a ha => ?_, fun a ha => ?_⟩
          · by_contra h; exact hpa ⟨v, hv, a, ha, h⟩
          · by_contra h; exact hqa ⟨v, hv, a, ha, h⟩
        rcases E.eq_empty_or_nonempty with hE0 | ⟨v, hvE⟩
        · subst hE0; exact ⟨fun _ => 0, by simp, by simp⟩
        obtain ⟨hwE, huE, hwv, huv, hwu⟩ := hnf v hvE
        set w := p v with hw
        set u := q v with hu
        obtain ⟨-, hxE, -, hxw, -⟩ := hnf w hwE
        set x := q w with hx
        have hxu : x ≠ u := fun h => hwv (hq.injective h)
        have hxv : x ≠ v := fun h => hwu (by rw [← hq w, ← hx, h])
        have hqu : q u = v := hq v
        have hqx : q x = w := hq w
        have hpw : p w = v := hp v
        set q' : α → α := fun y =>
          if y = u then x else if y = x then u else if y = v then v else if y = w then w
          else q y with hq'
        have hq'inv : Function.Involutive q' := by
          intro y
          by_cases h1 : y = u
          · subst h1; simp [hq', hxu]
          by_cases h2 : y = x
          · subst h2; simp [hq', hxu]
          by_cases h3 : y = v
          · subst h3; simp [hq', h1, h2]
          by_cases h4 : y = w
          · subst h4; simp [hq', h1, h2, h3]
          have k1 : q y ≠ u := fun h => h3 (by rw [← hq y, h, hqu])
          have k2 : q y ≠ x := fun h => h4 (by rw [← hq y, h, hqx])
          have k3 : q y ≠ v := fun h => h1 (by rw [← hq y, h])
          have k4 : q y ≠ w := fun h => h2 (by rw [← hq y, h])
          simp [hq', h1, h2, h3, h4, k1, k2, k3, k4, hq y]
        set E'' := (E.erase v).erase w with hE''
        have hcard : E''.card ≤ n := by
          rw [hE'', Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hwv, hwE⟩),
            Finset.card_erase_of_mem hvE]
          omega
        have huE'' : u ∈ E'' := Finset.mem_erase.2 ⟨fun h => hwu h.symm,
          Finset.mem_erase.2 ⟨huv, huE⟩⟩
        have hxE'' : x ∈ E'' := Finset.mem_erase.2 ⟨hxw, Finset.mem_erase.2 ⟨hxv, hxE⟩⟩
        obtain ⟨c', hc'L, hc'⟩ := ih E'' hcard p q' hp hq'inv L none
          (fun e he _ => hL2 e (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he)))
          (by simp)
        have hux : c' x ≠ c' u := by
          have := (hc' u huE'').2
          simp only [hq', if_true] at this
          exact this hxE'' hxu
        -- `c'` is proper for `q` on `E''`: the edges of `q` inside `E''` are edges of `q'`
        have hc'q : ∀ e ∈ E'', q e ∈ E'' → q e ≠ e → c' (q e) ≠ c' e := by
          intro e he hqe hne
          have hev : e ≠ v := (Finset.mem_erase.1 (Finset.mem_of_mem_erase he)).1
          have hew : e ≠ w := (Finset.mem_erase.1 he).1
          have heu : e ≠ u := fun h => by
            rw [h, hqu] at hqe
            exact (Finset.mem_erase.1 (Finset.mem_of_mem_erase hqe)).1 rfl
          have hex : e ≠ x := fun h => by
            rw [h, hqx] at hqe
            exact (Finset.mem_erase.1 hqe).1 rfl
          have : q' e = q e := by simp [hq', heu, hex, hev, hew]
          have := (hc' e he).2
          rw [‹q' e = q e›] at this
          exact this hqe hne
        set c1 := Function.update c' v (c' x) with hc1
        have hE1 : (E.erase w).erase v = E'' := by rw [hE'', Finset.erase_right_comm]
        have hc1p : ∀ e ∈ E.erase w, p e ∈ E.erase w → p e ≠ e → c1 (p e) ≠ c1 e :=
          involution_coloring_update (E.erase w) v c' (c' x) p hp
            (by rw [hE1]; exact fun e he => (hc' e he).1)
            (fun _ h => absurd (Finset.mem_erase.1 h).1 (by simp [hw]))
        have hc1q : ∀ e ∈ E.erase w, q e ∈ E.erase w → q e ≠ e → c1 (q e) ≠ c1 e :=
          involution_coloring_update (E.erase w) v c' (c' x) q hq
            (by rw [hE1]; exact hc'q) (fun _ _ => hux.symm)
        refine ⟨Function.update c1 w (c' u), ?_, ?_⟩
        · intro e he
          by_cases hew : e = w
          · rw [hew, Function.update_self]
            have h1 := hc'L u huE''
            have h2 := (hsub u huE).2 h1
            rw [hqu] at h2
            exact (hsub v hvE).1 h2
          · rw [Function.update_of_ne hew]
            by_cases hev : e = v
            · rw [hev, hc1, Function.update_self]
              have h1 := hc'L x hxE''
              have h2 := (hsub x hxE).2 h1
              rw [hqx] at h2
              have h3 := (hsub w hwE).1 h2
              rwa [hpw] at h3
            · rw [hc1, Function.update_of_ne hev]
              exact hc'L e (Finset.mem_erase.2 ⟨hew, Finset.mem_erase.2 ⟨hev, he⟩⟩)
        · intro e he
          refine ⟨involution_coloring_update E w c1 (c' u) p hp hc1p ?_ e he,
            involution_coloring_update E w c1 (c' u) q hq hc1q ?_ e he⟩
          · intro _ _
            rw [hpw, hc1, Function.update_self]
            exact hux
          · intro _ _
            rw [hc1, Function.update_of_ne hxv]
            exact hux

theorem list_colorable_two_of_two_involutions {α : Type*} (E : Set α) (hE : E.Finite)
    (p q : α → α) (hp : Function.Involutive p) (hq : Function.Involutive q)
    (L : α → Finset ℕ) (hL : ∀ e ∈ E, 2 ≤ (L e).card) :
    ∃ c : α → ℕ, (∀ e ∈ E, c e ∈ L e) ∧
      ∀ e ∈ E, (p e ∈ E → p e ≠ e → c (p e) ≠ c e) ∧ (q e ∈ E → q e ≠ e → c (q e) ≠ c e) := by
  classical
  obtain ⟨c, hcL, hc⟩ := two_involutions_list_aux hE.toFinset.card hE.toFinset le_rfl p q hp hq
    L none (fun e he _ => hL e (hE.mem_toFinset.1 he)) (by simp)
  refine ⟨c, fun e he => hcL e (hE.mem_toFinset.2 he), fun e he => ?_⟩
  obtain ⟨h1, h2⟩ := hc e (hE.mem_toFinset.2 he)
  exact ⟨fun h h' => h1 (hE.mem_toFinset.2 h) h', fun h h' => h2 (hE.mem_toFinset.2 h) h'⟩
