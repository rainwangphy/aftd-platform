import AFTD.Prelude
import AFTD.Kb.Tcs.Bit

/-!
# op_258_hypercube_bipartite_decomposition

Topic: combinatorics   Node: cb6ddcfe6c8b

Provenance: helper lemma. step towards op_258_sum_ne_top_of_forces_three

For any l ≥ 1, the edge set of the complete graph on 2^l vertices can be partitioned into l bipartite layers (indexed by the first differing bit under a hypercube bijection) such that layer j has at most 2^{2l - 2 - j} edges.
-/

lemma op_258_hypercube_bipartite_decomposition_xor_ne {u v : ℕ} (h : u ≠ v) : u ^^^ v ≠ 0 := by
  intro h0
  apply h
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun n => n.testBit i) h0
  simp only [Nat.testBit_xor, Nat.zero_testBit] at this
  revert this
  cases u.testBit i <;> cases v.testBit i <;> simp

lemma op_258_hypercube_bipartite_decomposition_hi {u v : ℕ} (h : u ≠ v) :
    u / 2 ^ ((u ^^^ v).log2 + 1) = v / 2 ^ ((u ^^^ v).log2 + 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  have hlt : u ^^^ v < 2 ^ (i + ((u ^^^ v).log2 + 1)) :=
    lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  have := Nat.testBit_eq_false_of_lt hlt
  rw [Nat.testBit_xor] at this
  revert this
  cases u.testBit (i + ((u ^^^ v).log2 + 1)) <;> cases v.testBit (i + ((u ^^^ v).log2 + 1)) <;> simp

lemma op_258_hypercube_bipartite_decomposition_bit {u v : ℕ} (h : u ≠ v) :
    u.testBit (u ^^^ v).log2 ≠ v.testBit (u ^^^ v).log2 := by
  have := Nat.testBit_log2 (op_258_hypercube_bipartite_decomposition_xor_ne h)
  rw [Nat.testBit_xor] at this
  revert this
  cases u.testBit (u ^^^ v).log2 <;> cases v.testBit (u ^^^ v).log2 <;> simp

lemma op_258_hypercube_bipartite_decomposition_recon {p x y : ℕ}
    (hd : x / 2 ^ (p + 1) = y / 2 ^ (p + 1)) (hb : x.testBit p = y.testBit p)
    (hm : x % 2 ^ p = y % 2 ^ p) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rcases lt_trichotomy i p with hi | hi | hi
  · have := congrArg (fun n => n.testBit i) hm
    simpa [Nat.testBit_mod_two_pow, hi] using this
  · subst hi; exact hb
  · have := congrArg (fun n => n.testBit (i - (p + 1))) hd
    simp only [Nat.testBit_div_two_pow] at this
    rwa [Nat.sub_add_cancel (by omega)] at this

def op_258_hypercube_bipartite_decomposition_key (p u v : ℕ) : ℕ × ℕ × ℕ :=
  if u.testBit p = v.testBit p then (0, 0, 0)
  else if u.testBit p then (v / 2 ^ (p + 1), v % 2 ^ p, u % 2 ^ p)
  else (u / 2 ^ (p + 1), u % 2 ^ p, v % 2 ^ p)

lemma op_258_hypercube_bipartite_decomposition_key_symm (p u v : ℕ) :
    op_258_hypercube_bipartite_decomposition_key p u v =
      op_258_hypercube_bipartite_decomposition_key p v u := by
  unfold op_258_hypercube_bipartite_decomposition_key
  cases u.testBit p <;> cases v.testBit p <;> simp

lemma op_258_hypercube_bipartite_decomposition_key_inj {p a1 b1 a2 b2 : ℕ}
    (hab1 : a1 / 2 ^ (p + 1) = b1 / 2 ^ (p + 1)) (hab2 : a2 / 2 ^ (p + 1) = b2 / 2 ^ (p + 1))
    (ha1 : a1.testBit p = false) (hb1 : b1.testBit p = true)
    (ha2 : a2.testBit p = false) (hb2 : b2.testBit p = true)
    (h : (a1 / 2 ^ (p + 1), a1 % 2 ^ p, b1 % 2 ^ p) = (a2 / 2 ^ (p + 1), a2 % 2 ^ p, b2 % 2 ^ p)) :
    a1 = a2 ∧ b1 = b2 := by
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨op_258_hypercube_bipartite_decomposition_recon h1 (by rw [ha1, ha2]) h2,
    op_258_hypercube_bipartite_decomposition_recon (by rw [← hab1, h1, hab2]) (by rw [hb1, hb2]) h3⟩

/-- On an edge whose highest differing bit is `p`, the key lists the high part, then the low
part of the endpoint with bit `p` clear, then that of the other. -/
lemma op_258_hypercube_bipartite_decomposition_key_eq {p u v : ℕ}
    (hd : u.testBit p ≠ v.testBit p) :
    op_258_hypercube_bipartite_decomposition_key p u v =
      if u.testBit p then (v / 2 ^ (p + 1), v % 2 ^ p, u % 2 ^ p)
      else (u / 2 ^ (p + 1), u % 2 ^ p, v % 2 ^ p) := by
  unfold op_258_hypercube_bipartite_decomposition_key
  rw [if_neg hd]

/-- Bipartite layering of the complete graph on 2^l vertices with layer bounds 2^{2l - 2 - j}. -/
theorem op_258_hypercube_bipartite_decomposition (l : ℕ) (hl : 1 ≤ l) :
    ∃ (layer : (SimpleGraph.completeGraph (Fin (2^l))).edgeSet → Fin l)
      (f : Fin l → Fin (2^l) → Fin 2),
      (∀ (u v : Fin (2^l)) (hne : u ≠ v),
        f (layer ⟨s(u, v), by simp [SimpleGraph.completeGraph_eq_top, hne]⟩) u ≠
        f (layer ⟨s(u, v), by simp [SimpleGraph.completeGraph_eq_top, hne]⟩) v) ∧
      (∀ j : Fin l,
        ((Finset.univ : Finset (SimpleGraph.completeGraph (Fin (2^l))).edgeSet).filter
          (fun e => layer e = j)).card ≤ 2 ^ (2 * l - 2 - (j : ℕ))) := by
  classical
  -- the level of an edge: its highest differing bit
  have hsym : ∀ a b : Fin (2 ^ l), (a.val ^^^ b.val).log2 = (b.val ^^^ a.val).log2 := by
    intro a b; rw [Nat.xor_comm]
  -- facts about an edge `s(u, v)`
  have hfacts : ∀ u v : Fin (2 ^ l), u.val ≠ v.val →
      (u.val ^^^ v.val).log2 < l ∧
      u.val / 2 ^ ((u.val ^^^ v.val).log2 + 1) = v.val / 2 ^ ((u.val ^^^ v.val).log2 + 1) ∧
      u.val.testBit (u.val ^^^ v.val).log2 ≠ v.val.testBit (u.val ^^^ v.val).log2 := by
    intro u v h
    exact ⟨(Nat.log2_lt (op_258_hypercube_bipartite_decomposition_xor_ne h)).mpr
        (Nat.xor_lt_two_pow u.isLt v.isLt),
      op_258_hypercube_bipartite_decomposition_hi h,
      op_258_hypercube_bipartite_decomposition_bit h⟩
  refine ⟨fun e => ⟨l - 1 - Sym2.lift ⟨fun a b : Fin (2 ^ l) => (a.val ^^^ b.val).log2, hsym⟩ e.1,
      by omega⟩,
    fun j w => if w.val.testBit (l - 1 - j.val) then 1 else 0, ?_, ?_⟩
  · intro u v hne
    have hne' : u.val ≠ v.val := fun h => hne (Fin.ext h)
    obtain ⟨hlt, -, hb⟩ := hfacts u v hne'
    have e : l - 1 - (l - 1 - (u.val ^^^ v.val).log2) = (u.val ^^^ v.val).log2 := by omega
    simp only [Sym2.lift_mk, Fin.val_mk, e]
    revert hb
    cases u.val.testBit (u.val ^^^ v.val).log2 <;>
      cases v.val.testBit (u.val ^^^ v.val).log2 <;> decide
  · intro j
    have hj : j.val < l := j.isLt
    set p := l - 1 - j.val with hp
    -- an edge of layer `j` has highest differing bit `p`
    have hlevel : ∀ (u v : Fin (2 ^ l)), u.val ≠ v.val →
        l - 1 - (u.val ^^^ v.val).log2 = j.val → (u.val ^^^ v.val).log2 = p := by
      intro u v h h'
      have := (hfacts u v h).1
      omega
    have hne_of : ∀ (u v : Fin (2 ^ l)),
        s(u, v) ∈ (SimpleGraph.completeGraph (Fin (2 ^ l))).edgeSet → u.val ≠ v.val := by
      intro u v h huv
      apply (show u ≠ v by simpa [SimpleGraph.completeGraph_eq_top] using h)
      exact Fin.ext huv
    calc ((Finset.univ : Finset (SimpleGraph.completeGraph (Fin (2^l))).edgeSet).filter
          (fun e => (⟨l - 1 - Sym2.lift ⟨fun a b : Fin (2 ^ l) => (a.val ^^^ b.val).log2, hsym⟩ e.1,
            by omega⟩ : Fin l) = j)).card
        ≤ (Finset.range (2 ^ (l - 1 - p)) ×ˢ Finset.range (2 ^ p) ×ˢ Finset.range (2 ^ p)).card := by
          refine Finset.card_le_card_of_injOn (fun e => Sym2.lift
            ⟨fun a b : Fin (2 ^ l) => op_258_hypercube_bipartite_decomposition_key p a.val b.val,
              fun a b => op_258_hypercube_bipartite_decomposition_key_symm p _ _⟩ e.1) ?_ ?_
          · intro e he
            have he' := congrArg Fin.val (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
            obtain ⟨e, hee⟩ := e
            induction e using Sym2.ind with
            | h u v =>
              have huv := hne_of u v hee
              simp only [Sym2.lift_mk] at he'
              have hX := hlevel u v huv he'
              obtain ⟨-, hhi, hb⟩ := hfacts u v huv
              rw [hX] at hhi hb
              simp only [Sym2.lift_mk, Finset.coe_product, Finset.coe_range, Set.mem_prod,
                Set.mem_Iio, Finset.mem_coe, Finset.mem_product, Finset.mem_range]
              rw [op_258_hypercube_bipartite_decomposition_key_eq hb]
              have hpow : 2 ^ (l - 1 - p) * 2 ^ (p + 1) = 2 ^ l := by
                rw [← pow_add]; congr 1; omega
              have hdiv : ∀ w : Fin (2 ^ l), w.val / 2 ^ (p + 1) < 2 ^ (l - 1 - p) := by
                intro w
                rw [Nat.div_lt_iff_lt_mul (by positivity), hpow]
                exact w.isLt
              split_ifs
              · exact ⟨hdiv v, Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity)⟩
              · exact ⟨hdiv u, Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity)⟩
          · intro e1 he1 e2 he2 heq
            have he1' := congrArg Fin.val (Finset.mem_filter.mp (Finset.mem_coe.mp he1)).2
            have he2' := congrArg Fin.val (Finset.mem_filter.mp (Finset.mem_coe.mp he2)).2
            obtain ⟨e1, hee1⟩ := e1
            obtain ⟨e2, hee2⟩ := e2
            induction e1 using Sym2.ind with
            | h u1 v1 =>
            induction e2 using Sym2.ind with
            | h u2 v2 =>
              have huv1 := hne_of u1 v1 hee1
              have huv2 := hne_of u2 v2 hee2
              simp only [Sym2.lift_mk] at he1' he2' heq
              have hX1 := hlevel u1 v1 huv1 he1'
              have hX2 := hlevel u2 v2 huv2 he2'
              obtain ⟨-, hhi1, hb1⟩ := hfacts u1 v1 huv1
              obtain ⟨-, hhi2, hb2⟩ := hfacts u2 v2 huv2
              rw [hX1] at hhi1 hb1
              rw [hX2] at hhi2 hb2
              rw [op_258_hypercube_bipartite_decomposition_key_eq hb1,
                op_258_hypercube_bipartite_decomposition_key_eq hb2] at heq
              apply Subtype.ext
              show s(u1, v1) = s(u2, v2)
              cases hu1 : u1.val.testBit p <;> cases hv1 : v1.val.testBit p <;>
                cases hu2 : u2.val.testBit p <;> cases hv2 : v2.val.testBit p <;>
                simp only [hu1, hv1, hu2, hv2, ne_eq, eq_self_iff_true, not_true_eq_false, not_false_eq_true, Bool.false_eq_true, Bool.true_eq_false,
                  if_true, if_false] at hb1 hb2 heq ⊢
              · obtain ⟨h1, h2⟩ := op_258_hypercube_bipartite_decomposition_key_inj
                  hhi1 hhi2 hu1 hv1 hu2 hv2 heq
                rw [Fin.ext h1, Fin.ext h2]
              · obtain ⟨h1, h2⟩ := op_258_hypercube_bipartite_decomposition_key_inj
                  hhi1 hhi2.symm hu1 hv1 hv2 hu2 heq
                rw [Fin.ext h1, Fin.ext h2, Sym2.eq_swap]
              · obtain ⟨h1, h2⟩ := op_258_hypercube_bipartite_decomposition_key_inj
                  hhi1.symm hhi2 hv1 hu1 hu2 hv2 heq
                rw [← Fin.ext h1, ← Fin.ext h2, Sym2.eq_swap]
              · obtain ⟨h1, h2⟩ := op_258_hypercube_bipartite_decomposition_key_inj
                  hhi1.symm hhi2.symm hv1 hu1 hv2 hu2 heq
                rw [Fin.ext h1, Fin.ext h2]
      _ = 2 ^ (2 * l - 2 - (j : ℕ)) := by
          simp only [Finset.card_product, Finset.card_range, ← pow_add]
          congr 1
          omega
