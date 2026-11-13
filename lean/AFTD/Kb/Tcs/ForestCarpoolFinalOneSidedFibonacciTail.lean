import AFTD.Prelude
import AFTD.Kb.Tcs.ForestCarpoolFinalDiscrepancy
import AFTD.Kb.Tcs.ForestCarpoolTailEnvelope
import AFTD.Kb.Tcs.CarpoolForestEdgeSequence
import AFTD.Kb.Tcs.ForestCarpoolDisjointComponentsIndependent
import AFTD.Kb.Tcs.ForestGreedyEnvelopePreservedByIndependentMerge
import AFTD.Kb.Tcs.CarpoolStep
import AFTD.Kb.Tcs.ForestCarpoolComponentCoinLocality
import AFTD.Kb.Tcs.ForestGreedyLawEnveloped
import AFTD.Kb.Tcs.ValidCarpoolEdgeSequence
import AFTD.Kb.Tcs.ForestCarpoolAppendEdgeDisconnected
import AFTD.Kb.Tcs.ForestGreedySignedStep
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# forest_carpool_final_one_sided_fibonacci_tail

Topic: online_algorithms   Node: de69970b3e1f

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

For any forest arrival sequence and any vertex, the finite uniform probability that its final greedy discrepancy is at least D is bounded by the stated Fibonacci envelope.
-/

namespace ForestCarpoolTail

theorem card_comp_equiv' {γ δ : Type} [Fintype γ] [Fintype δ] (Φ : γ ≃ δ) (f : δ → Prop)
    [DecidablePred f] :
    (Finset.univ.filter (fun p => f (Φ p))).card = (Finset.univ.filter f).card := by
  refine Finset.card_nbij' Φ Φ.symm ?_ ?_ (fun p _ => Φ.symm_apply_apply p)
    (fun p _ => Φ.apply_symm_apply p)
  · intro p hp; simpa using hp
  · intro p hp; simpa using hp

/-- enveloped laws are invariant under a change of coin space by an equivalence -/
theorem enveloped_equiv {γ δ : Type} [Fintype γ] [Fintype δ] (Φ : γ ≃ δ) (X : δ → ℤ)
    (h : forest_greedy_law_enveloped δ X) :
    forest_greedy_law_enveloped γ (fun p => X (Φ p)) := by
  obtain ⟨⟨p, hp⟩, hs, ht⟩ := h
  refine ⟨⟨p, fun a => hp _⟩, fun z => ?_, fun k hk => ?_⟩
  · rw [card_comp_equiv' Φ (fun q => X q = z), card_comp_equiv' Φ (fun q => X q = -z)]
    exact hs z
  · rw [card_comp_equiv' Φ (fun q => (k : ℤ) ≤ X q), Fintype.card_congr Φ]
    exact ht k hk

/-- an extra unused fair coin does not change the law -/
theorem enveloped_extra {α : Type} [Fintype α] (X : α → ℤ)
    (h : forest_greedy_law_enveloped α X) :
    forest_greedy_law_enveloped (α × Bool) (fun p => X p.1) := by
  obtain ⟨⟨p, hp⟩, hs, ht⟩ := h
  have hc : ∀ (f : ℤ → Prop) [DecidablePred f],
      (Finset.univ.filter (fun q : α × Bool => f (X q.1))).card =
        (Finset.univ.filter (fun a => f (X a))).card * 2 := by
    intro f _
    have : (Finset.univ.filter (fun q : α × Bool => f (X q.1))) =
        (Finset.univ.filter (fun a => f (X a))) ×ˢ (Finset.univ : Finset Bool) := by
      ext q; simp
    rw [this, Finset.card_product, Finset.card_univ, Fintype.card_bool]
  refine ⟨⟨p, fun a => hp _⟩, fun z => ?_, fun k hk => ?_⟩
  · rw [hc (fun x => x = z), hc (fun x => x = -z), hs z]
  · rw [hc (fun x => (k : ℤ) ≤ x), Fintype.card_prod, Fintype.card_bool]
    have := ht k hk
    push_cast
    rwa [mul_div_mul_right _ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- the transfer from the independent product law to the joint law on disjoint components -/
theorem enveloped_diag {L : ℕ} (A B : (Fin L → Bool) → ℤ)
    (mix : (Fin L → Bool) → (Fin L → Bool) → (Fin L → Bool))
    (hA : ∀ r s, A (mix r s) = A r) (hB : ∀ r s, B (mix r s) = B s)
    (hmix : ∀ r s, mix (mix r s) (mix s r) = r)
    (F : ℤ → ℤ → Bool → ℤ)
    (h : forest_greedy_law_enveloped ((Fin L → Bool) × (Fin L → Bool) × Bool)
      (fun p => F (A p.1) (B p.2.1) p.2.2)) :
    forest_greedy_law_enveloped ((Fin L → Bool) × Bool) (fun p => F (A p.1) (B p.1) p.2) := by
  obtain ⟨⟨p, hp⟩, hs, ht⟩ := h
  have hc : ∀ (f : ℤ → Prop) [DecidablePred f],
      (Finset.univ.filter (fun q : (Fin L → Bool) × (Fin L → Bool) × Bool =>
        f (F (A q.1) (B q.2.1) q.2.2))).card =
      (Finset.univ.filter (fun q : (Fin L → Bool) × Bool => f (F (A q.1) (B q.1) q.2))).card *
        2 ^ L := by
    intro f _
    let φ : (Fin L → Bool) × (Fin L → Bool) × Bool → (Fin L → Bool) × (Fin L → Bool) × Bool :=
      fun q => (mix q.1 q.2.1, mix q.2.1 q.1, q.2.2)
    have hφ : ∀ q, φ (φ q) = q := by
      rintro ⟨r, s, c⟩; simp only [φ, hmix]
    have h1 : (Finset.univ.filter (fun q : (Fin L → Bool) × (Fin L → Bool) × Bool =>
        f (F (A q.1) (B q.2.1) q.2.2))).card =
        (Finset.univ.filter (fun q : (Fin L → Bool) × (Fin L → Bool) × Bool =>
        f (F (A q.1) (B q.1) q.2.2))).card := by
      refine Finset.card_nbij' φ φ ?_ ?_ (fun q _ => hφ q) (fun q _ => hφ q)
      · rintro ⟨r, s, c⟩ hq
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hq ⊢
        simp only [φ, hA, hB]; exact hq
      · rintro ⟨r, s, c⟩ hq
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hq ⊢
        simp only [φ, hA, hB]; exact hq
    rw [h1]
    let ψ : (Fin L → Bool) × (Fin L → Bool) × Bool ≃ ((Fin L → Bool) × Bool) × (Fin L → Bool) :=
      { toFun := fun q => ((q.1, q.2.2), q.2.1)
        invFun := fun q => (q.1.1, q.2, q.1.2)
        left_inv := fun q => rfl
        right_inv := fun q => rfl }
    rw [← card_comp_equiv' ψ.symm (fun q => f (F (A q.1) (B q.1) q.2.2))]
    have : (Finset.univ.filter (fun q : ((Fin L → Bool) × Bool) × (Fin L → Bool) =>
        f (F (A (ψ.symm q).1) (B (ψ.symm q).1) (ψ.symm q).2.2))) =
        (Finset.univ.filter (fun q : (Fin L → Bool) × Bool => f (F (A q.1) (B q.1) q.2))) ×ˢ
          (Finset.univ : Finset (Fin L → Bool)) := by
      ext q; simp [ψ]
    rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  have hpos : 0 < 2 ^ L := by positivity
  refine ⟨⟨p, fun q => hp (q.1, q.1, q.2)⟩, fun z => ?_, fun k hk => ?_⟩
  · have e1 := hc (fun x => x = z)
    have e2 := hc (fun x => x = -z)
    have := hs z
    rw [e1, e2] at this
    exact Nat.eq_of_mul_eq_mul_right hpos this
  · have := ht k hk
    rw [hc (fun x => (k : ℤ) ≤ x)] at this
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this ⊢
    push_cast at this ⊢
    convert this using 1
    field_simp


open ForestCarpoolLocal in
theorem G_append (n : ℕ) (e : Fin n × Fin n) (c : Bool) :
    ∀ (es : List (Fin n × Fin n)) (cs : List Bool) (d : Fin n → ℤ), cs.length = es.length →
    G n (es ++ [e]) (cs ++ [c]) d = carpool_step n (G n es cs d) e (gbit (G n es cs d) e c) := by
  intro es
  induction es with
  | nil =>
    intro cs d h
    cases cs with
    | nil => simp [G]
    | cons _ _ => simp at h
  | cons e' es ih =>
    intro cs d h
    cases cs with
    | nil => simp at h
    | cons c' cs =>
      simp only [List.cons_append, G]
      exact ih cs _ (by simpa using h)

/-- coin space of an appended edge -/
def coinEquiv (L m : ℕ) (hm : m = L + 1) : (Fin L → Bool) × Bool ≃ (Fin m → Bool) where
  toFun p := fun i => if h : i.val < L then p.1 ⟨i.val, h⟩ else p.2
  invFun f := (fun j => f ⟨j.val, by omega⟩, f ⟨L, by omega⟩)
  left_inv p := by
    obtain ⟨r, c⟩ := p
    ext j
    · simp
    · simp
  right_inv f := by
    funext i
    by_cases h : i.val < L
    · simp [h]
    · simp only [h, dite_false]
      congr 1; ext; simp; omega

theorem ofFn_coinEquiv (L m : ℕ) (hm : m = L + 1) (r : Fin L → Bool) (c : Bool) :
    List.ofFn (coinEquiv L m hm (r, c)) = List.ofFn r ++ [c] := by
  apply List.ext_getElem
  · simp [hm]
  · intro i h1 h2
    simp only [List.getElem_ofFn, coinEquiv, Equiv.coe_fn_mk]
    rw [List.getElem_append]
    split_ifs with h3 h4 h4
    · simp
    · simp at h4; omega
    · simp at h4; omega
    · simp

theorem final_append (n : ℕ) (es : List (Fin n × Fin n)) (e : Fin n × Fin n)
    (p : (Fin es.length → Bool) × Bool) :
    forest_carpool_final_discrepancy n (es ++ [e])
        (coinEquiv es.length (es ++ [e]).length (by simp) p) =
      carpool_step n (forest_carpool_final_discrepancy n es p.1) e
        (ForestCarpoolLocal.gbit (forest_carpool_final_discrepancy n es p.1) e p.2) := by
  obtain ⟨r, c⟩ := p
  rw [ForestCarpoolLocal.final_eq, ForestCarpoolLocal.final_eq, ofFn_coinEquiv,
    G_append n e c es _ _ (by simp)]

theorem step_at_u (n : ℕ) (d : Fin n → ℤ) (u v : Fin n) (huv : u ≠ v) (c : Bool) :
    carpool_step n d (u, v) (ForestCarpoolLocal.gbit d (u, v) c) u =
      forest_greedy_signed_step (d u) (d v) c := by
  simp only [carpool_step, ForestCarpoolLocal.gbit, forest_greedy_signed_step, if_neg huv]
  cases c <;> split_ifs <;> first | omega | (exfalso; simp_all)

theorem step_at_v (n : ℕ) (d : Fin n → ℤ) (u v : Fin n) (huv : u ≠ v) (c : Bool) :
    carpool_step n d (u, v) (ForestCarpoolLocal.gbit d (u, v) c) v =
      forest_greedy_signed_step (d v) (d u) (!c) := by
  simp only [carpool_step, ForestCarpoolLocal.gbit, forest_greedy_signed_step, if_neg huv.symm]
  cases c <;> split_ifs <;> first | omega | (exfalso; simp_all)

theorem step_at_other (n : ℕ) (d : Fin n → ℤ) (u v w : Fin n) (hu : w ≠ u) (hv : w ≠ v)
    (b : Bool) : carpool_step n d (u, v) b w = d w := by
  simp [carpool_step, hu, hv]

theorem forest_init (n : ℕ) (es : List (Fin n × Fin n)) (e : Fin n × Fin n)
    (hf : CarpoolForestEdgeSequence n (es ++ [e])) : CarpoolForestEdgeSequence n es := by
  obtain ⟨hv, hnd, hac⟩ := hf
  refine ⟨fun x hx => hv x (List.mem_append_left _ hx), ?_, ?_⟩
  · rw [List.map_append] at hnd; exact hnd.sublist (List.sublist_append_left _ _)
  · refine hac.anti ?_
    intro x y hxy
    rw [SimpleGraph.fromEdgeSet_adj] at hxy ⊢
    obtain ⟨⟨e', he', hex⟩, hne⟩ := hxy
    exact ⟨⟨e', List.mem_append_left _ he', hex⟩, hne⟩

theorem env_pair (n : ℕ) (es : List (Fin n × Fin n)) (x y : Fin n)
    (hxy : ¬ (SimpleGraph.fromEdgeSet {s(e.1, e.2) | e ∈ es}).Reachable x y)
    (F : ℤ → ℤ → Bool → ℤ)
    (h : forest_greedy_law_enveloped ((Fin es.length → Bool) × (Fin es.length → Bool) × Bool)
      (fun p => F (forest_carpool_final_discrepancy n es p.1 x)
        (forest_carpool_final_discrepancy n es p.2.1 y) p.2.2)) :
    forest_greedy_law_enveloped ((Fin es.length → Bool) × Bool)
      (fun p => F (forest_carpool_final_discrepancy n es p.1 x)
        (forest_carpool_final_discrepancy n es p.1 y) p.2) := by
  classical
  set Γ := SimpleGraph.fromEdgeSet {s(e.1, e.2) | e ∈ es}
  let mix : (Fin es.length → Bool) → (Fin es.length → Bool) → (Fin es.length → Bool) :=
    fun r s i => if Γ.Reachable x (es.get i).1 then r i else s i
  refine enveloped_diag (fun r => forest_carpool_final_discrepancy n es r x)
    (fun r => forest_carpool_final_discrepancy n es r y) mix ?_ ?_ ?_ F h
  · intro r s
    apply forest_carpool_component_coin_locality
    intro i hi
    have hi' : Γ.Reachable x (es.get i).1 := hi
    simp only [mix, if_pos hi']
  · intro r s
    apply forest_carpool_component_coin_locality
    intro i hi
    have : ¬ Γ.Reachable x (es.get i).1 := fun h => hxy (h.trans hi.symm)
    simp only [mix, if_neg this]
  · intro r s; funext i; simp only [mix]; split_ifs <;> rfl

theorem env_all (n : ℕ) : ∀ es : List (Fin n × Fin n), CarpoolForestEdgeSequence n es →
    ∀ w, forest_greedy_law_enveloped (Fin es.length → Bool)
      (fun r => forest_carpool_final_discrepancy n es r w) := by
  intro es
  induction es using List.reverseRecOn with
  | nil =>
    intro _ w
    have h0 : ∀ r : Fin ([] : List (Fin n × Fin n)).length → Bool,
        forest_carpool_final_discrepancy n [] r w = 0 := by
      intro r; rw [ForestCarpoolLocal.final_eq]; simp [ForestCarpoolLocal.G]
    refine ⟨⟨0, fun r => by show forest_carpool_final_discrepancy n [] r w % 2 = 0; rw [h0]; rfl⟩, fun z => ?_, fun k hk => ?_⟩
    · simp only [h0]; congr 1; ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    · have : (Finset.univ.filter (fun r : Fin ([] : List (Fin n × Fin n)).length → Bool =>
          (k : ℤ) ≤ forest_carpool_final_discrepancy n [] r w)) = ∅ := by
        ext r; simp only [h0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]; omega
      rw [this, Finset.card_empty, Nat.cast_zero, zero_div]
      unfold forest_carpool_tail_envelope; split_ifs <;> positivity
  | append_singleton es e ih =>
    intro hf w
    obtain ⟨u, v⟩ := e
    have hf0 := forest_init n es (u, v) hf
    have ih' := ih hf0
    have huv : u ≠ v := hf.1 (u, v) (by simp)
    have hdis := forest_carpool_append_edge_disconnected n es u v hf
    have key : forest_greedy_law_enveloped ((Fin es.length → Bool) × Bool)
        (fun p => forest_carpool_final_discrepancy n (es ++ [(u, v)])
          (coinEquiv es.length (es ++ [(u, v)]).length (by simp) p) w) := by
      simp only [final_append]
      by_cases hwu : w = u
      · subst hwu
        simp only [step_at_u n _ _ _ huv]
        exact env_pair n es w v hdis forest_greedy_signed_step
          (forest_greedy_envelope_preserved_by_independent_merge _ _ _ _ (ih' w) (ih' v))
      · by_cases hwv : w = v
        · subst hwv
          simp only [step_at_v n _ _ _ huv]
          have hm := forest_greedy_envelope_preserved_by_independent_merge _ _ _ _ (ih' w) (ih' u)
          have hm' := enveloped_equiv
            ((Equiv.refl _).prodCongr ((Equiv.refl _).prodCongr Equiv.boolNot)) _ hm
          exact env_pair n es w u (fun h => hdis h.symm)
            (fun a b c => forest_greedy_signed_step a b (!c)) hm'
        · simp only [step_at_other n _ _ _ _ hwu hwv]
          exact enveloped_extra _ (ih' w)
    have := enveloped_equiv (coinEquiv es.length (es ++ [(u, v)]).length (by simp)).symm _ key
    simpa using this

end ForestCarpoolTail

theorem forest_carpool_final_one_sided_fibonacci_tail (n : ℕ)
    (edges : List (Fin n × Fin n)) (hf : CarpoolForestEdgeSequence n edges)
    (v : Fin n) (D : ℕ) (hD : 1 ≤ D) :
  (((Finset.univ.filter (fun r : Fin edges.length → Bool =>
    (D : ℤ) ≤ forest_carpool_final_discrepancy n edges r v)).card : ℝ) /
    (2 ^ edges.length : ℝ)) ≤ forest_carpool_tail_envelope D := by
  have := (ForestCarpoolTail.env_all n edges hf v).2.2 D hD
  simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using this
