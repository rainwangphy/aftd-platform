import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZeroForcingRootExposedFort
import AFTD.Kb.Tcs.ZeroForcingFinsetIterDecides
import AFTD.Kb.Tcs.ZfsComplIffNoStuck
import AFTD.Kb.Tcs.ZeroForced

/-!
# tree_one_blue_bounded_exposure_not_ulc

Topic: graphs   Node: 9b479ae575b7

Provenance: helper lemma.

There is a ten-vertex rooted tree for which fixing just one leaf blue causes the root-exposure mixture at weight one half to fail binomial-normalized log-concavity.
-/

namespace TreeOneBlueIN928

def adjN (u v : Fin 10) : Prop := u.val + 1 = v.val ∨ v.val + 1 = u.val
instance : DecidableRel adjN := fun u v => by unfold adjN; infer_instance

def T10 : SimpleGraph (Fin 10) where
  Adj := adjN
  symm := ⟨fun u v h => by unfold adjN at *; omega⟩
  loopless := ⟨fun u h => by unfold adjN at h; omega⟩

instance : DecidableRel T10.Adj := fun u v => inferInstanceAs (Decidable (adjN u v))

def PN (F : Finset (Fin 10)) : Prop :=
  (∃ w ∈ F, adjN 3 w) ∧ ∀ u : Fin 10, u ≠ 3 → u ∉ F → ∀ w : Fin 10, w ∈ F → adjN u w →
    ∃ x : Fin 10, x ∈ F ∧ adjN u x ∧ x ≠ w
instance : DecidablePred PN := fun F => by unfold PN; infer_instance

def QN (W : Finset (Fin 10)) : Prop :=
  4 ∈ W ∧ 9 ∈ W ∧ ¬ (5 ∉ W ∧ 6 ∉ W) ∧ ¬ (6 ∉ W ∧ 7 ∉ W) ∧ ¬ (7 ∉ W ∧ 8 ∉ W)
instance : DecidablePred QN := fun F => by unfold QN; infer_instance

set_option maxRecDepth 100000 in
theorem PN_QN : ∀ F : Finset (Fin 10), 0 ∉ F → 3 ∉ F → PN F → QN F := by decide +kernel
set_option maxRecDepth 100000 in
theorem QN_PN : ∀ W : Finset (Fin 10), QN W → PN (W.filter (fun v => 4 ≤ v.val)) := by decide +kernel

theorem zf_all (S : Finset (Fin 10)) (h0 : (0 : Fin 10) ∉ S) :
    is_zero_forcing_set T10 ((Finset.univ \ S : Finset (Fin 10)) : Set (Fin 10)) := by
  have key : ∀ i : ℕ, ∀ j : Fin 10, j.val ≤ i →
      ZeroForced T10 ((Finset.univ \ S : Finset (Fin 10)) : Set (Fin 10)) j := by
    intro i
    induction i with
    | zero =>
      intro j hj
      apply ZeroForced.init
      have : j = 0 := Fin.ext (by simp; omega)
      subst this; simpa using h0
    | succ i ih =>
      intro j hj
      rcases Nat.lt_or_ge j.val (i + 1) with h | h
      · exact ih j (by omega)
      · have hj' : j.val = i + 1 := by omega
        have hi : i < 10 := by omega
        refine ZeroForced.step ⟨i, hi⟩ j (ih _ le_rfl) (by change adjN _ _; unfold adjN; simp; omega) ?_
        intro x hx hxj
        change adjN _ _ at hx; unfold adjN at hx
        have : x.val ≠ j.val := fun h => hxj (Fin.ext h)
        apply ih; simp at hx; omega
  intro v; exact key v.val v le_rfl

theorem fort_iff (W : Finset (Fin 10)) (h0 : (0 : Fin 10) ∉ W) :
    zero_forcing_root_exposed_fort T10 3 W ↔ QN W := by
  constructor
  · rintro ⟨F, hFW, h3, hex, hall⟩
    have hq := PN_QN F (fun h => h0 (hFW h)) h3 ⟨hex, hall⟩
    obtain ⟨a1, a2, a3, a4, a5⟩ := hq
    exact ⟨hFW a1, hFW a2, fun ⟨h1, h2⟩ => a3 ⟨mt (@hFW _) h1, mt (@hFW _) h2⟩,
      fun ⟨h1, h2⟩ => a4 ⟨mt (@hFW _) h1, mt (@hFW _) h2⟩,
      fun ⟨h1, h2⟩ => a5 ⟨mt (@hFW _) h1, mt (@hFW _) h2⟩⟩
  · intro hq
    obtain ⟨hex, hall⟩ := QN_PN W hq
    exact ⟨W.filter (fun v => 4 ≤ v.val), Finset.filter_subset _ _, by simp, hex, hall⟩

set_option maxRecDepth 100000 in
theorem cnt7a : (Finset.univ.filter fun S : Finset (Fin 10) => 0 ∉ S ∧ S.card = 7 ∧ ¬ QN S).card = 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem cnt7c : (Finset.univ.filter fun S : Finset (Fin 10) => 0 ∉ S ∧ S.card = 7 ∧ QN S).card = 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem cnt8a : (Finset.univ.filter fun S : Finset (Fin 10) => 0 ∉ S ∧ S.card = 8 ∧ ¬ QN S).card = 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem cnt8c : (Finset.univ.filter fun S : Finset (Fin 10) => 0 ∉ S ∧ S.card = 8 ∧ QN S).card = 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem cnt9a : (Finset.univ.filter fun S : Finset (Fin 10) => 0 ∉ S ∧ S.card = 9 ∧ ¬ QN S).card = 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem cnt9c : (Finset.univ.filter fun S : Finset (Fin 10) => 0 ∉ S ∧ S.card = 9 ∧ QN S).card = 1 := by decide +kernel

theorem T10_eq : T10 = SimpleGraph.pathGraph 10 := by
  ext u v; simp [SimpleGraph.pathGraph_adj, T10, adjN]

set_option maxRecDepth 10000 in
theorem T10_tree : T10.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨T10_eq ▸ SimpleGraph.pathGraph_connected 9, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

end TreeOneBlueIN928

theorem tree_one_blue_bounded_exposure_not_ulc : ∃ (T : SimpleGraph (Fin 10)) (p b : Fin 10), T.IsTree ∧ p ≠ b ∧ (∃! v, T.Adj b v) ∧ (let a := fun k : ℕ => {S : Finset (Fin 10) | b ∉ S ∧ S.card = k ∧ is_zero_forcing_set T ((Finset.univ \ S : Finset (Fin 10)) : Set (Fin 10)) ∧ ¬ zero_forcing_root_exposed_fort T p S}.ncard; let c := fun k : ℕ => {S : Finset (Fin 10) | b ∉ S ∧ S.card = k ∧ is_zero_forcing_set T ((Finset.univ \ S : Finset (Fin 10)) : Set (Fin 10)) ∧ zero_forcing_root_exposed_fort T p S}.ncard; 2 * a 7 + c 7 = 54 ∧ 2 * a 8 + c 8 = 11 ∧ 2 * a 9 + c 9 = 1) := by
  refine ⟨TreeOneBlueIN928.T10, 3, 0, TreeOneBlueIN928.T10_tree, by decide, ⟨1, by decide, fun v hv => ?_⟩, ?_⟩
  · change TreeOneBlueIN928.adjN 0 v at hv; unfold TreeOneBlueIN928.adjN at hv; ext; simp at hv ⊢; omega
  · have ha : ∀ k, {S : Finset (Fin 10) | 0 ∉ S ∧ S.card = k ∧ is_zero_forcing_set TreeOneBlueIN928.T10 ((Finset.univ \ S : Finset (Fin 10)) : Set (Fin 10)) ∧ ¬ zero_forcing_root_exposed_fort TreeOneBlueIN928.T10 3 S}
        = ↑(Finset.univ.filter fun S : Finset (Fin 10) => 0 ∉ S ∧ S.card = k ∧ ¬ TreeOneBlueIN928.QN S) := by
      intro k; ext S
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h0, hk, _, hf⟩; exact ⟨h0, hk, fun hq => hf ((TreeOneBlueIN928.fort_iff S h0).2 hq)⟩
      · rintro ⟨h0, hk, hq⟩; exact ⟨h0, hk, TreeOneBlueIN928.zf_all S h0, fun hf => hq ((TreeOneBlueIN928.fort_iff S h0).1 hf)⟩
    have hc : ∀ k, {S : Finset (Fin 10) | 0 ∉ S ∧ S.card = k ∧ is_zero_forcing_set TreeOneBlueIN928.T10 ((Finset.univ \ S : Finset (Fin 10)) : Set (Fin 10)) ∧ zero_forcing_root_exposed_fort TreeOneBlueIN928.T10 3 S}
        = ↑(Finset.univ.filter fun S : Finset (Fin 10) => 0 ∉ S ∧ S.card = k ∧ TreeOneBlueIN928.QN S) := by
      intro k; ext S
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h0, hk, _, hf⟩; exact ⟨h0, hk, (TreeOneBlueIN928.fort_iff S h0).1 hf⟩
      · rintro ⟨h0, hk, hq⟩; exact ⟨h0, hk, TreeOneBlueIN928.zf_all S h0, (TreeOneBlueIN928.fort_iff S h0).2 hq⟩
    intro a c
    simp only [a, c, ha, hc, Set.ncard_coe_finset, TreeOneBlueIN928.cnt7a, TreeOneBlueIN928.cnt7c, TreeOneBlueIN928.cnt8a, TreeOneBlueIN928.cnt8c, TreeOneBlueIN928.cnt9a, TreeOneBlueIN928.cnt9c]
    norm_num
