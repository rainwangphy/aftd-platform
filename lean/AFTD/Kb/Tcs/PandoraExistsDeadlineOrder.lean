import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.IsPartiallyAdaptive
import AFTD.Kb.Tcs.ExpectedUtilityDUS
import AFTD.Kb.Tcs.PandoraDeadlineFeasible
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# pandora_exists_deadline_order

Topic: online_algorithms   Node: 1cc11377ef2e

Provenance: helper lemma. Helper for op184_partially_adaptive_half_approximation: arXiv:2610.13775 Section 3, Lemma 2 (feasibility test)

Lemma 2: a deadline-feasible set can be listed without repetition so that the j-th box (j from 1) has deadline at least j.
-/

open scoped Prod.Lex

def pandora_boxOrderEmb (inst : PandoraDeadlineInstance) : Fin inst.n ↪ Lex (ℕ × Fin inst.n) where
  toFun i := toLex (inst.deadline i, i)
  inj' _ _ h := by
    have h' := ofLex.injective h
    exact (Prod.ext_iff.mp h').2

lemma pandora_deadline_of_mem_emb (inst : PandoraDeadlineInstance) (S : Finset (Fin inst.n))
    (p : Lex (ℕ × Fin inst.n)) (hp : p ∈ S.map (pandora_boxOrderEmb inst)) :
    (ofLex p).1 = inst.deadline ((ofLex p).2) := by
  rcases Finset.mem_map.mp hp with ⟨b, _, rfl⟩
  rfl

lemma pandora_lex_fst_le {α β : Type*} [LinearOrder α] [LinearOrder β]
    {x y : Lex (α × β)} (h : x ≤ y) : (ofLex x).1 ≤ (ofLex y).1 := by
  rcases Prod.Lex.le_iff.mp h with (h1 | ⟨h1, _⟩)
  · exact le_of_lt h1
  · exact le_of_eq h1

theorem pandora_exists_deadline_order (inst : PandoraDeadlineInstance) (S : Finset (Fin inst.n))
    (hS : pandora_deadline_feasible inst S) :
    ∃ order : List (Fin inst.n), order.Nodup ∧ order.toFinset = S ∧
      ∀ (j : ℕ) (hj : j < order.length), j + 1 ≤ inst.deadline (order.get ⟨j, hj⟩) := by
  let S' := S.map (pandora_boxOrderEmb inst)
  let L' := S'.sort (· ≤ ·)
  let order := L'.map (fun (p : Lex (ℕ × Fin inst.n)) => (ofLex p).2)
  have hL' : L'.Nodup := Finset.sort_nodup _ _
  have h_inj_on : ∀ x ∈ L', ∀ y ∈ L', (ofLex x).2 = (ofLex y).2 → x = y := by
    intro x hx y hy hxy
    have hxS' : x ∈ S' := (Finset.mem_sort (· ≤ ·)).mp hx
    have hyS' : y ∈ S' := (Finset.mem_sort (· ≤ ·)).mp hy
    rcases Finset.mem_map.mp hxS' with ⟨a, _, rfl⟩
    rcases Finset.mem_map.mp hyS' with ⟨b, _, rfl⟩
    have hab : a = b := hxy
    rw [hab]
  have h_nodup : order.Nodup := List.Nodup.map_on h_inj_on hL'
  have h_toFinset : order.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    dsimp [order]
    rw [List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hpS' : p ∈ S' := (Finset.mem_sort (· ≤ ·)).mp hp
      rcases Finset.mem_map.mp hpS' with ⟨b, hb, rfl⟩
      exact hb
    · intro ha
      refine ⟨pandora_boxOrderEmb inst a, ?_, rfl⟩
      rw [Finset.mem_sort]
      exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
  refine ⟨order, h_nodup, h_toFinset, ?_⟩
  intro j hj
  set D := inst.deadline (order.get ⟨j, hj⟩)
  let f : Fin (j + 1) → Fin inst.n := fun k =>
    order.get ⟨k.1, lt_of_lt_of_le k.2 (Nat.succ_le_of_lt hj)⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    have h_inj := List.nodup_iff_injective_get.mp h_nodup hab
    ext
    exact congrArg (fun (x : Fin order.length) => x.val) h_inj
  have h_card : (Finset.univ.image f).card = j + 1 := by
    rw [Finset.card_image_of_injective _ hf_inj]
    simp
  have h_sub : Finset.univ.image f ⊆ {i ∈ S | inst.deadline i ≤ D} := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨k, _, rfl⟩
    dsimp [f]
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [← h_toFinset, List.mem_toFinset]
      exact List.get_mem _ _
    · have hkj : k.1 ≤ j := Nat.le_of_lt_add_one k.2
      have hj_L' : j < L'.length := by
        dsimp [order] at hj
        rwa [List.length_map] at hj
      have hk_L' : k.1 < L'.length := lt_of_le_of_lt hkj hj_L'
      have h_pair : List.Pairwise (· ≤ ·) L' := Finset.pairwise_sort _ _
      have h_le_fin : (⟨k.1, hk_L'⟩ : Fin L'.length) ≤ ⟨j, hj_L'⟩ := hkj
      have h_rel := List.Pairwise.rel_get_of_le h_pair h_le_fin
      have h_fst := pandora_lex_fst_le h_rel
      have h_k_in : L'.get ⟨k.1, hk_L'⟩ ∈ S' := by
        rw [← Finset.mem_sort (· ≤ ·)]
        exact List.get_mem _ _
      have h_j_in : L'.get ⟨j, hj_L'⟩ ∈ S' := by
        rw [← Finset.mem_sort (· ≤ ·)]
        exact List.get_mem _ _
      have hd_k := pandora_deadline_of_mem_emb inst S _ h_k_in
      have hd_j := pandora_deadline_of_mem_emb inst S _ h_j_in
      dsimp [f, D]
      change inst.deadline (order[k.1]'(lt_of_lt_of_le k.2 (Nat.succ_le_of_lt hj))) ≤
             inst.deadline (order[j]'hj)
      have h_get_k : order[k.1]'(lt_of_lt_of_le k.2 (Nat.succ_le_of_lt hj)) =
          (ofLex (L'[k.1]'hk_L')).2 :=
        List.getElem_map (fun (p : Lex (ℕ × Fin inst.n)) => (ofLex p).2)
          (h := lt_of_lt_of_le k.2 (Nat.succ_le_of_lt hj))
      have h_get_j : order[j]'hj = (ofLex (L'[j]'hj_L')).2 :=
        List.getElem_map (fun (p : Lex (ℕ × Fin inst.n)) => (ofLex p).2) (h := hj)
      rw [h_get_k, h_get_j]
      have hd_k' : inst.deadline (ofLex (L'[k.1]'hk_L')).2 = (ofLex (L'[k.1]'hk_L')).1 := hd_k.symm
      have hd_j' : inst.deadline (ofLex (L'[j]'hj_L')).2 = (ofLex (L'[j]'hj_L')).1 := hd_j.symm
      rw [hd_k', hd_j']
      exact h_fst
  have h_le_card := Finset.card_le_card h_sub
  rw [h_card] at h_le_card
  have h_feas := hS D
  exact le_trans h_le_card h_feas
