import AFTD.Prelude

/-!
# digraph_minimum_outneighbor_count_counterexample

Topic: graphs   Node: 545fb83bd0c0

Provenance: helper lemma. OP-337 campaign, experiments 13848, 13849, and 13854; counterexample to the minimum-quasi-kernel counting shortcut.

The explicit source-free oriented graph on twelve vertices has maximum outdegree at most four, and its unique minimum quasi-kernel is {0,1,2,3}, of size four, with only three out-neighbors.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 50000000

def in525_min_count_witness (v : Fin 12) : Finset (Fin 12) :=
  if v = 0 then {6} else
  if v = 3 then {4,5} else
  if v = 4 then {6,11} else
  if v = 5 then {6,7} else
  if v = 6 then {3,8,9,10} else
  if v = 7 then {3,6} else
  if v = 8 then {1,3} else
  if v = 9 then {2,3} else
  if v = 10 then {0} else
  if v = 11 then {6} else ∅

def in525_min_count_qk (Q : Finset (Fin 12)) : Prop :=
  (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → v ∉ in525_min_count_witness u) ∧
  (∀ v, ∃ u ∈ Q, u = v ∨ v ∈ in525_min_count_witness u ∨
    ∃ w, w ∈ in525_min_count_witness u ∧ v ∈ in525_min_count_witness w)

def in525_min_count_out (Q : Finset (Fin 12)) : Finset (Fin 12) :=
  Finset.univ.filter fun v => ∃ u ∈ Q, v ∈ in525_min_count_witness u

def in525_reach2 (u v : Fin 12) : Prop :=
  u = v ∨ v ∈ in525_min_count_witness u ∨
    ∃ w, w ∈ in525_min_count_witness u ∧ v ∈ in525_min_count_witness w

instance (Q : Finset (Fin 12)) : Decidable (in525_min_count_qk Q) := by
  unfold in525_min_count_qk
  infer_instance

instance (u v : Fin 12) : Decidable (in525_reach2 u v) := by
  unfold in525_reach2
  infer_instance

theorem in525_minimum_unique_structural (Q : Finset (Fin 12))
    (hq : in525_min_count_qk Q) :
    4 ≤ Q.card ∧ (Q.card = 4 → Q = {0,1,2,3}) := by
  obtain ⟨hind,hcov⟩ := hq
  have h6 : (6 : Fin 12) ∉ Q := by
    intro h6q
    have hsub : Q ⊆ ({1,2,6} : Finset (Fin 12)) := by
      intro u hu
      by_contra hnot
      have hnear : ∀ u : Fin 12, u ∉ ({1,2,6} : Finset (Fin 12)) →
          6 ∈ in525_min_count_witness u ∨ u ∈ in525_min_count_witness 6 := by decide
      have hu6 : u ≠ 6 := by
        intro heq
        subst u
        exact hnot (by decide)
      rcases hnear u hnot with ha | ha
      · exact hind u hu 6 h6q hu6 ha
      · exact hind 6 h6q u hu (Ne.symm hu6) ha
    obtain ⟨u,hu,hr⟩ := hcov 11
    have hm := hsub hu
    have hnot : ∀ u : Fin 12, u ∈ ({1,2,6} : Finset (Fin 12)) → ¬ in525_reach2 u 11 := by decide
    exact hnot u hm hr
  have allowed0 : ∀u : Fin 12, in525_reach2 u 0 → u = 0 ∨ u = 10 ∨ u = 6 := by decide
  have allowed1 : ∀u : Fin 12, in525_reach2 u 1 → u = 1 ∨ u = 8 ∨ u = 6 := by decide
  have allowed2 : ∀u : Fin 12, in525_reach2 u 2 → u = 2 ∨ u = 9 ∨ u = 6 := by decide
  have allowed11 : ∀u : Fin 12, in525_reach2 u 11 → u = 11 ∨ u = 4 ∨ u = 3 := by decide
  obtain ⟨u0,hu0,hr0⟩ := hcov 0
  obtain ⟨u1,hu1,hr1⟩ := hcov 1
  obtain ⟨u2,hu2,hr2⟩ := hcov 2
  obtain ⟨u11,hu11,hr11⟩ := hcov 11
  have ha : u0 = 0 ∨ u0 = 10 := by
    rcases allowed0 u0 hr0 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · subst u0; exact (h6 hu0).elim
  have hb : u1 = 1 ∨ u1 = 8 := by
    rcases allowed1 u1 hr1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · subst u1; exact (h6 hu1).elim
  have hc : u2 = 2 ∨ u2 = 9 := by
    rcases allowed2 u2 hr2 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · subst u2; exact (h6 hu2).elim
  have hd : u11 = 11 ∨ u11 = 4 ∨ u11 = 3 := allowed11 u11 hr11
  have hab : u0 ≠ u1 := by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  have hac : u0 ≠ u2 := by rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;> decide
  have had : u0 ≠ u11 := by rcases ha with rfl | rfl <;> rcases hd with rfl | rfl | rfl <;> decide
  have hbc : u1 ≠ u2 := by rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> decide
  have hbd : u1 ≠ u11 := by rcases hb with rfl | rfl <;> rcases hd with rfl | rfl | rfl <;> decide
  have hcd : u2 ≠ u11 := by rcases hc with rfl | rfl <;> rcases hd with rfl | rfl | rfl <;> decide
  let S : Finset (Fin 12) := {u0,u1,u2,u11}
  have hcard : S.card = 4 := by simp [S,hab,hac,had,hbc,hbd,hcd]
  have hSQ : S ⊆ Q := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hle : 4 ≤ Q.card := by simpa [hcard] using Finset.card_le_card hSQ
  refine ⟨hle, ?_⟩
  intro hsize
  have heq : Q = S := (Finset.eq_of_subset_of_card_le hSQ (by simpa [hcard] using hsize.le)).symm
  have hqS : in525_min_count_qk S := by
    rw [← heq]
    exact ⟨hind,hcov⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl | rfl
  all_goals first | exact heq | exact False.elim ((by decide : ¬ in525_min_count_qk S) hqS)

theorem digraph_minimum_outneighbor_count_counterexample :
    (∀ v, v ∉ in525_min_count_witness v) ∧
    (∀ v, ∃ u, v ∈ in525_min_count_witness u) ∧
    (∀ u v, v ∈ in525_min_count_witness u → u ∉ in525_min_count_witness v) ∧
    (∀ v, (in525_min_count_witness v).card ≤ 4) ∧
    let Q : Finset (Fin 12) := {0,1,2,3}
    in525_min_count_qk Q ∧ Q.card = 4 ∧ (in525_min_count_out Q).card = 3 ∧
      (∀ P : Finset (Fin 12), in525_min_count_qk P →
        4 ≤ P.card ∧ (P.card = 4 → P = Q)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v; fin_cases v <;> decide
  · intro v; fin_cases v <;> decide
  · intro u v; fin_cases u <;> fin_cases v <;> decide
  · intro v; fin_cases v <;> decide
  · dsimp only
    refine ⟨by decide, by decide, by decide, ?_⟩
    exact in525_minimum_unique_structural
