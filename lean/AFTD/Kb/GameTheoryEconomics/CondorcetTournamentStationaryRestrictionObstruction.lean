import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetStationaryTelescopingGeneral
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorMember
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorChallenger
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorNext
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorPotential
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorComplete
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorChk
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorLocal
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorTransLo
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorTransHi

/-!
# condorcet_tournament_stationary_restriction_obstruction

Topic: social_choice   Node: 3d372a6635e1

Provenance: helper lemma. IN-341 OP-19 method diagnostic, experiments8577 and8584. The prior8-candidate stationarity obstruction has mutual root arcs, so does not imply this tournament-consistent version. Exact23-candidate conservation data give C45,K23 and p<=73. Related election convention and general problem: Condorcet winning sets (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf and arXiv:2604.19851v2. No research advance is claimed.

There is a complete outside-challenger selector on all1771 three-element subsets of23 candidates such that every challenger dominates every committee member in the single quadratic-residue tournament modulo23, yet no natural weighting stationary under uniform evict-one/insert-the-challenger transitions has strict half-weight score for every ranking: the canonical candidate ordering already satisfies at least half its weight. Each transition evicts one distinct committee member. This is an obstruction to that additional certificate restriction even under tournament consistency. It asserts no election counterexample and no dimension bound.
-/

private def condorcet_tournament_stationary_restriction_obstruction_S (i : Fin 1771) : Finset (Fin 23) :=
  {condorcet_qr23_selector_member i 0, condorcet_qr23_selector_member i 1, condorcet_qr23_selector_member i 2}

private theorem condorcet_tournament_stationary_restriction_obstruction_mem (i : Fin 1771) (c : Fin 23) : c ∈ condorcet_tournament_stationary_restriction_obstruction_S i ↔ ∃ k, condorcet_qr23_selector_member i k = c := by
  simp only [condorcet_tournament_stationary_restriction_obstruction_S, Finset.mem_insert, Finset.mem_singleton, Fin.exists_fin_succ,
    Fin.exists_fin_zero]
  constructor
  · rintro (h | h | h) <;> simp [h]
  · rintro (h | h | h | h) <;> simp_all [Fin.succ]

private theorem condorcet_tournament_stationary_restriction_obstruction_mem3 (i : Fin 1771) (c : Fin 23) (h : c ∈ condorcet_tournament_stationary_restriction_obstruction_S i) :
    c = condorcet_qr23_selector_member i 0 ∨ c = condorcet_qr23_selector_member i 1 ∨ c = condorcet_qr23_selector_member i 2 := by
  simpa only [condorcet_tournament_stationary_restriction_obstruction_S, Finset.mem_insert, Finset.mem_singleton] using h

private theorem condorcet_tournament_stationary_restriction_obstruction_card (i : Fin 1771) : (condorcet_tournament_stationary_restriction_obstruction_S i).card = 3 := by
  obtain ⟨h01, h12, -⟩ := condorcet_qr23_selector_chk i
  exact Finset.card_eq_three.mpr ⟨_, _, _, h01.ne, (h01.trans h12).ne, h12.ne, rfl⟩

private theorem condorcet_tournament_stationary_restriction_obstruction_fnot (i : Fin 1771) : condorcet_qr23_selector_challenger i ∉ condorcet_tournament_stationary_restriction_obstruction_S i := by
  obtain ⟨-, -, h0, h1, h2, -⟩ := condorcet_qr23_selector_chk i
  intro h
  rcases condorcet_tournament_stationary_restriction_obstruction_mem3 i _ h with h | h | h
  exacts [h0 h, h1 h, h2 h]

private theorem condorcet_tournament_stationary_restriction_obstruction_inj (i : Fin 1771) : Function.Injective (condorcet_qr23_selector_member i) := by
  obtain ⟨h01, h12, -⟩ := condorcet_qr23_selector_chk i
  refine (Fin.strictMono_iff_lt_succ.mpr fun m => ?_).injective
  fin_cases m
  exacts [h01, h12]

private theorem condorcet_tournament_stationary_restriction_obstruction_qr : ∀ i, ∀ c ∈ condorcet_tournament_stationary_restriction_obstruction_S i, (c.val + 23 - (condorcet_qr23_selector_challenger i).val) % 23 ∈
    ({1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18} : Finset ℕ) := by
  intro i c hc
  obtain ⟨-, -, -, -, -, hq⟩ := condorcet_qr23_selector_chk i
  obtain ⟨k, rfl⟩ := (condorcet_tournament_stationary_restriction_obstruction_mem i c).mp hc
  have := hq k
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact this

private theorem condorcet_tournament_stationary_restriction_obstruction_trans (i : Fin 1771) (k : Fin 3) : condorcet_tournament_stationary_restriction_obstruction_S (condorcet_qr23_selector_next i k) =
    insert (condorcet_qr23_selector_challenger i) ((condorcet_tournament_stationary_restriction_obstruction_S i).erase (condorcet_qr23_selector_member i k)) := by
  obtain ⟨hA, hB, hC⟩ := (if h : i.val < 886 then condorcet_qr23_selector_trans_lo i h k else condorcet_qr23_selector_trans_hi i (by omega) k)
  ext c
  rw [Finset.mem_insert, Finset.mem_erase, condorcet_tournament_stationary_restriction_obstruction_mem, condorcet_tournament_stationary_restriction_obstruction_mem]
  constructor
  · rintro ⟨m, rfl⟩
    rcases hA m with h | ⟨hne, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨hne, ?_⟩
      rcases h with h | h | h
      exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  · rintro (rfl | ⟨hne, m, rfl⟩)
    · rcases hB with h | h | h
      exacts [⟨0, h.symm⟩, ⟨1, h.symm⟩, ⟨2, h.symm⟩]
    · have hm : m ≠ k := fun e => hne (e ▸ rfl)
      rcases hC m hm with h | h | h
      exacts [⟨0, h.symm⟩, ⟨1, h.symm⟩, ⟨2, h.symm⟩]

private theorem condorcet_tournament_stationary_restriction_obstruction_local (i : Fin 1771) : 23 + 3 * condorcet_qr23_selector_potential i ≤
    45 * (if ∀ c ∈ condorcet_tournament_stationary_restriction_obstruction_S i, condorcet_qr23_selector_challenger i < c then 1 else 0) + ∑ k : Fin 3, condorcet_qr23_selector_potential (condorcet_qr23_selector_next i k) := by
  have h := condorcet_qr23_selector_local i
  obtain ⟨h01, h12, -⟩ := condorcet_qr23_selector_chk i
  by_cases hc : ∀ c ∈ condorcet_tournament_stationary_restriction_obstruction_S i, condorcet_qr23_selector_challenger i < c
  · have h0 : condorcet_qr23_selector_challenger i < condorcet_qr23_selector_member i 0 := hc _ ((condorcet_tournament_stationary_restriction_obstruction_mem i _).mpr ⟨0, rfl⟩)
    rw [if_pos hc]; rwa [if_pos h0] at h
  · have h0 : ¬ condorcet_qr23_selector_challenger i < condorcet_qr23_selector_member i 0 := fun h0 => hc fun c hc' => by
      rcases condorcet_tournament_stationary_restriction_obstruction_mem3 i c hc' with e | e | e <;> rw [e]
      exacts [h0, h0.trans h01, (h0.trans h01).trans h12]
    rw [if_neg hc]; rwa [if_neg h0] at h

theorem condorcet_tournament_stationary_restriction_obstruction :
    ∃ (S : Fin 1771 → Finset (Fin 23)) (f : Fin 1771 → Fin 23)
      (d : Fin 1771 → Fin 3 → Fin 23) (next : Fin 1771 → Fin 3 → Fin 1771),
      (∀ i, (S i).card=3) ∧
      (∀ T : Finset (Fin 23), T.card=3 → ∃ i,S i=T) ∧
      (∀ i, f i ∉ S i) ∧
      (∀ i, Function.Injective (d i) ∧ ∀ c,c∈S i ↔ ∃ k,d i k=c) ∧
      (∀ i, ∀ c∈S i, (c.val+23-(f i).val)%23 ∈
        ({1,2,3,4,6,8,9,12,13,16,18} : Finset ℕ)) ∧
      (∀ i k,S (next i k)=insert (f i) ((S i).erase (d i k))) ∧
      ∀ w : Fin 1771 → ℕ,
        (∀ j, 3*w j=∑ i,∑ k : Fin 3,if next i k=j then w i else 0) →
        (∑ i,w i) ≤ 2*∑ i,if ∀ c∈S i,f i<c then w i else 0 := by
  refine ⟨condorcet_tournament_stationary_restriction_obstruction_S, condorcet_qr23_selector_challenger, condorcet_qr23_selector_member, condorcet_qr23_selector_next, condorcet_tournament_stationary_restriction_obstruction_card, condorcet_qr23_selector_complete, condorcet_tournament_stationary_restriction_obstruction_fnot,
    fun i => ⟨condorcet_tournament_stationary_restriction_obstruction_inj i, condorcet_tournament_stationary_restriction_obstruction_mem i⟩, condorcet_tournament_stationary_restriction_obstruction_qr, condorcet_tournament_stationary_restriction_obstruction_trans, ?_⟩
  intro w hw
  have h := condorcet_stationary_telescoping_general 1771 45 23 (by norm_num) (by norm_num)
    condorcet_qr23_selector_next condorcet_qr23_selector_potential (fun i => if ∀ c ∈ condorcet_tournament_stationary_restriction_obstruction_S i, condorcet_qr23_selector_challenger i < c then 1 else 0) w
    (fun i => condorcet_tournament_stationary_restriction_obstruction_local i) hw
  have e : (∑ i, (fun i => if ∀ c ∈ condorcet_tournament_stationary_restriction_obstruction_S i, condorcet_qr23_selector_challenger i < c then 1 else 0) i * w i) =
      ∑ i, if ∀ c ∈ condorcet_tournament_stationary_restriction_obstruction_S i, condorcet_qr23_selector_challenger i < c then w i else 0 :=
    Finset.sum_congr rfl fun i _ => by simp only [ite_mul, one_mul, zero_mul]
  rw [e] at h
  exact h
