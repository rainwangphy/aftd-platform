import AFTD.Prelude
import AFTD.Kb.Tcs.NestedMatching
import AFTD.Kb.Tcs.MonotonePath
import AFTD.Kb.Tcs.CyclicRamseyNumber
import AFTD.Kb.Tcs.CyclicRamseyProperty
import AFTD.Kb.Tcs.CyclicHasCopy

/-!
# op_1258_cyclic_ramsey_k_one

Topic: graphs   Node: 7d9ba9ee0e56

Provenance: formalization of a published result. Source: arXiv:2611.08375, Sec. 3.4

For every integer l ≥ 3, the cyclic Ramsey number R_cyc(NM_2, MP_l) of the 1-edge nested matching and the monotone path MP_l equals l.
-/

open SimpleGraph

/-- A cyclic copy of a graph on `m` vertices into a graph on `N` vertices forces `m ≤ N`. -/
private lemma op_1258_cyclic_ramsey_k_one_vertex_bound {m N : ℕ} {H : SimpleGraph (Fin m)}
    {G : SimpleGraph (Fin N)} (h : cyclic_has_copy H G) : m ≤ N := by
  obtain ⟨f, hf, _⟩ := h
  simpa using Fintype.card_le_of_injective f hf

/-- The empty graph contains no cyclic copy of the one-edge nested matching. -/
private lemma op_1258_cyclic_ramsey_k_one_not_copy_bot {N : ℕ} :
    ¬ cyclic_has_copy (nested_matching 1) (⊥ : SimpleGraph (Fin N)) := by
  rintro ⟨f, _, hadj, _⟩
  have h01 : (nested_matching 1).Adj (0 : Fin 2) 1 := by
    simp [nested_matching, SimpleGraph.fromRel]
  have h := hadj h01
  simp [SimpleGraph.bot_adj] at h

/-- Any graph with an edge contains a cyclic copy of the one-edge nested matching. -/
private lemma op_1258_cyclic_ramsey_k_one_edge_copy (l : ℕ) (G : SimpleGraph (Fin l))
    (u v : Fin l) (huv : G.Adj u v) : cyclic_has_copy (nested_matching 1) G := by
  have huvne : u ≠ v := huv.ne
  have hvu : G.Adj v u := huv.symm
  refine ⟨![u, v], ?_, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [nested_matching, SimpleGraph.fromRel]
  · intro a b c hab
    rw [sbtw_iff] at hab
    omega

/-- The complete graph on `N ≥ l` vertices contains a cyclic copy of the monotone path `MP_l`. -/
private lemma op_1258_cyclic_ramsey_k_one_monotone_top {l N : ℕ} (h : l ≤ N) :
    cyclic_has_copy (monotone_path l) (⊤ : SimpleGraph (Fin N)) := by
  refine ⟨Fin.castLE h, Fin.castLE_injective h, ?_, ?_⟩
  · intro u v huv
    simp only [SimpleGraph.top_adj]
    exact fun heq => huv.ne (Fin.castLE_injective h heq)
  · intro u v w hb
    simpa only [sbtw_iff, Fin.lt_def, Fin.val_castLE] using hb

/-- The cyclic Ramsey property holds at `N = l`: every edge-colouring of `K_l` has a red
single edge or a blue cyclic monotone path `MP_l`. -/
private lemma op_1258_cyclic_ramsey_k_one_property (l : ℕ) :
    cyclic_ramsey_property (nested_matching 1) (monotone_path l) l := by
  intro G
  by_cases h : ∃ u v, G.Adj u v
  · left
    obtain ⟨u, v, huv⟩ := h
    exact op_1258_cyclic_ramsey_k_one_edge_copy l G u v huv
  · right
    have hbot : G = ⊥ := by
      ext u v
      simp only [SimpleGraph.bot_adj]
      constructor
      · intro huv; exact absurd ⟨u, v, huv⟩ h
      · intro hf; exact hf.elim
    rw [hbot]
    simpa using op_1258_cyclic_ramsey_k_one_monotone_top (l := l) (N := l) le_rfl

/-- For every `N < l` the cyclic Ramsey property fails, witnessed by the empty graph. -/
private lemma op_1258_cyclic_ramsey_k_one_not_property {l N : ℕ} (hN : N < l) :
    ¬ cyclic_ramsey_property (nested_matching 1) (monotone_path l) N := by
  intro hp
  have h' := hp (⊥ : SimpleGraph (Fin N))
  rcases h' with h1 | h2
  · exact op_1258_cyclic_ramsey_k_one_not_copy_bot h1
  · have hbot : (⊥ : SimpleGraph (Fin N))ᶜ = ⊤ := by simp
    rw [hbot] at h2
    have hle := op_1258_cyclic_ramsey_k_one_vertex_bound h2
    omega

/-- The k = 1 case of Conjecture 4.32: R_cyc(NM_2, MP_l) = l. -/
theorem op_1258_cyclic_ramsey_k_one (l : ℕ) (hl : 3 ≤ l) :
    cyclic_ramsey_number (nested_matching 1) (monotone_path l) = l := by
  unfold cyclic_ramsey_number
  have hmem : l ∈ {N : ℕ | 0 < N ∧ cyclic_ramsey_property (nested_matching 1) (monotone_path l) N} :=
    ⟨by omega, op_1258_cyclic_ramsey_k_one_property l⟩
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hinf : sInf {N : ℕ | 0 < N ∧ cyclic_ramsey_property (nested_matching 1) (monotone_path l) N} ∈
      {N : ℕ | 0 < N ∧ cyclic_ramsey_property (nested_matching 1) (monotone_path l) N} :=
    Nat.sInf_mem ⟨l, hmem⟩
  exact op_1258_cyclic_ramsey_k_one_not_property hcon hinf.2
