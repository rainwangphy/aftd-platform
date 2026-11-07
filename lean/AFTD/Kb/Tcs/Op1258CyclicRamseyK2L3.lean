import AFTD.Prelude
import AFTD.Kb.Tcs.NestedMatching
import AFTD.Kb.Tcs.MonotonePath
import AFTD.Kb.Tcs.CyclicRamseyNumber
import AFTD.Kb.Tcs.CyclicHasCopy
import AFTD.Kb.Tcs.CyclicRamseyProperty
import AFTD.Kb.GameTheoryEconomics.Strict

/-!
# op_1258_cyclic_ramsey_k2_l3

Topic: graphs   Node: 0fb5d1f8d47f

Provenance: formalization of a published result. Source: arXiv:2611.08375, Table 1

The cyclic Ramsey number R_cyc(NM_4, MP_3) of the 2-edge nested matching NM_4 and the monotone path MP_3 is equal to 4.
-/

/-- Decidability of strict betweenness on `Fin n`, through the linear-order instance. -/
instance op_1258_cyclic_ramsey_k2_l3_instDecidableSBtwFin {n : ℕ} (a b c : Fin n) : Decidable (sbtw a b c) :=
  decidable_of_iff (a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b) Iff.rfl

/-- Rotation of the cyclic order on `Fin 4` by `j`. -/
def op_1258_cyclic_ramsey_k2_l3_rot4 (j u : Fin 4) : Fin 4 := ⟨(j.val + u.val) % 4, by omega⟩

/-- Rotation of `Fin 3` into the cyclic order on `Fin 4` by `j`. -/
def op_1258_cyclic_ramsey_k2_l3_rot34 (j : Fin 4) (u : Fin 3) : Fin 4 :=
  ⟨(j.val + u.val) % 4, by omega⟩

lemma op_1258_cyclic_ramsey_k2_l3_rot4_inj :
    ∀ j : Fin 4, Function.Injective (op_1258_cyclic_ramsey_k2_l3_rot4 j) := by decide

lemma op_1258_cyclic_ramsey_k2_l3_rot4_sbtw : ∀ (j u v w : Fin 4), sbtw u v w →
    sbtw (op_1258_cyclic_ramsey_k2_l3_rot4 j u) (op_1258_cyclic_ramsey_k2_l3_rot4 j v)
      (op_1258_cyclic_ramsey_k2_l3_rot4 j w) := by decide

lemma op_1258_cyclic_ramsey_k2_l3_rot34_inj :
    ∀ j : Fin 4, Function.Injective (op_1258_cyclic_ramsey_k2_l3_rot34 j) := by decide

lemma op_1258_cyclic_ramsey_k2_l3_rot34_sbtw : ∀ (j : Fin 4) (u v w : Fin 3), sbtw u v w →
    sbtw (op_1258_cyclic_ramsey_k2_l3_rot34 j u) (op_1258_cyclic_ramsey_k2_l3_rot34 j v)
      (op_1258_cyclic_ramsey_k2_l3_rot34 j w) := by decide

/-- The edges of `NM_4` are `{0,3}` and `{1,2}`. -/
lemma op_1258_cyclic_ramsey_k2_l3_nm4_cases {u v : Fin 4} (h : (nested_matching 2).Adj u v) :
    (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) := by
  fin_cases u <;> fin_cases v <;> simp_all [nested_matching, SimpleGraph.fromRel]

/-- The edges of `MP_3` are `{0,1}` and `{1,2}`. -/
lemma op_1258_cyclic_ramsey_k2_l3_mp3_cases {u v : Fin 3} (h : (monotone_path 3).Adj u v) :
    (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) := by
  fin_cases u <;> fin_cases v <;> simp_all [monotone_path, SimpleGraph.fromRel]

/-- Two nested edges `03` and `12` form a cyclic copy of `NM_4`. -/
lemma op_1258_cyclic_ramsey_k2_l3_copy_nm4_rot0 (G : SimpleGraph (Fin 4))
    (h03 : G.Adj 0 3) (h12 : G.Adj 1 2) : cyclic_has_copy (nested_matching 2) G := by
  refine ⟨op_1258_cyclic_ramsey_k2_l3_rot4 0,
    op_1258_cyclic_ramsey_k2_l3_rot4_inj 0, ?_, op_1258_cyclic_ramsey_k2_l3_rot4_sbtw 0⟩
  intro u v huv
  rcases op_1258_cyclic_ramsey_k2_l3_nm4_cases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h03
  · exact (SimpleGraph.adj_comm G 0 3).1 h03
  · exact h12
  · exact (SimpleGraph.adj_comm G 1 2).1 h12

/-- The rotated edges `01` and `23` form a cyclic copy of `NM_4`. -/
lemma op_1258_cyclic_ramsey_k2_l3_copy_nm4_rot1 (G : SimpleGraph (Fin 4))
    (h01 : G.Adj 0 1) (h23 : G.Adj 2 3) : cyclic_has_copy (nested_matching 2) G := by
  refine ⟨op_1258_cyclic_ramsey_k2_l3_rot4 1,
    op_1258_cyclic_ramsey_k2_l3_rot4_inj 1, ?_, op_1258_cyclic_ramsey_k2_l3_rot4_sbtw 1⟩
  intro u v huv
  rcases op_1258_cyclic_ramsey_k2_l3_nm4_cases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (SimpleGraph.adj_comm G 0 1).1 h01
  · exact h01
  · exact h23
  · exact (SimpleGraph.adj_comm G 2 3).1 h23

/-- The cyclic path `0-1-2` in `H` is a copy of `MP_3`. -/
lemma op_1258_cyclic_ramsey_k2_l3_copy_mp3_rot0 (H : SimpleGraph (Fin 4))
    (h01 : H.Adj 0 1) (h12 : H.Adj 1 2) : cyclic_has_copy (monotone_path 3) H := by
  refine ⟨op_1258_cyclic_ramsey_k2_l3_rot34 0,
    op_1258_cyclic_ramsey_k2_l3_rot34_inj 0, ?_, op_1258_cyclic_ramsey_k2_l3_rot34_sbtw 0⟩
  intro u v huv
  rcases op_1258_cyclic_ramsey_k2_l3_mp3_cases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h01
  · exact (SimpleGraph.adj_comm H 0 1).1 h01
  · exact h12
  · exact (SimpleGraph.adj_comm H 1 2).1 h12

/-- The cyclic path `1-2-3` in `H` is a copy of `MP_3`. -/
lemma op_1258_cyclic_ramsey_k2_l3_copy_mp3_rot1 (H : SimpleGraph (Fin 4))
    (h12 : H.Adj 1 2) (h23 : H.Adj 2 3) : cyclic_has_copy (monotone_path 3) H := by
  refine ⟨op_1258_cyclic_ramsey_k2_l3_rot34 1,
    op_1258_cyclic_ramsey_k2_l3_rot34_inj 1, ?_, op_1258_cyclic_ramsey_k2_l3_rot34_sbtw 1⟩
  intro u v huv
  rcases op_1258_cyclic_ramsey_k2_l3_mp3_cases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h12
  · exact (SimpleGraph.adj_comm H 1 2).1 h12
  · exact h23
  · exact (SimpleGraph.adj_comm H 2 3).1 h23

/-- The cyclic path `2-3-0` in `H` is a copy of `MP_3`. -/
lemma op_1258_cyclic_ramsey_k2_l3_copy_mp3_rot2 (H : SimpleGraph (Fin 4))
    (h23 : H.Adj 2 3) (h30 : H.Adj 3 0) : cyclic_has_copy (monotone_path 3) H := by
  refine ⟨op_1258_cyclic_ramsey_k2_l3_rot34 2,
    op_1258_cyclic_ramsey_k2_l3_rot34_inj 2, ?_, op_1258_cyclic_ramsey_k2_l3_rot34_sbtw 2⟩
  intro u v huv
  rcases op_1258_cyclic_ramsey_k2_l3_mp3_cases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h23
  · exact (SimpleGraph.adj_comm H 2 3).1 h23
  · exact h30
  · exact (SimpleGraph.adj_comm H 3 0).1 h30

/-- The cyclic path `3-0-1` in `H` is a copy of `MP_3`. -/
lemma op_1258_cyclic_ramsey_k2_l3_copy_mp3_rot3 (H : SimpleGraph (Fin 4))
    (h30 : H.Adj 3 0) (h01 : H.Adj 0 1) : cyclic_has_copy (monotone_path 3) H := by
  refine ⟨op_1258_cyclic_ramsey_k2_l3_rot34 3,
    op_1258_cyclic_ramsey_k2_l3_rot34_inj 3, ?_, op_1258_cyclic_ramsey_k2_l3_rot34_sbtw 3⟩
  intro u v huv
  rcases op_1258_cyclic_ramsey_k2_l3_mp3_cases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h30
  · exact (SimpleGraph.adj_comm H 3 0).1 h30
  · exact h01
  · exact (SimpleGraph.adj_comm H 0 1).1 h01

/-- Every `2`-colouring of the cyclically ordered `K_4` contains a monochromatic copy of `NM_4`
or of `MP_3`: a propositional case analysis on the four edges of the `4`-cycle. -/
lemma op_1258_cyclic_ramsey_k2_l3_property_four :
    cyclic_ramsey_property (nested_matching 2) (monotone_path 3) 4 := by
  intro G
  have key : (G.Adj 0 1 ∧ G.Adj 2 3) ∨ (G.Adj 3 0 ∧ G.Adj 1 2) ∨
      (¬ G.Adj 0 1 ∧ ¬ G.Adj 1 2) ∨ (¬ G.Adj 1 2 ∧ ¬ G.Adj 2 3) ∨
      (¬ G.Adj 2 3 ∧ ¬ G.Adj 3 0) ∨ (¬ G.Adj 3 0 ∧ ¬ G.Adj 0 1) := by tauto
  have h01 : (¬ G.Adj 0 1) → Gᶜ.Adj (0 : Fin 4) 1 :=
    fun h => (SimpleGraph.compl_adj G 0 1).2 ⟨by decide, h⟩
  have h12 : (¬ G.Adj 1 2) → Gᶜ.Adj (1 : Fin 4) 2 :=
    fun h => (SimpleGraph.compl_adj G 1 2).2 ⟨by decide, h⟩
  have h23 : (¬ G.Adj 2 3) → Gᶜ.Adj (2 : Fin 4) 3 :=
    fun h => (SimpleGraph.compl_adj G 2 3).2 ⟨by decide, h⟩
  have h30 : (¬ G.Adj 3 0) → Gᶜ.Adj (3 : Fin 4) 0 :=
    fun h => (SimpleGraph.compl_adj G 3 0).2 ⟨by decide, h⟩
  rcases key with h | h | h | h | h | h
  · exact Or.inl (op_1258_cyclic_ramsey_k2_l3_copy_nm4_rot1 G h.1 h.2)
  · exact Or.inl (op_1258_cyclic_ramsey_k2_l3_copy_nm4_rot0 G ((SimpleGraph.adj_comm G 0 3).2 h.1) h.2)
  · exact Or.inr (op_1258_cyclic_ramsey_k2_l3_copy_mp3_rot0 Gᶜ (h01 h.1) (h12 h.2))
  · exact Or.inr (op_1258_cyclic_ramsey_k2_l3_copy_mp3_rot1 Gᶜ (h12 h.1) (h23 h.2))
  · exact Or.inr (op_1258_cyclic_ramsey_k2_l3_copy_mp3_rot2 Gᶜ (h23 h.1) (h30 h.2))
  · exact Or.inr (op_1258_cyclic_ramsey_k2_l3_copy_mp3_rot3 Gᶜ (h30 h.1) (h01 h.2))

/-- No `N < 4` has the cyclic Ramsey property: `NM_4` needs `4` vertices, and the complete
colouring has no `MP_3` in the empty complement. -/
lemma op_1258_cyclic_ramsey_k2_l3_not_property_of_lt (N : ℕ) (hN : N < 4) :
    ¬ cyclic_ramsey_property (nested_matching 2) (monotone_path 3) N := by
  intro h
  rcases h ⊤ with h | h
  · rcases h with ⟨f, hf, -, -⟩
    have h4 : 4 ≤ N := by
      have := Fintype.card_le_of_injective f hf
      simpa using this
    omega
  · rcases h with ⟨f, hf, hadj, -⟩
    have h01 : (monotone_path 3).Adj (0 : Fin 3) 1 := by
      simp [monotone_path, SimpleGraph.fromRel]
    have hbad := (SimpleGraph.compl_adj (⊤ : SimpleGraph (Fin N)) (f 0) (f 1)).1 (hadj h01)
    exact hbad.2 ((SimpleGraph.top_adj (f 0) (f 1)).2 (hf.ne (by decide)))

/-- Smallest even-k instance of Conjecture 4.32: R_cyc(NM_4, MP_3) = 4. -/
theorem op_1258_cyclic_ramsey_k2_l3 :
    cyclic_ramsey_number (nested_matching 2) (monotone_path 3) = 4 := by
  have hmem : 4 ∈ {N : ℕ | 0 < N ∧ cyclic_ramsey_property (nested_matching 2) (monotone_path 3) N} :=
    ⟨by norm_num, op_1258_cyclic_ramsey_k2_l3_property_four⟩
  refine le_antisymm (Nat.sInf_le hmem) ?_
  have hinf := Nat.sInf_mem (⟨4, hmem⟩ :
    {N : ℕ | 0 < N ∧ cyclic_ramsey_property (nested_matching 2) (monotone_path 3) N}.Nonempty)
  by_contra hcon
  rw [not_le] at hcon
  exact op_1258_cyclic_ramsey_k2_l3_not_property_of_lt _ hcon hinf.2
