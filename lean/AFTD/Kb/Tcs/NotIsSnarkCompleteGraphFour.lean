import AFTD.Prelude
import AFTD.Kb.Tcs.IsSnark
import AFTD.Kb.Tcs.IsBridgelessGraph

/-!
# not_is_snark_completeGraph_four

Topic: graphs   Node: d68ea8cbf3aa

Provenance: helper lemma. folklore

The complete graph on four vertices is not a snark.
-/

def not_is_snark_completeGraph_four_c_fun : Fin 4 → Fin 4 → Fin 3
  | 0, 1 => 0
  | 1, 0 => 0
  | 2, 3 => 0
  | 3, 2 => 0
  | 0, 2 => 1
  | 2, 0 => 1
  | 1, 3 => 1
  | 3, 1 => 1
  | 0, 3 => 2
  | 3, 0 => 2
  | 1, 2 => 2
  | 2, 1 => 2
  | _, _ => 0

lemma not_is_snark_completeGraph_four_c_fun_symm (a b : Fin 4) :
    not_is_snark_completeGraph_four_c_fun a b = not_is_snark_completeGraph_four_c_fun b a := by
  revert a b
  decide

def not_is_snark_completeGraph_four_c_sym2 : Sym2 (Fin 4) → Fin 3 :=
  Sym2.lift ⟨not_is_snark_completeGraph_four_c_fun, not_is_snark_completeGraph_four_c_fun_symm⟩

def not_is_snark_completeGraph_four_c_edge (e : (⊤ : SimpleGraph (Fin 4)).edgeSet) : Fin 3 :=
  not_is_snark_completeGraph_four_c_sym2 e.val

lemma not_is_snark_completeGraph_four_c_fun_prop (a b c d v : Fin 4)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hv₁ : v = a ∨ v = b) (hv₂ : v = c ∨ v = d)
    (hne : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    not_is_snark_completeGraph_four_c_fun a b ≠ not_is_snark_completeGraph_four_c_fun c d := by
  revert a b c d v
  decide

lemma not_is_snark_completeGraph_four_c_edge_valid (e₁ e₂ : (⊤ : SimpleGraph (Fin 4)).edgeSet)
    (h : (⊤ : SimpleGraph (Fin 4)).lineGraph.Adj e₁ e₂) :
    not_is_snark_completeGraph_four_c_edge e₁ ≠ not_is_snark_completeGraph_four_c_edge e₂ := by
  obtain ⟨e₁, h₁⟩ := e₁
  obtain ⟨e₂, h₂⟩ := e₂
  rw [SimpleGraph.lineGraph_adj_iff_exists] at h
  rcases h with ⟨hne, v, hv₁, hv₂⟩
  induction e₁ using Sym2.inductionOn with | hf a b =>
  induction e₂ using Sym2.inductionOn with | hf c d =>
  dsimp [not_is_snark_completeGraph_four_c_edge, not_is_snark_completeGraph_four_c_sym2]
  simp only [Sym2.mem_iff] at hv₁ hv₂
  have hab : a ≠ b := by simpa using h₁
  have hcd : c ≠ d := by simpa using h₂
  have hne' : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
    intro hor
    apply hne
    apply Subtype.ext
    rw [Sym2.eq_iff]
    exact hor
  exact not_is_snark_completeGraph_four_c_fun_prop a b c d v hab hcd hv₁ hv₂ hne'

def not_is_snark_completeGraph_four_c_coloring : (⊤ : SimpleGraph (Fin 4)).lineGraph.Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk not_is_snark_completeGraph_four_c_edge
    (by intro e₁ e₂ h; exact not_is_snark_completeGraph_four_c_edge_valid e₁ e₂ h)

lemma not_is_snark_completeGraph_four_lineGraph_colorable : (⊤ : SimpleGraph (Fin 4)).lineGraph.Colorable 3 :=
  ⟨not_is_snark_completeGraph_four_c_coloring⟩

/-- The complete graph K_4 on four vertices is not a snark. -/
theorem not_is_snark_completeGraph_four : ¬ is_snark (⊤ : SimpleGraph (Fin 4)) := by
  intro hsnark
  exact hsnark.2.2 not_is_snark_completeGraph_four_lineGraph_colorable
