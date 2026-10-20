import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeColorClassGraph
import AFTD.Kb.Tcs.IsBalancedFiveColoring
import AFTD.Kb.Tcs.GraphSatisfiesPropertyL
import AFTD.Kb.Tcs.EdgesOrdWithin

/-!
# balanced_five_coloring_color_class_property_l

Topic: combinatorics   Node: c897bf6630f9

Provenance: formalization of a published result. Source: scout/2610-24484-erd-h-o-s-gy-arf-as-balanced-five-colorings.md:1283

For an arbitrary type V, in any balanced edge coloring c : Sym2 V → Fin 5, every color class graph edge_color_class_graph c k satisfies property (L).
-/

/-- Every color class of a balanced 5-coloring satisfies property (L). -/
theorem balanced_five_coloring_color_class_property_l
    {V : Type*} (c : Sym2 V → Fin 5) (hc : is_balanced_five_coloring c) (k : Fin 5) :
    graph_satisfies_property_l (edge_color_class_graph c k) := by
  classical
  intro S hS
  -- Each colour class of `S.offDiag` has at least two elements: balancedness gives one pair,
  -- and both orders of that pair lie in the class.
  have h2 : ∀ j : Fin 5, 2 ≤ (S.offDiag.filter (fun p : V × V => c s(p.1, p.2) = j)).card := by
    intro j
    obtain ⟨v, hv, w, hw, hne, hcol⟩ := hc S hS j
    have hvw : (v, w) ∈ S.offDiag.filter (fun p : V × V => c s(p.1, p.2) = j) := by
      simp only [Finset.mem_filter, Finset.mem_offDiag]
      exact ⟨⟨hv, hw, hne⟩, hcol⟩
    have hwv : (w, v) ∈ S.offDiag.filter (fun p : V × V => c s(p.1, p.2) = j) := by
      simp only [Finset.mem_filter, Finset.mem_offDiag]
      refine ⟨⟨hw, hv, hne.symm⟩, ?_⟩
      rw [Sym2.eq_swap]
      exact hcol
    have hne' : (v, w) ≠ (w, v) := fun h => hne (congrArg Prod.fst h)
    have hpair : ({(v, w), (w, v)} : Finset (V × V)) ⊆
        S.offDiag.filter (fun p : V × V => c s(p.1, p.2) = j) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hvw
      · exact hwv
    have := Finset.card_le_card hpair
    rw [Finset.card_pair hne'] at this
    omega
  -- The five colour classes partition the 30 ordered pairs of `S.offDiag`.
  have hsum : ∑ j : Fin 5, (S.offDiag.filter (fun p : V × V => c s(p.1, p.2) = j)).card = 30 := by
    have h := Finset.card_eq_sum_card_fiberwise (s := S.offDiag)
      (f := fun p : V × V => c s(p.1, p.2)) (t := Finset.univ)
      (fun p _ => Finset.mem_univ _)
    rw [Finset.offDiag_card, hS] at h
    norm_num at h
    exact h.symm
  -- Hence the class of `k` has at most 30 - 4 * 2 = 22 elements.
  have hkey : (S.offDiag.filter (fun p : V × V => c s(p.1, p.2) = k)).card ≤ 22 := by
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun j : Fin 5 => (S.offDiag.filter (fun p : V × V => c s(p.1, p.2) = j)).card)
      (Finset.mem_univ k)
    have hbound : 8 ≤ ∑ j ∈ Finset.univ.erase k,
        (S.offDiag.filter (fun p : V × V => c s(p.1, p.2) = j)).card := by
      have hc4 := Finset.card_nsmul_le_sum (Finset.univ.erase k)
        (fun j : Fin 5 => (S.offDiag.filter (fun p : V × V => c s(p.1, p.2) = j)).card) 2
        (fun j _ => h2 j)
      have hcard : (Finset.univ.erase k).card = 4 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ k)]
        simp
      rw [hcard] at hc4
      simpa using hc4
    rw [hsum] at hsplit
    omega
  -- The filtered set of directed edges of the colour class is exactly this class.
  have hEq : edges_ord_within (edge_color_class_graph c k) S
      = (S.offDiag.filter (fun p : V × V => c s(p.1, p.2) = k)).card := by
    rw [edges_ord_within]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag]
    tauto
  rw [hEq]
  exact hkey
