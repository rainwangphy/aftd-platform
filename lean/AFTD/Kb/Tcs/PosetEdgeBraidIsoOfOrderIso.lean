import AFTD.Prelude
import AFTD.Kb.Tcs.IsBraidIso
import AFTD.Kb.Tcs.PosetEdgeBraidMap

/-!
# poset_edge_braid_iso_of_order_iso

Topic: combinatorics   Node: 7758e800d620

Provenance: helper lemma. arXiv:2611.15540, after Theorem 3.3

If two partially ordered sets P and Q with decidable equality are order isomorphic, then their associated poset braid solutions poset_edge_braid_map are isomorphic.
-/

def poset_edge_braid_iso_of_order_iso_edge_equiv {P Q : Type*} [PartialOrder P] [PartialOrder Q] (e : P ≃o Q) :
    {p : P × P // p.1 ≤ p.2} ≃ {q : Q × Q // q.1 ≤ q.2} :=
  Equiv.subtypeEquiv (Equiv.prodCongr e.toEquiv e.toEquiv)
    (fun ⟨x, y⟩ => by dsimp; exact (e.le_iff_le : e x ≤ e y ↔ x ≤ y).symm)

def poset_edge_braid_iso_of_order_iso_equiv {P Q : Type*} [PartialOrder P] [PartialOrder Q] (e : P ≃o Q) :
    ({p : P × P // p.1 ≤ p.2} ⊕ (P × ZMod 2)) ≃ ({p : Q × Q // p.1 ≤ p.2} ⊕ (Q × ZMod 2)) :=
  Equiv.sumCongr (poset_edge_braid_iso_of_order_iso_edge_equiv e) (Equiv.prodCongr e.toEquiv (Equiv.refl (ZMod 2)))

/-- An order isomorphism between posets P and Q induces an isomorphism between their bipartite braid solutions. -/
theorem poset_edge_braid_iso_of_order_iso {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    [DecidableEq P] [DecidableEq Q] (e : P ≃o Q) :
    is_braid_iso (@poset_edge_braid_map P _ _) (@poset_edge_braid_map Q _ _) := by
  use poset_edge_braid_iso_of_order_iso_equiv e
  funext ⟨a, b⟩
  rcases a with l | ⟨y, ε⟩ <;> rcases b with l' | ⟨y', ε'⟩
  · rfl
  · simp only [poset_edge_braid_iso_of_order_iso_equiv, Function.comp_apply, Prod.map_apply, poset_edge_braid_map,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Equiv.prodCongr_apply, Equiv.refl_apply,
      OrderIso.coe_toEquiv]
    congr 1
    congr 1
    change Prod.map (⇑e) id
      (if (y', ε') = (l.val.1, 0) then (l.val.2, 1) else if (y', ε') = (l.val.2, 1) then (l.val.1, 0) else (y', ε')) =
      if (e y', ε') = (e l.val.1, 0) then (e l.val.2, 1) else if (e y', ε') = (e l.val.2, 1) then (e l.val.1, 0) else (e y', ε')
    have h1 : (e y', ε') = (e l.val.1, 0) ↔ (y', ε') = (l.val.1, 0) := by
      simp [Prod.ext_iff, e.injective.eq_iff]
    have h2 : (e y', ε') = (e l.val.2, 1) ↔ (y', ε') = (l.val.2, 1) := by
      simp [Prod.ext_iff, e.injective.eq_iff]
    split_ifs with ha hb hc <;> aesop
  · simp only [poset_edge_braid_iso_of_order_iso_equiv, Function.comp_apply, Prod.map_apply, poset_edge_braid_map,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Equiv.prodCongr_apply, Equiv.refl_apply,
      OrderIso.coe_toEquiv]
    congr 1
    congr 1
    change Prod.map (⇑e) id
      (if (y, ε) = (l'.val.1, 0) then (l'.val.2, 1) else if (y, ε) = (l'.val.2, 1) then (l'.val.1, 0) else (y, ε)) =
      if (e y, ε) = (e l'.val.1, 0) then (e l'.val.2, 1) else if (e y, ε) = (e l'.val.2, 1) then (e l'.val.1, 0) else (e y, ε)
    have h1 : (e y, ε) = (e l'.val.1, 0) ↔ (y, ε) = (l'.val.1, 0) := by
      simp [Prod.ext_iff, e.injective.eq_iff]
    have h2 : (e y, ε) = (e l'.val.2, 1) ↔ (y, ε) = (l'.val.2, 1) := by
      simp [Prod.ext_iff, e.injective.eq_iff]
    split_ifs with ha hb hc <;> aesop
  · rfl
