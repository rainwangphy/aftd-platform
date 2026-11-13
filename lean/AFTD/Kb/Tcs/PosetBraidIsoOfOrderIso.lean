import AFTD.Prelude
import AFTD.Kb.Tcs.IsBraidIso
import AFTD.Kb.Tcs.PosetBraidMap

/-!
# poset_braid_iso_of_order_iso

Topic: combinatorics   Node: 5b9af91fd776

Provenance: helper lemma. scout/2611-15540-solutions-of-the-set-theoretic-quantum-yang-baxter-equation.md:504

If two partially ordered sets P and Q with decidable orders are order isomorphic, then their associated poset braid solutions poset_braid_map are isomorphic.
-/

/-- An order isomorphism between posets induces an isomorphism between their braid solutions. -/
theorem poset_braid_iso_of_order_iso {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    [DecidableRel ((· ≤ ·) : P → P → Prop)] [DecidableRel ((· ≤ ·) : Q → Q → Prop)]
    (e : P ≃o Q) :
    is_braid_iso (@poset_braid_map P _ _) (@poset_braid_map Q _ _) := by
  use Equiv.sumCongr e.toEquiv (Equiv.prodCongr e.toEquiv (Equiv.refl (ZMod 2)))
  funext ⟨a, b⟩
  rcases a with x | ⟨y, ε⟩ <;> rcases b with x' | ⟨y', ε'⟩ <;>
    first
    | rfl
    | simp only [Function.comp_apply, Prod.map_apply, poset_braid_map,
        Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
        Equiv.prodCongr_apply, Equiv.refl_apply,
        OrderIso.coe_toEquiv, OrderIso.le_iff_le]
