import AFTD.Prelude
import AFTD.Kb.Tcs.InvolutionEqualBlocksInternalCard
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# wild_rainbow_equal_blocks_closed_matching_crosses

Topic: graphs   Node: 07e3c28867bc

Provenance: helper lemma. IN-338 structural/repair helpers for OP-306, the prescribed-coloring conjecture in arXiv:2610.22142 Sections3.3.2 and6. Exact matching-involution balance and the method obstruction computed in experiment8464. These are certificate/method lemmas, not new wild-number bounds or research advances.

In a properly colored complete graph with one specified missing vertex for each color, let two disjoint equally sized blocks have no common internal color except i0. If a different color i closes their union, every color-i partner of a vertex in the first block belongs to the second block.
-/

open Finset
set_option maxHeartbeats 2500000

theorem wild_rainbow_equal_blocks_closed_matching_crosses
    {n k : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k))
    (m : Fin k → Fin n)
    (hm : ∀ i v, (∀ w (h : v ≠ w), c ⟨s(v,w),wild_kn_mem h⟩ ≠ i) ↔ v = m i)
    (A B : Finset (Fin n)) (hdis : Disjoint A B) (hcard : A.card = B.card)
    (i0 i : Fin k) (hne : i ≠ i0)
    (hsep : ∀ a ∈ A, ∀ a' ∈ A, ∀ ha : a ≠ a',
      ∀ b ∈ B, ∀ b' ∈ B, ∀ hb : b ≠ b',
        c ⟨s(a,a'),wild_kn_mem ha⟩ = c ⟨s(b,b'),wild_kn_mem hb⟩ →
          c ⟨s(a,a'),wild_kn_mem ha⟩ = i0)
    (hclosed : w279_closed c i (A ∪ B)) :
    ∀ a ∈ A, w279_pc c i a ∈ B := by
  classical
  let p := w279_pc c i
  have hmiss : m i ∉ A ∪ B := by
    intro hmi
    have hh := w279_card_closed c m hm i (A ∪ B) hclosed
    rw [if_pos hmi, card_union_of_disjoint hdis] at hh
    omega
  have hvne : ∀ v ∈ A ∪ B, v ≠ m i := by
    intro v hv he
    exact hmiss (he ▸ hv)
  have hstable : ∀ v ∈ A ∪ B, p v ∈ A ∪ B := by
    intro v hv
    exact (w279_closed_iff c m hm i (A ∪ B)).mp hclosed v hv (hvne v hv)
  have hinv : ∀ v ∈ A ∪ B, p (p v) = v := by
    intro v hv
    exact w279_pc_pc c m hm i v (hvne v hv)
  have heq := involution_equal_blocks_internal_card p A B hdis hcard hstable hinv
  intro a ha
  by_contra hpB
  have hpA : p a ∈ A := (mem_union.mp (hstable a (mem_union_left B ha))).resolve_right hpB
  have hposA : 0 < (A.filter fun v => p v ∈ A).card := card_pos.mpr ⟨a,mem_filter.mpr ⟨ha,hpA⟩⟩
  have hposB : 0 < (B.filter fun v => p v ∈ B).card := by omega
  obtain ⟨b,hb⟩ := card_pos.mp hposB
  obtain ⟨hbB,hpB'⟩ := mem_filter.mp hb
  obtain ⟨hane,hac⟩ := w279_pc_spec c m hm i a (hvne a (mem_union_left B ha))
  obtain ⟨hbne,hbc⟩ := w279_pc_spec c m hm i b (hvne b (mem_union_right A hbB))
  have hci0 := hsep a ha (p a) hpA hane b hbB (p b) hpB' hbne (hac.trans hbc.symm)
  exact hne (hac.symm.trans hci0)
