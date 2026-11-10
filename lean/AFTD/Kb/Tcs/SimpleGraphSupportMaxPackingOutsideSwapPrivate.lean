import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_support_max_packing_outside_swap_private

Topic: graphs   Node: 9d770e0b120f

Provenance: helper lemma. Support-maximal exchange reduction for the general pair-stable triangle-packing residual; no novelty claim.

If P has maximum vertex support among triangle packings of its size, replacing packed triangle abc by abx with x outside P is possible only if c belongs to no other triangle of P.
-/

open scoped Sym2
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem simple_graph_support_max_packing_outside_swap_private (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hsupport : ∀ Q : Finset (Finset (Fin n)), (∀ t ∈ Q, G.IsNClique 3 t) → (Q : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1) → Q.card = P.card → (Q.biUnion id).card ≤ (P.biUnion id).card) (a b c x : Fin n) (hp : ({a,b,c} : Finset (Fin n)) ∈ P) (hx : x ∉ P.biUnion id) (hface : G.IsNClique 3 ({a,b,x} : Finset (Fin n))) : ∀ q ∈ P, q ≠ ({a,b,c} : Finset (Fin n)) → c ∉ q := by
  classical
  let p : Finset (Fin n) := {a,b,c}
  let t : Finset (Fin n) := {a,b,x}
  have hp' : p ∈ P := hp
  have hxP : ∀ q ∈ P, x ∉ q := by
    intro q hq hqx
    apply hx
    exact Finset.mem_biUnion.mpr ⟨q,hq,hqx⟩
  have hxp : x ∉ p := hxP p hp'
  have hab : a ≠ b := by
    intro h
    have hs : p ⊆ ({a,c} : Finset (Fin n)) := by
      intro v hv
      simp only [p, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      aesop
    have hc := Finset.card_le_card hs
    have htwo := Finset.card_le_two (a := a) (b := c)
    have hp3 := (htri p hp').card_eq
    omega
  have htP : t ∉ P := by
    intro ht
    have : x ∈ t := by simp [t]
    exact hxP t ht this
  let R : Finset (Finset (Fin n)) := P.erase p
  let Q : Finset (Finset (Fin n)) := insert t R
  have hQt : t ∈ Q := by simp [Q]
  have hRsub : R ⊆ P := by intro q hq; exact Finset.mem_of_mem_erase hq
  have hface' : G.IsNClique 3 t := hface
  have hQtri : ∀ s ∈ Q, G.IsNClique 3 s := by
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hface'
    · exact htri s (hRsub hs)
  have htpair : ∀ q ∈ R, (t ∩ q).card ≤ 1 := by
    intro q hq
    have hqP : q ∈ P := hRsub hq
    have hne : p ≠ q := (Finset.ne_of_mem_erase hq).symm
    have hpq := hdisj hp' hqP hne
    have hsub : t ∩ q ⊆ p ∩ q := by
      intro v hv
      obtain ⟨hvt,hvq⟩ := Finset.mem_inter.mp hv
      have hvp : v ∈ p := by
        simp only [t, Finset.mem_insert, Finset.mem_singleton] at hvt
        simp only [p, Finset.mem_insert, Finset.mem_singleton]
        rcases hvt with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact False.elim (hxP q hqP hvq)
      exact Finset.mem_inter.mpr ⟨hvp,hvq⟩
    have hc := Finset.card_le_card hsub
    omega
  have hRpair : (R : Set (Finset (Fin n))).Pairwise (fun s u => (s ∩ u).card ≤ 1) := by
    intro s hs u hu hne
    exact hdisj (hRsub hs) (hRsub hu) hne
  have hQpair : (Q : Set (Finset (Fin n))).Pairwise (fun s u => (s ∩ u).card ≤ 1) := by
    change ((insert t R : Finset (Finset (Fin n))) : Set (Finset (Fin n))).Pairwise _
    rw [Finset.coe_insert]
    refine hRpair.insert ?_
    intro q hq _
    have hh := htpair q hq
    exact ⟨hh, by rw [Finset.inter_comm]; exact hh⟩
  have hQcard : Q.card = P.card := by
    have htR : t ∉ R := fun h => htP (hRsub h)
    rw [show Q = insert t R by rfl, Finset.card_insert_of_notMem htR]
    rw [show R = P.erase p by rfl, Finset.card_erase_of_mem hp']
    have hpos : 0 < P.card := Finset.card_pos.mpr ⟨p,hp'⟩
    omega
  intro q hq hqp hcq
  have hqR : q ∈ R := Finset.mem_erase.mpr ⟨hqp,hq⟩
  have hqQ : q ∈ Q := Finset.mem_insert_of_mem hqR
  have hsub : P.biUnion id ⊆ Q.biUnion id := by
    intro v hv
    obtain ⟨r,hr,hvr⟩ := Finset.mem_biUnion.mp hv
    by_cases hrp : r = p
    · subst r
      change v ∈ ({a,b,c} : Finset (Fin n)) at hvr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvr
      rcases hvr with rfl | rfl | rfl
      · exact Finset.mem_biUnion.mpr ⟨t,hQt,by simp [t]⟩
      · exact Finset.mem_biUnion.mpr ⟨t,hQt,by simp [t]⟩
      · exact Finset.mem_biUnion.mpr ⟨q,hqQ,hcq⟩
    · have hrR : r ∈ R := Finset.mem_erase.mpr ⟨hrp,hr⟩
      have hrQ : r ∈ Q := Finset.mem_insert_of_mem hrR
      exact Finset.mem_biUnion.mpr ⟨r,hrQ,hvr⟩
  have hxQ : x ∈ Q.biUnion id := Finset.mem_biUnion.mpr ⟨t,hQt,by simp [t]⟩
  have hstrict : P.biUnion id ⊂ Q.biUnion id := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro heq
    apply hx
    rw [heq]
    exact hxQ
  have hlt := Finset.card_lt_card hstrict
  have hle := hsupport Q hQtri hQpair hQcard
  omega
