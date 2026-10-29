import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.CompleteGraphOddLineGraphChromaticNumberEq
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# complete_graph_odd_rainbow_matching_third_bound

Topic: graphs   Node: 05370baf7bfe

Provenance: helper lemma. OP-306 / IN-338 general construction helpers related to arXiv:2610.22142, Sections3.3.2 and6. Binary leaf-translation classification and standard maximal rainbow-matching counting, used to repair the diagnosed sampling law (experiments8414 and8442). No new exact wild-number case, numerical bound or research advance is claimed.

Every proper edge coloring of an odd complete graph of order n>=3 has a matching with pairwise distinct colors and at least ceil(n/3) edges.
-/

open Finset
open scoped Classical BigOperators
set_option maxHeartbeats 4000000

private theorem in338_odd_subset_colors {n k : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k))
    (U : Finset (Fin n)) (C : Finset (Fin k)) (hU : 3 ≤ U.card)
    (hodd : U.card % 2 = 1)
    (hcol : ∀ u ∈ U, ∀ v ∈ U, ∀ h : u ≠ v,
      c ⟨s(u,v),wild_kn_mem h⟩ ∈ C) : U.card ≤ C.card := by
  classical
  let E : Fin U.card ≃ ↥U := Fintype.equivOfCardEq (by simp)
  let f : Fin U.card ↪ Fin n :=
    ⟨fun v => (E v).val, fun a b h => E.injective (Subtype.ext h)⟩
  let cc := c.comap (SimpleGraph.Embedding.completeGraph f).toCopy.toLineGraphEmbedding.toHom
  have hcc : ∀ e : (⊤ : SimpleGraph (Fin U.card)).edgeSet, cc e ∈ C := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with | hf a b =>
      have hab : a ≠ b := by simpa using he
      change c ⟨s(f a,f b),_⟩ ∈ C
      exact hcol (f a) (E a).property (f b) (E b).property (fun h => hab (f.injective h))
  let cs : (⊤ : SimpleGraph (Fin U.card)).lineGraph.Coloring ↥C :=
    SimpleGraph.Coloring.mk (fun e => ⟨cc e, hcc e⟩) (by
      intro a b hab heq
      exact (cc.valid hab) (congrArg Subtype.val heq))
  have hcfin : (⊤ : SimpleGraph (Fin U.card)).lineGraph.Colorable C.card := by
    let cf := (SimpleGraph.recolorOfEquiv _ (Fintype.equivFin ↥C)) cs
    have : (⊤ : SimpleGraph (Fin U.card)).lineGraph.Colorable (Fintype.card ↥C) := ⟨cf⟩
    simpa only [Fintype.card_coe] using this
  have hh := hcfin.chromaticNumber_le
  rw [complete_graph_odd_line_graph_chromatic_number_eq U.card hU hodd] at hh
  exact_mod_cast hh

theorem complete_graph_odd_rainbow_matching_third_bound {n k : ℕ}
    (hn : 3 ≤ n) (hodd : n % 2 = 1)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) :
    ∃ W : Finset (⊤ : SimpleGraph (Fin n)).edgeSet,
      (∀ a ∈ W, ∀ b ∈ W, a ≠ b →
        Disjoint a.val.toFinset b.val.toFinset) ∧
      Set.InjOn (fun e => c e) (↑W : Set (⊤ : SimpleGraph (Fin n)).edgeSet) ∧
      n ≤ 3 * W.card := by
  classical
  let E := (⊤ : SimpleGraph (Fin n)).edgeSet
  let P : Finset E → Prop := fun W =>
    (∀ a ∈ W, ∀ b ∈ W, a ≠ b → Disjoint a.val.toFinset b.val.toFinset) ∧
      Set.InjOn (fun e => c e) (↑W : Set E)
  let Q : Finset (Finset E) := univ.filter P
  have hQ : Q.Nonempty := ⟨∅, by simp [Q, P, Set.InjOn]⟩
  obtain ⟨W, hWQ, hmax⟩ := Q.exists_max_image card hQ
  have hW : P W := (mem_filter.mp hWQ).2
  let V : Finset (Fin n) := W.biUnion fun e => e.val.toFinset
  let U : Finset (Fin n) := univ \ V
  let C : Finset (Fin k) := W.image fun e => c e
  have hV : V.card = 2 * W.card := by
    dsimp only [V]
    rw [card_biUnion (by intro a ha b hb hab; exact hW.1 a ha b hb hab)]
    have htwo : ∀ e ∈ W, e.val.toFinset.card = 2 := by
      intro e _
      exact Sym2.card_toFinset_of_not_isDiag e.val
        ((⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet e.property)
    rw [sum_congr rfl htwo, sum_const, nsmul_eq_mul]
    simp only [Nat.cast_id, Nat.mul_comm]
  have hC : C.card = W.card := card_image_of_injOn hW.2
  have hUV : U.card + V.card = n := by
    have hh := card_sdiff_add_card_eq_card (subset_univ V)
    simpa only [card_univ, Fintype.card_fin] using hh
  have hcol : ∀ u ∈ U, ∀ v ∈ U, ∀ h : u ≠ v,
      c ⟨s(u,v),wild_kn_mem h⟩ ∈ C := by
    intro u hu v hv huv
    by_contra hno
    let e : E := ⟨s(u,v),wild_kn_mem huv⟩
    have huV : u ∉ V := (mem_sdiff.mp hu).2
    have hvV : v ∉ V := (mem_sdiff.mp hv).2
    have heW : e ∉ W := by
      intro he
      exact huV (mem_biUnion.mpr ⟨e, he, by simp [e]⟩)
    have hedis : ∀ b ∈ W, Disjoint e.val.toFinset b.val.toFinset := by
      intro b hb
      apply disjoint_left.mpr
      intro a ha hab
      have haV : a ∈ V := mem_biUnion.mpr ⟨b,hb,hab⟩
      have hauv : a = u ∨ a = v := by simpa [e] using ha
      rcases hauv with rfl | rfl
      · exact huV haV
      · exact hvV haV
    have hnew : P (insert e W) := by
      constructor
      · intro a ha b hb hab
        rcases mem_insert.mp ha with rfl | ha <;> rcases mem_insert.mp hb with rfl | hb
        · exact (hab rfl).elim
        · exact hedis b hb
        · exact (hedis a ha).symm
        · exact hW.1 a ha b hb hab
      · intro a ha b hb hcolor
        rcases mem_insert.mp ha with rfl | ha <;> rcases mem_insert.mp hb with rfl | hb
        · rfl
        · exact (hno (mem_image.mpr ⟨b,hb,hcolor.symm⟩)).elim
        · exact (hno (mem_image.mpr ⟨a,ha,hcolor⟩)).elim
        · exact hW.2 ha hb hcolor
    have hle := hmax (insert e W) (mem_filter.mpr ⟨mem_univ _,hnew⟩)
    rw [card_insert_of_notMem heW] at hle
    omega
  have hUodd : U.card % 2 = 1 := by omega
  have hsmall : U.card ≤ W.card := by
    by_cases hU : 3 ≤ U.card
    · have hh := in338_odd_subset_colors c U C hU hUodd hcol
      omega
    · omega
  refine ⟨W, hW.1, hW.2, ?_⟩
  omega
