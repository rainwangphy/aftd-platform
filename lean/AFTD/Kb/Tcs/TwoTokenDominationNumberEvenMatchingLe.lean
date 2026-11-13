import AFTD.Prelude
import AFTD.Kb.Tcs.TokenGraph
import AFTD.Kb.Tcs.SimpleGraphIsDominating
import AFTD.Kb.Tcs.SimpleGraphDominationNumber

/-!
# two_token_domination_number_even_matching_le

Topic: graphs   Node: 13f2b858276b

Provenance: formalization of a published result. Source: arXiv:2611.15124, Theorem 1.3

Let G be a finite simple graph on vertex type V whose complement graph Gᶜ is 1-regular. Then the domination number of the 2-token graph F_2(G) is at most Fintype.card V / 2.
-/

open scoped Classical in
/-- If the complement of G is 1-regular (a 1-factor), then the domination number of F_2(G) is at most n / 2. -/
theorem two_token_domination_number_even_matching_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hreg : Gᶜ.IsRegularOfDegree 1) :
    simple_graph_domination_number (token_graph G 2) ≤ Fintype.card V / 2 := by
  classical
  -- The complement is 1-regular, so every vertex has a unique complement-neighbour.
  have hex : ∀ v : V, ∃! w, Gᶜ.Adj v w := by
    intro v
    have hdeg : (Gᶜ).degree v = 1 := hreg v
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hdeg
    refine ⟨w, ?_, ?_⟩
    · have : w ∈ Gᶜ.neighborFinset v := by rw [hw]; simp
      exact (SimpleGraph.mem_neighborFinset _ _ _).mp this
    · intro y hy
      have : y ∈ Gᶜ.neighborFinset v := (SimpleGraph.mem_neighborFinset _ _ _).mpr hy
      rw [hw] at this
      simpa using this
  let p : V → V := fun v => Classical.choose (hex v)
  have hp_adj : ∀ v, Gᶜ.Adj v (p v) := fun v => (Classical.choose_spec (hex v)).1
  have hp_uniq : ∀ v w, Gᶜ.Adj v w → w = p v := fun v w h => (Classical.choose_spec (hex v)).2 w h
  have hp_ne : ∀ v, p v ≠ v := by
    intro v h
    exact (Gᶜ).ne_of_adj (hp_adj v) h.symm
  have hp_invol : ∀ v, p (p v) = v := by
    intro v
    exact (hp_uniq (p v) v (hp_adj v).symm).symm
  -- The pairing as a map on 2-element subsets.
  let f : V → {s : Finset V // s.card = 2} := fun v => ⟨{v, p v}, Finset.card_pair (hp_ne v).symm⟩
  have hfib : ∀ v, (Finset.univ.filter (fun u => f u = f v)) = ({v, p v} : Finset V) := by
    intro v
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have hmem : u ∈ (f u).val := by simp [f]
      rw [h] at hmem
      simpa [f] using hmem
    · rintro (rfl | rfl)
      · rfl
      · apply Subtype.ext
        change ({p v, p (p v)} : Finset V) = {v, p v}
        rw [hp_invol, Finset.pair_comm]
  let D : Finset {s : Finset V // s.card = 2} := Finset.univ.image f
  -- `D` has exactly half as many elements as `V`.
  have hcard : D.card = Fintype.card V / 2 := by
    have hmaps : Set.MapsTo f (↑(Finset.univ : Finset V)) (↑D) := by
      intro x hx
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    have hsum := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.card_univ] at hsum
    have hfiber2 : ∀ b ∈ D, (Finset.univ.filter (fun a => f a = b)).card = 2 := by
      intro b hb
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      rw [hfib v, Finset.card_pair (hp_ne v).symm]
    have h1 : Fintype.card V = D.card * 2 := by
      rw [hsum, Finset.sum_congr rfl hfiber2]
      simp [Finset.sum_const]
    rw [h1, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
  -- Symmetric-difference computation used for the domination step.
  have hpair : ∀ a b : V, a ≠ b → b ≠ p a →
      symmDiff ({a, p a} : Finset V) {a, b} = {b, p a} := by
    intro a b hab hbpa
    have hapa : a ≠ p a := fun h => (hp_ne a) h.symm
    ext c
    rw [Finset.mem_symmDiff]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hca : c = a
    · rw [hca]; simp [hapa, hapa.symm, hab, hab.symm, hbpa, hbpa.symm]
    · by_cases hcp : c = p a
      · rw [hcp]; simp [hapa, hapa.symm, hab, hab.symm, hbpa, hbpa.symm]
      · by_cases hcb : c = b
        · rw [hcb]; simp [hapa, hapa.symm, hab, hab.symm, hbpa, hbpa.symm]
        · simp [hca, hcp, hcb]
  -- `D` is a dominating set of the 2-token graph.
  have hdom : simple_graph_is_dominating (token_graph G 2) (D : Set {s : Finset V // s.card = 2}) := by
    intro s
    obtain ⟨S, hS⟩ := s
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
    by_cases h : Gᶜ.Adj a b
    · left
      have hpa : p a = b := (hp_uniq a b h).symm
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      apply Subtype.ext
      change ({a, p a} : Finset V) = {a, b}
      rw [hpa]
    · right
      have hbpa : b ≠ p a := by
        intro hb
        exact h (by rw [hb]; exact hp_adj a)
      have hgadj : G.Adj b (p a) := by
        by_contra hg
        have hc : Gᶜ.Adj b (p a) := ⟨hbpa, hg⟩
        have hba : b = a := by rw [hp_uniq (p a) b hc.symm, hp_invol]
        exact hab hba.symm
      exact ⟨f a, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩, b, p a, hgadj,
        hpair a b hab hbpa⟩
  unfold simple_graph_domination_number
  rw [← hcard]
  exact Nat.sInf_le ⟨D, hdom, rfl⟩
