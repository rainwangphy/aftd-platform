import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutSingleVertexGluingAbstract
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_single_vertex_sum_strong_equilibrium

Topic: equilibria   Node: 63206ad7eaaf

Provenance: helper lemma. Structural reduction for OP-85, the general strong-equilibrium existence question; supported on five-vertex decompositions by experiment 12429.

If a finite graph is covered by two induced subgraphs meeting in one vertex with no edge between their exclusive parts, and a coloring restricts to a strong equilibrium on each induced subgraph, then the coloring is a strong equilibrium on the entire graph.
-/

open Finset

def maxcut_single_vertex_sum_strong_equilibrium_a_payoff
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {k : ℕ} (p : V → Fin k) (v : V) : ℕ :=
  if hv : v ∈ A then
    maxcut_utility (G.induce (↑A : Set V)) (fun (w : (↑A : Set V)) => p w.1) ⟨v, hv⟩
  else 0

theorem maxcut_single_vertex_sum_strong_equilibrium_card_filter_subtype
    {V : Type} [Fintype V] [DecidableEq V]
    (A : Finset V) (P : V → Prop) [DecidablePred P] :
  (Finset.univ.filter (fun (w : (↑A : Set V)) => P w.1)).card = (A.filter P).card := by
  apply Finset.card_bij (fun (w : (↑A : Set V)) _ => w.1)
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    simp only [mem_filter]
    exact ⟨w.2, hw⟩
  · intro w1 _ w2 _ h
    exact Subtype.ext h
  · intro b hb
    simp only [mem_filter] at hb
    use ⟨b, hb.1⟩
    simp [hb.2]

lemma maxcut_single_vertex_sum_strong_equilibrium_a_payoff_eq
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {k : ℕ} (p : V → Fin k) (v : V) (hv : v ∈ A) :
    maxcut_single_vertex_sum_strong_equilibrium_a_payoff G A p v =
      (A.filter (fun w => G.Adj v w ∧ p w ≠ p v)).card := by
  dsimp [maxcut_single_vertex_sum_strong_equilibrium_a_payoff]
  rw [dif_pos hv]
  exact maxcut_single_vertex_sum_strong_equilibrium_card_filter_subtype A (fun w => G.Adj v w ∧ p w ≠ p v)

lemma maxcut_single_vertex_sum_strong_equilibrium_utility_eq_sum_payoffs
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (o : V) (k : ℕ) (p : V → Fin k)
    (hcover : A ∪ B = Finset.univ) (hinter : A ∩ B = {o})
    (hsep : ∀ v ∈ A, v ∉ B → ∀ w ∈ B, w ∉ A → ¬ G.Adj v w) (v : V) :
    maxcut_utility G p v =
      maxcut_single_vertex_sum_strong_equilibrium_a_payoff G A p v +
      maxcut_single_vertex_sum_strong_equilibrium_a_payoff G B p v := by
  let P := fun w => G.Adj v w ∧ p w ≠ p v
  have hP_univ : maxcut_utility G p v = (Finset.univ.filter P).card := rfl
  by_cases hvA : v ∈ A
  · by_cases hvB : v ∈ B
    · have hvo : v = o := by
        have : v ∈ A ∩ B := mem_inter.mpr ⟨hvA, hvB⟩
        rw [hinter] at this
        exact mem_singleton.mp this
      rw [maxcut_single_vertex_sum_strong_equilibrium_a_payoff_eq G A p v hvA,
          maxcut_single_vertex_sum_strong_equilibrium_a_payoff_eq G B p v hvB]
      rw [hP_univ]
      have hunion : Finset.univ.filter P = (A.filter P) ∪ (B.filter P) := by
        rw [← filter_union, hcover]
      have hdisj : Disjoint (A.filter P) (B.filter P) := by
        rw [disjoint_iff_inter_eq_empty, ← filter_inter_distrib, hinter]
        rw [filter_singleton]
        split_ifs with hPo
        · subst hvo
          exact False.elim (G.irrefl hPo.1)
        · rfl
      rw [hunion, card_union_of_disjoint hdisj]
    · have hpayB : maxcut_single_vertex_sum_strong_equilibrium_a_payoff G B p v = 0 := dif_neg hvB
      rw [hP_univ, hpayB, add_zero, maxcut_single_vertex_sum_strong_equilibrium_a_payoff_eq G A p v hvA]
      congr 1
      ext w
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro hw
        have hwA : w ∈ A := by
          by_contra hnwA
          have hwB : w ∈ B := by
            have : w ∈ A ∪ B := by rw [hcover]; exact mem_univ w
            exact (mem_union.mp this).resolve_left hnwA
          exact hsep v hvA hvB w hwB hnwA hw.1
        exact ⟨hwA, hw⟩
      · intro hw
        exact hw.2
  · have hvB : v ∈ B := by
      have : v ∈ A ∪ B := by rw [hcover]; exact mem_univ v
      exact (mem_union.mp this).resolve_left hvA
    have hpayA : maxcut_single_vertex_sum_strong_equilibrium_a_payoff G A p v = 0 := dif_neg hvA
    rw [hP_univ, hpayA, zero_add, maxcut_single_vertex_sum_strong_equilibrium_a_payoff_eq G B p v hvB]
    congr 1
    ext w
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hw
      have hwB : w ∈ B := by
        by_contra hnwB
        have hwA : w ∈ A := by
          have : w ∈ A ∪ B := by rw [hcover]; exact mem_univ w
          exact (mem_union.mp this).resolve_right hnwB
        have : ¬ G.Adj w v := hsep w hwA hnwB v hvB hvA
        exact this (G.adj_symm hw.1)
      exact ⟨hwB, hw⟩
    · intro hw
      exact hw.2

lemma maxcut_single_vertex_sum_strong_equilibrium_hstable_of_eq
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (σ : V → Fin k)
    (hA : is_maxcut_strong_equilibrium (G.induce (↑A : Set V)) (fun v => σ v.1))
    (τ : V → Fin k) (hchanged : ∃ v ∈ (↑A : Set V), τ v ≠ σ v) :
    ∃ v ∈ (↑A : Set V), τ v ≠ σ v ∧
      maxcut_single_vertex_sum_strong_equilibrium_a_payoff G A τ v ≤
      maxcut_single_vertex_sum_strong_equilibrium_a_payoff G A σ v := by
  by_contra hnot
  have hnot' : ∀ v ∈ (↑A : Set V), τ v ≠ σ v →
      maxcut_single_vertex_sum_strong_equilibrium_a_payoff G A σ v <
      maxcut_single_vertex_sum_strong_equilibrium_a_payoff G A τ v := by
    intro v hv hd
    by_contra hle
    push Not at hle
    exact hnot ⟨v, hv, hd, hle⟩
  obtain ⟨v0, hv0A, hd0⟩ := hchanged
  let GA := G.induce (↑A : Set V)
  let σA : (↑A : Set V) → Fin k := fun v => σ v.1
  let τA : (↑A : Set V) → Fin k := fun v => τ v.1
  let SA : Finset (↑A : Set V) := Finset.univ.filter (fun v => τA v ≠ σA v)
  have hdev : is_maxcut_strong_deviation GA σA SA τA := by
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨⟨v0, hv0A⟩, ?_⟩
      rw [mem_filter]
      exact ⟨mem_univ _, hd0⟩
    · intro v hv
      rw [mem_filter] at hv
      push Not at hv
      exact hv (mem_univ v)
    · intro v hv
      rw [mem_filter] at hv
      have hne : τ v.1 ≠ σ v.1 := hv.2
      have hvA : v.1 ∈ (↑A : Set V) := v.2
      have hlt := hnot' v.1 hvA hne
      have ha_σ : maxcut_single_vertex_sum_strong_equilibrium_a_payoff G A σ v.1 = maxcut_utility GA σA v := by
        dsimp [maxcut_single_vertex_sum_strong_equilibrium_a_payoff]
        split_ifs with h
        · rfl
        · exact False.elim (h v.2)
      have ha_τ : maxcut_single_vertex_sum_strong_equilibrium_a_payoff G A τ v.1 = maxcut_utility GA τA v := by
        dsimp [maxcut_single_vertex_sum_strong_equilibrium_a_payoff]
        split_ifs with h
        · rfl
        · exact False.elim (h v.2)
      rw [ha_σ, ha_τ] at hlt
      exact hlt
  exact hA SA τA hdev

theorem maxcut_single_vertex_sum_strong_equilibrium
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (o : V) (k : ℕ) (σ : V → Fin k)
    (hcover : A ∪ B = Finset.univ) (hinter : A ∩ B = {o})
    (hsep : ∀ v ∈ A, v ∉ B → ∀ w ∈ B, w ∉ A → ¬ G.Adj v w)
    (hA : is_maxcut_strong_equilibrium (G.induce (↑A : Set V)) (fun v => σ v.1))
    (hB : is_maxcut_strong_equilibrium (G.induce (↑B : Set V)) (fun v => σ v.1)) :
    is_maxcut_strong_equilibrium G σ := by
  have hoA : o ∈ (↑A : Set V) := by
    have : o ∈ A ∩ B := by rw [hinter]; exact mem_singleton_self o
    exact (mem_inter.mp this).1
  have hoB : o ∈ (↑B : Set V) := by
    have : o ∈ A ∩ B := by rw [hinter]; exact mem_singleton_self o
    exact (mem_inter.mp this).2
  have hcov : ∀ v, v ∈ (↑A : Set V) ∨ v ∈ (↑B : Set V) := by
    intro v
    have : v ∈ A ∪ B := by rw [hcover]; exact mem_univ v
    exact mem_union.mp this
  have hint : ∀ v, v ∈ (↑A : Set V) → v ∈ (↑B : Set V) → v = o := by
    intro v hvA hvB
    have : v ∈ A ∩ B := mem_inter.mpr ⟨hvA, hvB⟩
    rw [hinter] at this
    exact mem_singleton.mp this
  have ha0 : ∀ (p : V → Fin k) (v : V), v ∉ (↑A : Set V) →
      maxcut_single_vertex_sum_strong_equilibrium_a_payoff G A p v = 0 :=
    fun p v hv => dif_neg hv
  have hb0 : ∀ (p : V → Fin k) (v : V), v ∉ (↑B : Set V) →
      maxcut_single_vertex_sum_strong_equilibrium_a_payoff G B p v = 0 :=
    fun p v hv => dif_neg hv
  have hstabA : ∀ τ, (∃ v, v ∈ (↑A : Set V) ∧ τ v ≠ σ v) →
      ∃ v, v ∈ (↑A : Set V) ∧ τ v ≠ σ v ∧
        maxcut_single_vertex_sum_strong_equilibrium_a_payoff G A τ v ≤
        maxcut_single_vertex_sum_strong_equilibrium_a_payoff G A σ v :=
    fun τ h => maxcut_single_vertex_sum_strong_equilibrium_hstable_of_eq G A k σ hA τ h
  have hstabB : ∀ τ, (∃ v, v ∈ (↑B : Set V) ∧ τ v ≠ σ v) →
      ∃ v, v ∈ (↑B : Set V) ∧ τ v ≠ σ v ∧
        maxcut_single_vertex_sum_strong_equilibrium_a_payoff G B τ v ≤
        maxcut_single_vertex_sum_strong_equilibrium_a_payoff G B σ v :=
    fun τ h => maxcut_single_vertex_sum_strong_equilibrium_hstable_of_eq G B k σ hB τ h
  have hglue := maxcut_single_vertex_gluing_abstract σ (↑A : Set V) (↑B : Set V) o
    hoA hoB hcov hint
    (maxcut_single_vertex_sum_strong_equilibrium_a_payoff G A)
    (maxcut_single_vertex_sum_strong_equilibrium_a_payoff G B)
    ha0 hb0 hstabA hstabB
  intro S τ hdev
  rcases hdev with ⟨hne, houtside, hgain⟩
  have hdiff : ∃ v, τ v ≠ σ v := by
    by_contra hsame
    push Not at hsame
    obtain ⟨v0, hv0⟩ := hne
    have hg := hgain v0 hv0
    have hu_eq : maxcut_utility G τ v0 = maxcut_utility G σ v0 := by
      dsimp [maxcut_utility]
      congr 1
      ext w
      simp only [mem_filter, mem_univ, true_and]
      rw [hsame w, hsame v0]
    rw [hu_eq] at hg
    exact Nat.lt_irrefl _ hg
  obtain ⟨v, hvd, hle⟩ := hglue τ hdiff
  have hvS : v ∈ S := by
    by_contra hnvS
    exact hvd (houtside v hnvS)
  have hg := hgain v hvS
  rw [maxcut_single_vertex_sum_strong_equilibrium_utility_eq_sum_payoffs G A B o k τ hcover hinter hsep v,
      maxcut_single_vertex_sum_strong_equilibrium_utility_eq_sum_payoffs G A B o k σ hcover hinter hsep v] at hg
  exact Nat.not_le_of_lt hg hle
