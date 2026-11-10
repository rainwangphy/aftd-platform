import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongEquilibriumOfOneDoubleDefect
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_strong_equilibrium_of_near_defect_one

Topic: equilibria   Node: 35faa200d6cd

Provenance: helper lemma. Structural consequence of the one-exception potential route for OP-85.

If deleting a vertex produces a graph admitting a defect-one k-coloring and the deleted vertex has degree below 2k, then the original graph has a strong k-color equilibrium.
-/

theorem maxcut_strong_equilibrium_of_near_defect_one
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (k : ℕ) (hd : G.degree v < 2 * k)
    (hsub : ∃ σ : (↑(Finset.univ.erase v) : Set V) → Fin k,
      ∀ x : (↑(Finset.univ.erase v) : Set V),
        (Finset.univ.filter fun y => (G.induce (↑(Finset.univ.erase v) : Set V)).Adj x y ∧ σ y = σ x).card ≤ 1) :
    ∃ σ : V → Fin k, is_maxcut_strong_equilibrium G σ := by
  classical
  obtain ⟨s, hs⟩ := hsub
  have hk : 0 < k := by
    have h := Nat.zero_le (G.degree v); omega
  let T : Set V := ↑(Finset.univ.erase v)
  let g : (w : V) → w ≠ v → Fin k := fun w hw => s ⟨w, by simp [T, hw]⟩
  let c₀ : Fin k := ⟨0, hk⟩
  let f : V → Fin k := fun w => if hw : w = v then c₀ else g w hw
  have hdeg : (Finset.univ.filter (fun w => G.Adj v w)).card < k * 2 := by
    rw [← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨c, -, hc⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul
    (s := Finset.univ.filter (fun w => G.Adj v w)) (t := (Finset.univ : Finset (Fin k)))
    (f := f) (n := 2) (by simpa using hdeg)
  let τ : V → Fin k := fun u => if h : u = v then c else g u h
  have hτv : τ v = c := by simp [τ]
  have hτne : ∀ (w : V) (hw : w ≠ v), τ w = f w := by
    intro w hw
    simp [τ, f, hw]
  have hτg : ∀ (w : V) (hw : w ≠ v), τ w = g w hw := by
    intro w hw; simp [τ, hw]
  have hv1 : (Finset.univ.filter fun w => G.Adj v w ∧ τ w = τ v).card ≤ 1 := by
    have heq : (Finset.univ.filter fun w => G.Adj v w ∧ τ w = τ v) =
        Finset.univ.filter (fun w => G.Adj v w ∧ f w = c) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hadj, hτ⟩
        have hwv : w ≠ v := fun h => G.irrefl (h ▸ hadj)
        exact ⟨hadj, by rw [← hτne w hwv, hτ, hτv]⟩
      · rintro ⟨hadj, hf⟩
        have hwv : w ≠ v := fun h => G.irrefl (h ▸ hadj)
        exact ⟨hadj, by rw [hτne w hwv, hf, hτv]⟩
    rw [heq]
    have heq2 : Finset.univ.filter (fun w => G.Adj v w ∧ f w = c) =
        (Finset.univ.filter (fun w => G.Adj v w)).filter (fun w => f w = c) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq2]
    omega
  have key : ∀ (u : V) (hu : u ≠ v),
      (Finset.univ.filter fun w : V => G.Adj u w ∧ τ w = τ u).filter (fun w => w ≠ v)
      = (Finset.univ.filter fun y : T => (G.induce T).Adj ⟨u, by simp [T, hu]⟩ y ∧ s y = s ⟨u, by simp [T, hu]⟩).image (fun y : T => y.1) := by
    intro u hu
    have hτu : τ u = s ⟨u, by simp [T, hu]⟩ := by simp [τ, hu, g]
    ext w
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hadj, hτ⟩, hwv⟩
      refine ⟨⟨w, by simp [T, hwv]⟩, ⟨?_, ?_⟩, rfl⟩
      · rw [SimpleGraph.induce_adj]; exact hadj
      · show g w hwv = s ⟨u, by simp [T, hu]⟩
        rw [← hτg w hwv, hτ, hτu]
    · rintro ⟨y, ⟨hyadj, hys⟩, hyw⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [SimpleGraph.induce_adj] at hyadj
        rw [← hyw]; exact hyadj
      · rw [← hyw]
        have hyv : y.1 ≠ v := by
          have h := y.2; simp [T] at h; exact h
        rw [hτg y.1 hyv, hτu]
        change s ⟨y.1, by simp [T, hyv]⟩ = s ⟨u, by simp [T, hu]⟩
        rw [show (⟨y.1, by simp [T, hyv]⟩ : T) = y from Subtype.ext rfl, hys]
      · rw [← hyw]
        have hyv : y.1 ≠ v := by
          have h := y.2; simp [T] at h; exact h
        exact hyv
  have hpair : ∀ (u : V) (hu : u ≠ v),
      ((Finset.univ.filter fun w : V => G.Adj u w ∧ τ w = τ u).filter (fun w => w = v)).card ≤ 1 ∧
      ((Finset.univ.filter fun w : V => G.Adj u w ∧ τ w = τ u).filter (fun w => w ≠ v)).card ≤ 1 := by
    intro u hu
    constructor
    · have hsub' : (Finset.univ.filter fun w : V => G.Adj u w ∧ τ w = τ u).filter (fun w => w = v) ⊆ {v} := by
        intro w hw
        rw [Finset.mem_filter] at hw
        rw [Finset.mem_singleton]
        exact hw.2
      calc _ ≤ ({v} : Finset V).card := Finset.card_le_card hsub'
        _ = 1 := Finset.card_singleton v
    · rw [key u hu]
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
      exact hs ⟨u, by simp [T, hu]⟩
  have hD_le : ∀ u : V, (Finset.univ.filter fun w => G.Adj u w ∧ τ w = τ u).card ≤ 2 := by
    intro u
    by_cases hu : u = v
    · subst hu; omega
    · have hsplit : (Finset.univ.filter fun w : V => G.Adj u w ∧ τ w = τ u)
          = ((Finset.univ.filter fun w : V => G.Adj u w ∧ τ w = τ u).filter (fun w => w = v))
            ∪ ((Finset.univ.filter fun w : V => G.Adj u w ∧ τ w = τ u).filter (fun w => w ≠ v)) := by
        rw [Finset.filter_union_filter_not_eq]
      rw [hsplit]
      have h1 := (hpair u hu).1
      have h2 := (hpair u hu).2
      calc (((Finset.univ.filter fun w : V => G.Adj u w ∧ τ w = τ u).filter (fun w => w = v))
              ∪ ((Finset.univ.filter fun w : V => G.Adj u w ∧ τ w = τ u).filter (fun w => w ≠ v))).card
          ≤ _ + _ := Finset.card_union_le _ _
        _ ≤ 1 + 1 := by omega
        _ = 2 := by norm_num
  have hv_mem : ∀ (u : V), u ≠ v → (Finset.univ.filter fun w => G.Adj u w ∧ τ w = τ u).card = 2 →
      v ∈ Finset.univ.filter fun w => G.Adj u w ∧ τ w = τ u := by
    intro u hu hcard
    by_contra hvD
    have hvD' : ¬ (G.Adj u v ∧ τ v = τ u) := by
      intro h
      exact hvD (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have heq : (Finset.univ.filter fun w : V => G.Adj u w ∧ τ w = τ u)
        = (Finset.univ.filter fun w : V => G.Adj u w ∧ τ w = τ u).filter (fun w => w ≠ v) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hw
        exact ⟨hw, fun h => hvD' (h ▸ hw)⟩
      · intro hw; exact hw.1
    rw [heq] at hcard
    have hb := (hpair u hu).2
    omega
  have huniq : ∀ u₁ u₂ : V,
      (Finset.univ.filter fun w => G.Adj u₁ w ∧ τ w = τ u₁).card = 2 →
      (Finset.univ.filter fun w => G.Adj u₂ w ∧ τ w = τ u₂).card = 2 → u₁ = u₂ := by
    intro u₁ u₂ h1 h2
    have hu1 : u₁ ≠ v := by
      intro h; subst h; omega
    have hu2 : u₂ ≠ v := by
      intro h; subst h; omega
    have hm1 : u₁ ∈ Finset.univ.filter (fun w => G.Adj v w ∧ τ w = τ v) := by
      have h := hv_mem u₁ hu1 h1
      rw [Finset.mem_filter] at h ⊢
      exact ⟨Finset.mem_univ _, h.2.1.symm, h.2.2.symm⟩
    have hm2 : u₂ ∈ Finset.univ.filter (fun w => G.Adj v w ∧ τ w = τ v) := by
      have h := hv_mem u₂ hu2 h2
      rw [Finset.mem_filter] at h ⊢
      exact ⟨Finset.mem_univ _, h.2.1.symm, h.2.2.symm⟩
    exact (Finset.card_le_one.mp hv1) u₁ hm1 u₂ hm2
  obtain ⟨σ, hse, -, -⟩ := maxcut_strong_equilibrium_of_one_double_defect G ⟨τ, hD_le, huniq⟩
  exact ⟨σ, hse⟩
