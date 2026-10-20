import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphMultiRadioNumber
import AFTD.Kb.Tcs.SimpleGraphIsMultiRadioLabeling
import AFTD.Kb.Tcs.MultiLabelSpan
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.G

/-!
# simple_graph_multi_radio_number_path_mono

Topic: graphs   Node: b83ae8d6a2cc

Provenance: helper lemma. for simple_graph_multi_radio_number_path_three_of_le (OP-384)

The (m,k)-radio number of the path P_n is nondecreasing in n: a labeling of P_{n+1} restricts to one of P_n.
-/

lemma simple_graph_multi_radio_number_path_mono_dist_castSucc_le (n : ℕ) (a b : Fin n) :
    (SimpleGraph.pathGraph (n+1)).dist (Fin.castSucc a) (Fin.castSucc b) ≤
      (SimpleGraph.pathGraph n).dist a b := by
  obtain ⟨p, hp⟩ := ((SimpleGraph.pathGraph_preconnected n) a b).exists_walk_length_eq_dist
  let hhom : SimpleGraph.pathGraph n →g SimpleGraph.pathGraph (n+1) :=
    { toFun := Fin.castSucc
      map_rel' := by
        intro x y hxy
        simpa [SimpleGraph.pathGraph_adj] using hxy }
  have key := SimpleGraph.dist_le (SimpleGraph.Walk.map hhom p)
  rw [SimpleGraph.Walk.length_map] at key
  rw [hp] at key
  exact key

lemma simple_graph_multi_radio_number_path_mono_labeling_comp {V W : Type*}
    (G : SimpleGraph V) (G' : SimpleGraph W) (m k : ℕ) (f : W → Finset ℕ) (φ : V → W)
    (hf : simple_graph_is_multi_radio_labeling G' m k f)
    (hφ : Function.Injective φ)
    (hdist : ∀ x y, G'.dist (φ x) (φ y) ≤ G.dist x y) :
    simple_graph_is_multi_radio_labeling G m k (fun v => f (φ v)) := by
  refine ⟨fun v => hf.1 (φ v), ?_⟩
  intro x y a ha b hb hne
  have hne' : (φ x, a) ≠ (φ y, b) := by
    intro h
    apply hne
    have h1 : φ x = φ y := congrArg Prod.fst h
    have h2 : a = b := congrArg Prod.snd h
    rw [hφ h1, h2]
  have h1 := hf.2 (φ x) (φ y) a ha b hb hne'
  have h2 : ((G'.dist (φ x) (φ y) : ℕ) : ℤ) ≤ ((G.dist x y : ℕ) : ℤ) := by
    exact_mod_cast hdist x y
  linarith

lemma simple_graph_multi_radio_number_path_mono_span_comp_le {V W : Type*}
    [Fintype V] [Fintype W] (f : W → Finset ℕ) (φ : V → W) :
    multi_label_span (fun v => f (φ v)) ≤ multi_label_span f := by
  simp only [multi_label_span]
  refine Finset.sup_le fun x _ => Finset.sup_le fun y _ => ?_
  exact le_trans
    (Finset.le_sup (s := (Finset.univ : Finset W))
      (f := fun y => (f (φ x)).sup fun a => (f y).sup fun b => b - a) (Finset.mem_univ (φ y)))
    (Finset.le_sup (s := (Finset.univ : Finset W))
      (f := fun x => (Finset.univ : Finset W).sup fun y =>
        (f x).sup fun a => (f y).sup fun b => b - a) (Finset.mem_univ (φ x)))

lemma simple_graph_multi_radio_number_path_mono_exists_labeling {V : Type*} [Fintype V]
    (G : SimpleGraph V) (m k : ℕ) :
    ∃ f : V → Finset ℕ, simple_graph_is_multi_radio_labeling G m k f := by
  classical
  let h : V × Fin m → ℕ := fun p => (Fintype.equivFin (V × Fin m) p).val
  have h_inj : Function.Injective h := by
    intro p q hpq
    exact (Fintype.equivFin (V × Fin m)).injective (Fin.val_injective hpq)
  refine ⟨fun v => (Finset.univ : Finset (Fin m)).image (fun a => h (v, a) * (k+1)), ?_, ?_⟩
  · intro v
    rw [Finset.card_image_of_injective _ ?_]
    simp
    intro a b hab
    have hk : 0 < k + 1 := Nat.succ_pos k
    have h1 : h (v, a) = h (v, b) := (Nat.mul_right_cancel_iff hk).mp hab
    exact congrArg Prod.snd (h_inj h1)
  · intro x y a ha b hb hne
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    have hneN : h (x, a') ≠ h (y, b') := by
      intro hEq
      apply hne
      have hp : (x, a') = (y, b') := h_inj hEq
      simp only [Prod.mk.injEq] at hp
      rw [← ha', ← hb', hp.1, hp.2]
    have hz : ((h (x, a') : ℤ)) - ((h (y, b') : ℤ)) ≠ 0 := by
      intro hcon
      apply hneN
      have : ((h (x, a') : ℤ)) = ((h (y, b') : ℤ)) := by linarith
      exact_mod_cast this
    have step1 : ((a : ℤ) - (b : ℤ)) =
        (((h (x, a') : ℤ)) - ((h (y, b') : ℤ))) * ((k : ℤ) + 1) := by
      rw [← ha', ← hb']
      push_cast
      ring
    have habs : |((a : ℤ) - (b : ℤ))| =
        |(((h (x, a') : ℤ)) - ((h (y, b') : ℤ)))| * ((k : ℤ) + 1) := by
      rw [step1, abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ (k : ℤ) + 1)]
    have hone : (1:ℤ) ≤ |(((h (x, a') : ℤ)) - ((h (y, b') : ℤ)))| := Int.one_le_abs hz
    rw [habs]
    calc ((k : ℤ) + 1 - ((G.dist x y : ℕ) : ℤ)) ≤ (k : ℤ) + 1 := by
          have : (0:ℤ) ≤ ((G.dist x y : ℕ) : ℤ) := by positivity
          linarith
      _ = 1 * ((k : ℤ) + 1) := by ring
      _ ≤ |(((h (x, a') : ℤ)) - ((h (y, b') : ℤ)))| * ((k : ℤ) + 1) := by
          apply mul_le_mul_of_nonneg_right hone (by positivity)

theorem simple_graph_multi_radio_number_path_mono (n m k : ℕ) (hn : 1 ≤ n) :
    simple_graph_multi_radio_number (SimpleGraph.pathGraph n) m k ≤
      simple_graph_multi_radio_number (SimpleGraph.pathGraph (n + 1)) m k := by
  classical
  have hne : {s : ℕ | ∃ f : Fin (n+1) → Finset ℕ,
      simple_graph_is_multi_radio_labeling (SimpleGraph.pathGraph (n+1)) m k f ∧
      multi_label_span f = s}.Nonempty := by
    obtain ⟨f, hf⟩ := simple_graph_multi_radio_number_path_mono_exists_labeling
      (SimpleGraph.pathGraph (n+1)) m k
    exact ⟨_, f, hf, rfl⟩
  obtain ⟨f, hf, hspan⟩ := Nat.sInf_mem hne
  have hlabel : simple_graph_is_multi_radio_labeling (SimpleGraph.pathGraph n) m k
      (fun v => f (Fin.castSucc v)) :=
    simple_graph_multi_radio_number_path_mono_labeling_comp _ _ m k f Fin.castSucc hf
      (Fin.castSucc_injective n)
      (fun x y => simple_graph_multi_radio_number_path_mono_dist_castSucc_le n x y)
  have hmem : multi_label_span (fun v => f (Fin.castSucc v)) ∈ {s : ℕ | ∃ g : Fin n → Finset ℕ,
      simple_graph_is_multi_radio_labeling (SimpleGraph.pathGraph n) m k g ∧
      multi_label_span g = s} := ⟨_, hlabel, rfl⟩
  have h1 : simple_graph_multi_radio_number (SimpleGraph.pathGraph n) m k ≤
      multi_label_span (fun v => f (Fin.castSucc v)) := Nat.sInf_le hmem
  have h2 : multi_label_span (fun v => f (Fin.castSucc v)) ≤ multi_label_span f :=
    simple_graph_multi_radio_number_path_mono_span_comp_le f Fin.castSucc
  have h3 : multi_label_span f =
      simple_graph_multi_radio_number (SimpleGraph.pathGraph (n+1)) m k := hspan
  exact le_trans h1 (le_trans h2 (le_of_eq h3))
