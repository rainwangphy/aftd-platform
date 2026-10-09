import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphDominatingSetsContaining

/-!
# simple_graph_local_avg_dominating_order_of_degree_eq_card_sub_two

Topic: graphs   Node: 9a593c49e342

Provenance: formalization of a published result. Source: arXiv:2610.11446 (On the local average order of dominating sets), Corollary 4.2. The paper's connectivity hypothesis is kept though the proof here does not use it; the proof counts the sets containing v that meet N[u] directly instead of differentiating the domination polynomial.

Let G be a connected graph of order n ≥ 3 and v a vertex of degree n − 2, with u the vertex other than v not adjacent to v. Then the dominating sets containing v have average size (n+1)/2 + (deg u + 1)/(2(2^{deg u + 1} − 1)).
-/

theorem simple_graph_local_avg_dominating_order_of_degree_eq_card_sub_two {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hn : 3 ≤ Fintype.card V) (v u : V) (huv : u ≠ v) (hnadj : ¬ G.Adj v u)
    (hdeg : G.degree v = Fintype.card V - 2) :
    simple_graph_local_avg_dominating_order G v =
      ((Fintype.card V : ℚ) + 1) / 2 +
        ((G.degree u : ℚ) + 1) / (2 * (2 ^ (G.degree u + 1) - 1)) := by
  classical
  set n := Fintype.card V with hn'
  set D := simple_graph_dominating_sets_containing G v with hD
  -- sets containing `v` inside `insert v W`: `2^|W|` of them, total size `2^|W| + |W| 2^|W| / 2`
  have count : ∀ W : Finset V, v ∉ W →
      (Finset.univ.filter (fun S : Finset V => v ∈ S ∧ S ⊆ insert v W)).card = 2 ^ W.card ∧
      ∑ S ∈ Finset.univ.filter (fun S : Finset V => v ∈ S ∧ S ⊆ insert v W), (S.card : ℚ) =
        2 ^ W.card + W.card * 2 ^ W.card / 2 := by
    intro W hvW
    have himg : Finset.univ.filter (fun S : Finset V => v ∈ S ∧ S ⊆ insert v W) =
        W.powerset.image (insert v) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_powerset]
      constructor
      · rintro ⟨hvS, hSW⟩
        refine ⟨S.erase v, fun x hx => ?_, Finset.insert_erase hvS⟩
        have := hSW (Finset.mem_of_mem_erase hx)
        rw [Finset.mem_insert] at this
        rcases this with h | h
        · exact absurd h (Finset.ne_of_mem_erase hx)
        · exact h
      · rintro ⟨T, hTW, rfl⟩
        exact ⟨Finset.mem_insert_self v T, Finset.insert_subset_insert v hTW⟩
    have hinj : Set.InjOn (insert v) (W.powerset : Set (Finset V)) := by
      intro S hS T hT h
      simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
        Finset.coe_subset] at hS hT
      have hvS : v ∉ S := fun h' => hvW (hS h')
      have hvT : v ∉ T := fun h' => hvW (hT h')
      rw [← Finset.erase_insert hvS, ← Finset.erase_insert hvT]
      exact congrArg (fun U => Finset.erase U v) h
    -- complements in `W` pair sizes `k` and `|W| - k`
    have hhalf : 2 * ∑ T ∈ W.powerset, (T.card : ℚ) = W.card * 2 ^ W.card := by
      have hc : ∑ T ∈ W.powerset, (T.card : ℚ) = ∑ T ∈ W.powerset, ((W.card : ℚ) - T.card) := by
        refine Finset.sum_nbij' (fun T => W \ T) (fun T => W \ T) ?_ ?_ ?_ ?_ ?_
        · intro T hT; simp only [Finset.mem_coe, Finset.mem_powerset] at hT ⊢; exact Finset.sdiff_subset
        · intro T hT; simp only [Finset.mem_coe, Finset.mem_powerset] at hT ⊢; exact Finset.sdiff_subset
        · intro T hT; simp only [Finset.mem_coe, Finset.mem_powerset] at hT; exact Finset.sdiff_sdiff_eq_self hT
        · intro T hT; simp only [Finset.mem_coe, Finset.mem_powerset] at hT; exact Finset.sdiff_sdiff_eq_self hT
        · intro T hT
          rw [Finset.mem_powerset] at hT
          rw [Finset.card_sdiff_of_subset hT, Nat.cast_sub (Finset.card_le_card hT)]
          ring
      rw [two_mul]
      nth_rewrite 2 [hc]
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun T _ =>
        (show (T.card : ℚ) + ((W.card : ℚ) - T.card) = W.card by ring), Finset.sum_const,
        Finset.card_powerset, nsmul_eq_mul]
      push_cast; ring
    rw [himg, Finset.card_image_of_injOn hinj, Finset.card_powerset, Finset.sum_image hinj]
    refine ⟨rfl, ?_⟩
    have : ∀ T ∈ W.powerset, ((insert v T).card : ℚ) = T.card + 1 := by
      intro T hT
      rw [Finset.mem_powerset] at hT
      rw [Finset.card_insert_of_notMem (fun h => hvW (hT h))]
      push_cast; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_powerset,
      nsmul_eq_mul]
    push_cast
    linarith
  -- every vertex other than `u` and `v` is a neighbour of `v`
  have hnbr : G.neighborFinset v = (Finset.univ.erase v).erase u := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      rw [G.mem_neighborFinset] at hw
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨fun h => hnadj (h ▸ hw), (G.ne_of_adj hw).symm, Finset.mem_univ w⟩
    · rw [G.card_neighborFinset_eq_degree, hdeg,
        Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨huv, Finset.mem_univ u⟩),
        Finset.card_erase_of_mem (Finset.mem_univ v)]
      rfl
  have hadj : ∀ w, w ≠ v → w ≠ u → G.Adj v w := by
    intro w hwv hwu
    rw [← G.mem_neighborFinset, hnbr, Finset.mem_erase, Finset.mem_erase]
    exact ⟨hwu, hwv, Finset.mem_univ w⟩
  set Y : Finset V := insert u (G.neighborFinset u) with hY
  have hvY : v ∉ Y := by
    rw [hY, Finset.mem_insert, G.mem_neighborFinset]
    rintro (h | h)
    · exact huv h.symm
    · exact hnadj h.symm
  set X : Finset V := Finset.univ.erase v with hX
  set Z : Finset V := X \ Y with hZ
  have hvX : v ∉ X := Finset.notMem_erase v _
  have hvZ : v ∉ Z := fun h => hvX (Finset.mem_sdiff.1 h).1
  have hYX : Y ⊆ X := fun w hw => Finset.mem_erase.2 ⟨fun h => hvY (h ▸ hw), Finset.mem_univ w⟩
  have hXcard : X.card = n - 1 := by rw [hX, Finset.card_erase_of_mem (Finset.mem_univ v)]; rfl
  have hYcard : Y.card = G.degree u + 1 := by
    rw [hY, Finset.card_insert_of_notMem (by simp), G.card_neighborFinset_eq_degree]
  have hZcard : Z.card + (G.degree u + 1) = n - 1 := by
    rw [hZ, Finset.card_sdiff_of_subset hYX, hXcard, ← hYcard]
    have := Finset.card_le_card hYX
    omega
  -- the dominating sets containing `v` are the sets containing `v` that meet `N[u]`
  set P := Finset.univ.filter (fun S : Finset V => v ∈ S ∧ S ⊆ insert v X) with hP
  set Q := Finset.univ.filter (fun S : Finset V => v ∈ S ∧ S ⊆ insert v Z) with hQ
  have hQP : Q ⊆ P := by
    intro S hS
    rw [hQ, Finset.mem_filter] at hS
    rw [hP, Finset.mem_filter]
    exact ⟨Finset.mem_univ S, hS.2.1,
      hS.2.2.trans (Finset.insert_subset_insert v Finset.sdiff_subset)⟩
  have hDPQ : D = P \ Q := by
    ext S
    rw [hD, Finset.mem_sdiff, hP, hQ]
    unfold simple_graph_dominating_sets_containing
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hSX : v ∈ S → S ⊆ insert v X := fun _ w _ => by
      rw [Finset.mem_insert, hX, Finset.mem_erase]
      by_cases h : w = v
      · exact Or.inl h
      · exact Or.inr ⟨h, Finset.mem_univ w⟩
    constructor
    · rintro ⟨hvS, hdom⟩
      refine ⟨⟨hvS, hSX hvS⟩, fun ⟨_, hSZ⟩ => ?_⟩
      rcases hdom u with h | ⟨w, hw, hwu⟩
      · have := hSZ h
        rw [Finset.mem_insert, hZ, Finset.mem_sdiff] at this
        rcases this with h' | h'
        · exact huv h'
        · exact h'.2 (by rw [hY]; exact Finset.mem_insert_self u _)
      · have := hSZ hw
        rw [Finset.mem_insert, hZ, Finset.mem_sdiff] at this
        rcases this with h' | h'
        · exact hnadj (h' ▸ hwu)
        · exact h'.2 (by rw [hY, Finset.mem_insert, G.mem_neighborFinset]; exact Or.inr hwu.symm)
    · rintro ⟨⟨hvS, _⟩, hnot⟩
      refine ⟨hvS, fun w => ?_⟩
      by_cases hwv : w = v
      · exact Or.inl (hwv ▸ hvS)
      by_cases hwu : w = u
      · -- `S` meets `N[u]`
        subst hwu
        by_contra hcon
        push_neg at hcon
        apply hnot
        refine ⟨hvS, fun x hx => ?_⟩
        rw [Finset.mem_insert, hZ, Finset.mem_sdiff, hX, Finset.mem_erase]
        by_cases hxv : x = v
        · exact Or.inl hxv
        · refine Or.inr ⟨⟨hxv, Finset.mem_univ x⟩, ?_⟩
          rw [hY, Finset.mem_insert, G.mem_neighborFinset]
          rintro (h | h)
          · exact hcon.1 (h ▸ hx)
          · exact hcon.2 x hx h.symm
      · exact Or.inr ⟨v, hvS, hadj w hwv hwu⟩
  obtain ⟨hPc, hPs⟩ := count X hvX
  obtain ⟨hQc, hQs⟩ := count Z hvZ
  have hDcard : (D.card : ℚ) = 2 ^ X.card - 2 ^ Z.card := by
    rw [hDPQ, Finset.card_sdiff_of_subset hQP, hPc, hQc,
      Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) (Finset.card_le_card (Finset.sdiff_subset)))]
    push_cast; ring
  have hDsum : ∑ S ∈ D, (S.card : ℚ) = (2 ^ X.card + X.card * 2 ^ X.card / 2) -
      (2 ^ Z.card + Z.card * 2 ^ Z.card / 2) := by
    rw [hDPQ, ← hPs, ← hQs, ← Finset.sum_sdiff hQP]; ring
  -- algebra, with `|X| = |Z| + (d + 1)` and `|X| = n - 1`
  set d := G.degree u with hd
  set z := Z.card with hz
  have hXz : X.card = z + (d + 1) := by rw [hXcard]; omega
  have hnq : (n : ℚ) = z + d + 2 := by
    have : n = z + (d + 1) + 1 := by omega
    rw [this]; push_cast; ring
  unfold simple_graph_local_avg_dominating_order
  rw [← hD, hDsum, hDcard, hXz, hnq]
  have h2 : (2 : ℚ) ^ (d + 1) - 1 ≠ 0 := by
    have : (1 : ℚ) < 2 ^ (d + 1) := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have h2z : (0 : ℚ) < 2 ^ z := by positivity
  rw [pow_add]
  push_cast
  field_simp
  ring
