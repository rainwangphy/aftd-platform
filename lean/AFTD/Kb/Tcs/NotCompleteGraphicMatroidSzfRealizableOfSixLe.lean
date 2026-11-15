import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteGraphicMatroidSzfRealizable
import AFTD.Kb.Tcs.SzfMultigraphClosure
import AFTD.Kb.Tcs.SzfMultiForced
import AFTD.Kb.Tcs.CompleteGraphCycleClosure
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# not_complete_graphic_matroid_szf_realizable_of_six_le

Topic: graphs   Node: 0fcd43154879

Provenance: formalization of a published result. Source: arXiv:2611.15741 Proposition 4.3 (via Corollary 2.12, multigraph version)

For n ≥ 6 the cycle matroid M(K_n) is not SZF-realizable by any multigraph on E(K_n).
-/

namespace PR1227Six

abbrev E (n : ℕ) := (⊤ : SimpleGraph (Fin n)).edgeSet

def ed {n : ℕ} (a b : Fin n) (h : a ≠ b) : E n := ⟨s(a, b), by simpa using h⟩

theorem iso_reach {n : ℕ} (F : Set (Sym2 (Fin n))) (v x : Fin n) (hv : ∀ e ∈ F, v ∉ e)
    (h : (SimpleGraph.fromEdgeSet F).Reachable v x) : v = x := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ =>
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    exact absurd (Sym2.mem_mk_left _ _) (hv _ hadj.1)

theorem inside3 {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (x : E n)
    (hx : ∀ y ∈ x.val, y = a ∨ y = b ∨ y = c) :
    x = ed a b hab ∨ x = ed b c hbc ∨ x = ed c a (Ne.symm hac) := by
  obtain ⟨p, hp⟩ := x
  induction p using Sym2.ind with
  | _ y z =>
    have hyz : y ≠ z := by simpa using hp
    have hy := hx y (Sym2.mem_mk_left y z)
    have hz := hx z (Sym2.mem_mk_right y z)
    simp only [ed, Subtype.mk.injEq, Sym2.eq_iff]
    rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;> simp_all

/-- Closure of a set of edges supported on vertices `W`: its closure stays supported on `W`. -/
theorem cl_inside {n : ℕ} (S : Set (E n)) (W : Fin n → Prop) (hS : ∀ e ∈ S, ∀ y ∈ e.val, W y)
    (x : E n) (hx : x ∈ complete_graph_cycle_closure n S) : ∀ y ∈ x.val, W y := by
  obtain ⟨a, b, hab, hr⟩ := hx
  have hne : a ≠ b := by
    have := x.2; rw [hab] at this; simpa using this
  have key : ∀ v, ¬ W v → ∀ u, (SimpleGraph.fromEdgeSet (Subtype.val '' S)).Reachable v u → v = u :=
    fun v hv u h => iso_reach _ v u (by
      rintro e ⟨e', he', rfl⟩ hve
      exact hv (hS e' he' v hve)) h
  intro y hy
  rw [hab, Sym2.mem_iff] at hy
  by_contra hW
  rcases hy with rfl | rfl
  · exact hne (key _ hW _ hr)
  · exact hne (key _ hW _ hr.symm).symm

theorem forced_mem {V : Type*} {μ : V → V → ℕ} {S : Set V} {x : V}
    (h : x ∈ szf_multigraph_closure μ S) : SzfMultiForced μ S x := h

theorem key3 {n : ℕ} (μ : E n → E n → ℕ)
    (hreal : ∀ S, szf_multigraph_closure μ S = complete_graph_cycle_closure n S)
    {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ u, ∀ x : E n, μ u x ≠ 0 ↔ ∀ y ∈ x.val, y = a ∨ y = b ∨ y = c := by
  set eab := ed a b hab
  set ebc := ed b c hbc
  set eca := ed c a (Ne.symm hac)
  have hmem : eca ∈ complete_graph_cycle_closure n {eab, ebc} := by
    refine ⟨c, a, rfl, ?_⟩
    have h1 : (SimpleGraph.fromEdgeSet (Subtype.val '' ({eab, ebc} : Set (E n)))).Adj c b := by
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨⟨ebc, by simp, by simp [ebc, ed, Sym2.eq_swap]⟩, Ne.symm hbc⟩
    have h2 : (SimpleGraph.fromEdgeSet (Subtype.val '' ({eab, ebc} : Set (E n)))).Adj b a := by
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨⟨eab, by simp, by simp [eab, ed, Sym2.eq_swap]⟩, Ne.symm hab⟩
    exact h1.reachable.trans h2.reachable
  have hT : ∀ x ∈ complete_graph_cycle_closure n {eab, ebc}, ∀ y ∈ x.val, y = a ∨ y = b ∨ y = c :=
    cl_inside _ _ (by
      intro e he y hy
      rcases he with rfl | rfl <;> simp [eab, ebc, ed] at hy <;> tauto)
  have hf : SzfMultiForced μ {eab, ebc} eca := forced_mem (by rw [hreal]; exact hmem)
  have hnS : eca ∉ ({eab, ebc} : Set (E n)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, eca, eab, ebc, ed, Subtype.mk.injEq,
      Sym2.eq_iff]
    omega
  cases hf with
  | init _ h => exact absurd h hnS
  | step u _ hu1 hall =>
    have hsupp : ∀ x, μ u x ≠ 0 → ∀ y ∈ x.val, y = a ∨ y = b ∨ y = c := by
      intro x hx
      by_cases hxe : x = eca
      · rw [hxe]; intro y hy; simp [eca, ed] at hy; tauto
      · exact hT x (by rw [← hreal]; exact hall x hxe hx)
    have hab_nb : μ u eab ≠ 0 := by
      intro h0
      have hfo : SzfMultiForced μ {ebc} eca := SzfMultiForced.step u eca hu1 (fun x hxe hx => by
        rcases inside3 hab hbc hac x (hsupp x hx) with h | h | h
        · rw [h] at hx; exact absurd h0 hx
        · rw [h]; exact SzfMultiForced.init _ rfl
        · exact absurd h hxe)
      have hcl : eca ∈ complete_graph_cycle_closure n {ebc} := by rw [← hreal]; exact hfo
      have := cl_inside {ebc} (fun y => y = b ∨ y = c)
        (by intro e he y hy; rw [he] at hy; simpa [ebc, ed] using hy) eca hcl a (by simp [eca, ed])
      rcases this with h | h
      · exact hab h
      · exact hac h
    have hbc_nb : μ u ebc ≠ 0 := by
      intro h0
      have hfo : SzfMultiForced μ {eab} eca := SzfMultiForced.step u eca hu1 (fun x hxe hx => by
        rcases inside3 hab hbc hac x (hsupp x hx) with h | h | h
        · rw [h]; exact SzfMultiForced.init _ rfl
        · rw [h] at hx; exact absurd h0 hx
        · exact absurd h hxe)
      have hcl : eca ∈ complete_graph_cycle_closure n {eab} := by rw [← hreal]; exact hfo
      have := cl_inside {eab} (fun y => y = a ∨ y = b)
        (by intro e he y hy; rw [he] at hy; simpa [eab, ed] using hy) eca hcl c (by simp [eca, ed])
      rcases this with h | h
      · exact hac h.symm
      · exact hbc h.symm
    refine ⟨u, fun x => ⟨hsupp x, fun hx => ?_⟩⟩
    rcases inside3 hab hbc hac x hx with h | h | h
    · rw [h]; exact hab_nb
    · rw [h]; exact hbc_nb
    · rw [h, hu1]; exact one_ne_zero

theorem six_le_aux (n : ℕ) (hn : 6 ≤ n) : ¬ complete_graphic_matroid_szf_realizable n := by
  rintro ⟨μ, -, hreal⟩
  classical
  have hk : ∀ s ∈ (Finset.univ : Finset (Fin n)).powersetCard 3, ∃ u : E n,
      ∀ x : E n, μ u x ≠ 0 ↔ ∀ y ∈ x.val, y ∈ s := by
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs.2
    obtain ⟨u, hu⟩ := key3 μ hreal hab hbc hac
    exact ⟨u, fun x => by rw [hu x]; simp⟩
  have : Nonempty (E n) := ⟨ed ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])⟩
  choose! f hf using hk
  have sub : ∀ s t : Finset (Fin n), 2 ≤ s.card →
      (∀ x : E n, (∀ y ∈ x.val, y ∈ s) → (∀ y ∈ x.val, y ∈ t)) → s ⊆ t := by
    intro s t hs2 h a ha
    obtain ⟨b, hb, hba⟩ : ∃ b ∈ s, b ≠ a := Finset.exists_mem_ne (by omega) a
    have := h (ed a b (Ne.symm hba)) (by
      intro y hy
      simp only [ed, Sym2.mem_iff] at hy
      rcases hy with rfl | rfl <;> assumption)
    exact this a (by simp [ed])
  have hinj : Set.InjOn f ((Finset.univ.powersetCard 3 : Finset (Finset (Fin n))) : Set _) := by
    intro s hs t ht hst
    have hs3 := (Finset.mem_powersetCard.mp hs).2
    have ht3 := (Finset.mem_powersetCard.mp ht).2
    have hiff : ∀ x : E n, (∀ y ∈ x.val, y ∈ s) ↔ (∀ y ∈ x.val, y ∈ t) := fun x => by
      rw [← hf s hs, ← hf t ht, hst]
    exact Finset.Subset.antisymm (sub s t (by omega) fun x => (hiff x).mp)
      (sub t s (by omega) fun x => (hiff x).mpr)
  have hle := Finset.card_le_card_of_injOn f (t := (Finset.univ : Finset (E n)))
    (fun s _ => Finset.mem_univ (f s)) hinj
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, Finset.card_univ,
    ← SimpleGraph.edgeFinset_card, SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_fin] at hle
  have h3 : n.choose 3 * 3 = n.choose 2 * (n - 2) := Nat.choose_succ_right_eq n 2
  have hpos : 0 < n.choose 2 := Nat.choose_pos (by omega)
  have hX : n.choose 2 * 4 ≤ n.choose 2 * (n - 2) := Nat.mul_le_mul_left _ (by omega)
  omega

end PR1227Six

theorem not_complete_graphic_matroid_szf_realizable_of_six_le (n : ℕ) (hn : 6 ≤ n) :
    ¬ complete_graphic_matroid_szf_realizable n := by
  exact PR1227Six.six_le_aux n hn
