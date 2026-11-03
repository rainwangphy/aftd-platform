import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_finite_predecessor_closed_set_cycle

Topic: graphs   Node: 53e06620420b

Provenance: helper lemma. Finite-cycle helper for the small-overlap structural route to OP-110.

A nonempty finite predecessor-closed subset of a loopless digraph contains a directed cycle.
-/

theorem digraph_finite_predecessor_closed_set_cycle
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α)
    (T : Finset α) (hne : T.Nonempty) (hloop : ∀ v, ¬ D.Adj v v)
    (hpred : ∀ x ∈ T, ∃ y ∈ T, D.Adj y x) :
    ∃ C : Finset α, digraph_directed_cycle_on D C ∧ C ⊆ T := by
  classical
  obtain ⟨w0, hw0a⟩ := hne
  let S := {x : α // x ∈ T}
  have hS : ∀ s : S, ∃ t : S, D.Adj t.1 s.1 := by
    intro ⟨s, hs⟩
    obtain ⟨w, hwT, hws⟩ := hpred s hs
    exact ⟨⟨w, hwT⟩, hws⟩
  let step : S → S := fun s => (hS s).choose
  have hstep : ∀ s : S, D.Adj (step s).1 s.1 := fun s => (hS s).choose_spec
  let s0 : S := ⟨w0, hw0a⟩
  let x : ℕ → S := fun t => step^[t] s0
  have hxstep : ∀ t, x (t + 1) = step (x t) := fun t => Function.iterate_succ_apply' step t s0
  have hxadj : ∀ t, D.Adj (x (t + 1)).1 (x t).1 := by
    intro t
    rw [hxstep]
    exact hstep (x t)
  have hninj : ¬ Function.Injective x := not_injective_infinite_finite x
  have hex : ∃ n, ∃ m < n, x m = x n := by
    by_contra h
    apply hninj
    intro u v huv
    rcases lt_trichotomy u v with hlt | heq | hgt
    · exfalso
      have : ¬ ∃ m < v, x m = x v := fun ⟨m, hm, hx⟩ => h ⟨v, m, hm, hx⟩
      push Not at this
      exact this u hlt huv
    · exact heq
    · exfalso
      have : ¬ ∃ m < u, x m = x u := fun ⟨m, hm, hx⟩ => h ⟨u, m, hm, hx⟩
      push Not at this
      exact this v hgt huv.symm
  classical
  let n := Nat.find hex
  obtain ⟨m, hmn, hxmn⟩ := Nat.find_spec hex
  have hmin : ∀ t < n, ¬ ∃ s < t, x s = x t := fun t ht => Nat.find_min hex ht
  have hinj : ∀ i < n, ∀ j < n, x i = x j → i = j := by
    intro i hi j hj hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exfalso
      exact hmin j hj ⟨i, hlt, hij⟩
    · exact heq
    · exfalso
      exact hmin i hi ⟨j, hgt, hij.symm⟩
  have hk : n - m ≠ 0 := by omega
  have hk2 : 2 ≤ n - m := by
    by_contra! h
    have hk1 : n - m = 1 := by omega
    have hnm1 : n = m + 1 := by omega
    have hx1 : x (m + 1) = x m := by rw [← hnm1, hxmn.symm]
    have hadj := hxadj m
    rw [hx1] at hadj
    exact hloop (x m).1 hadj
  let k := n - m
  let c : ℕ → α := fun i => (x (n - 1 - i)).1
  let l : List α := (List.range k).map c
  have hlen : l.length = k := by simp [l]
  have hnodup : l.Nodup := by
    refine (List.nodup_map_iff_inj_on List.nodup_range).mpr ?_
    intro i hi j hj hij
    simp only [List.mem_range] at hi hj
    have heq : x (n - 1 - i) = x (n - 1 - j) := Subtype.ext hij
    have hi' : n - 1 - i < n := by omega
    have hj' : n - 1 - j < n := by omega
    have : n - 1 - i = n - 1 - j := hinj (n - 1 - i) hi' (n - 1 - j) hj' heq
    omega
  have hchain : l.IsChain D.Adj := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have hik : i + 1 < k := by simpa [hlen] using hi
    have h1 : l[i] = c i := by simp [l]
    have h2 : l[i + 1] = c (i + 1) := by simp [l]
    rw [h1, h2]
    dsimp [c]
    have hrel : n - 1 - i = (n - 1 - (i + 1)) + 1 := by omega
    rw [hrel]
    exact hxadj (n - 1 - (i + 1))
  have hhead : l.head? = some (c 0) := by
    rw [List.head?_map, List.head?_range]
    have : k ≠ 0 := by omega
    simp [this]
  have hlast : l.getLast? = some (c (k - 1)) := by
    rw [List.getLast?_map, List.getLast?_range]
    have : k ≠ 0 := by omega
    simp [this]
  have hadj_last_head : D.Adj (c (k - 1)) (c 0) := by
    change D.Adj (x (n - 1 - (k - 1))).1 (x (n - 1 - 0)).1
    have h1 : n - 1 - (k - 1) = m := by omega
    have h2 : n - 1 - 0 = n - 1 := by omega
    rw [h1, h2]
    have heq : (x m).1 = (x n).1 := by rw [hxmn]
    rw [heq]
    have hnrel : n = (n - 1) + 1 := by omega
    nth_rw 1 [hnrel]
    exact hxadj (n - 1)
  refine ⟨l.toFinset, ⟨l, hnodup, by rw [hlen]; exact hk2, rfl, hchain, ⟨c 0, c (k - 1), hhead, hlast, hadj_last_head⟩⟩, ?_⟩
  intro v hv
  rw [List.mem_toFinset] at hv
  rcases List.mem_map.mp hv with ⟨i, hi, rfl⟩
  exact (x (n - 1 - i)).2
