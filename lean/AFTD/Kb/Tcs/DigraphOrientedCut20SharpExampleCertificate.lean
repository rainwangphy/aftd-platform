import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphOrientedCut20SharpExample
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_oriented_cut20_sharp_example_certificate

Topic: graphs   Node: 2bf0bd88a5d7

Provenance: helper lemma. Structural certificate for the construction in experiment 26321.

The explicit oriented example has a seven-outregular twenty-vertex part with twenty outgoing arcs and no two disjoint cycles; every nonempty induced subset of minimum outdegree two has at least three vertices of outdegree two.
-/

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

private instance : DecidableRel digraph_oriented_cut20_sharp_example.Adj := by
  unfold digraph_oriented_cut20_sharp_example
  infer_instance

private theorem in833_oriented_cut20_orientation :
    ∀ u v, digraph_oriented_cut20_sharp_example.Adj u v → ¬ digraph_oriented_cut20_sharp_example.Adj v u := by
  decide

private theorem in833_oriented_cut20_degree :
    ∀ v ∈ (Finset.univ.filter fun v : Fin 26 => v.val < 20),
      (Finset.univ.filter fun w => digraph_oriented_cut20_sharp_example.Adj v w).card = 7 := by
  decide

private theorem in833_oriented_cut20_boundary :
    (∑ v ∈ (Finset.univ.filter fun v : Fin 26 => v.val < 20),
      ((Finset.univ.filter fun v : Fin 26 => v.val < 20)ᶜ.filter fun w => digraph_oriented_cut20_sharp_example.Adj v w).card) = 20 := by
  decide

private theorem in833_oriented_no_sinks
    (T : Finset (Fin 26))
    (hs : ∀ v ∈ T, ∃ w ∈ T, digraph_oriented_cut20_sharp_example.Adj v w) :
    ∀ v ∈ T, v.val < 20 := by
  intro v hv
  obtain ⟨w, hw, ha⟩ := hs v hv
  change (v.val < 5 ∧ (w.val < v.val ∨ w.val = 5 ∨ (20 ≤ w.val ∧ v.val + w.val < 26))) ∨
    (v.val = 5 ∧ 13 ≤ w.val ∧ w.val < 20) ∨
    (6 ≤ v.val ∧ v.val < 13 ∧ (w.val < 6 ∨ w.val = 6 + (v.val - 6 + 1) % 7)) ∨
    (13 ≤ v.val ∧ v.val < 20 ∧ ((13 ≤ w.val ∧ w.val < v.val) ∨ (6 ≤ w.val ∧ v.val + w.val < 26))) at ha
  omega

private theorem in833_oriented_low_witness
    (T : Finset (Fin 26))
    (hnosink : ∀ v ∈ T, v.val < 20)
    (hex : ∃ v ∈ T, v.val < 5) :
    ∃ v ∈ T, v.val < 5 ∧
      (T.filter fun w => digraph_oriented_cut20_sharp_example.Adj v w) ⊆ {5} := by
  let L := T.filter fun v => v.val < 5
  have hL : L.Nonempty := by
    obtain ⟨v, hv, hv5⟩ := hex
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hv5⟩⟩
  let v := L.min' hL
  have hvL : v ∈ L := Finset.min'_mem L hL
  have hvT : v ∈ T := (Finset.mem_filter.mp hvL).1
  have hv5 : v.val < 5 := (Finset.mem_filter.mp hvL).2
  refine ⟨v, hvT, hv5, ?_⟩
  intro w hw
  obtain ⟨hwT, ha⟩ := Finset.mem_filter.mp hw
  have hw20 := hnosink w hwT
  have hmin : ∀ z ∈ L, v.val ≤ z.val := by
    intro z hz
    exact Finset.min'_le L z hz
  change (v.val < 5 ∧ (w.val < v.val ∨ w.val = 5 ∨ (20 ≤ w.val ∧ v.val + w.val < 26))) ∨
    (v.val = 5 ∧ 13 ≤ w.val ∧ w.val < 20) ∨
    (6 ≤ v.val ∧ v.val < 13 ∧ (w.val < 6 ∨ w.val = 6 + (v.val - 6 + 1) % 7)) ∨
    (13 ≤ v.val ∧ v.val < 20 ∧ ((13 ≤ w.val ∧ w.val < v.val) ∨ (6 ≤ w.val ∧ v.val + w.val < 26))) at ha
  have hw5 : w.val = 5 := by
    by_contra hh
    have hwL : w ∈ L := Finset.mem_filter.mpr ⟨hwT, by omega⟩
    have hhmin := hmin w hwL
    omega
  simp only [Finset.mem_singleton]
  exact Fin.ext hw5

private theorem in833_oriented_has_parent
    (T : Finset (Fin 26)) (hne : T.Nonempty)
    (hs : ∀ v ∈ T, ∃ w ∈ T, digraph_oriented_cut20_sharp_example.Adj v w)
    (hlow : ∀ v ∈ T, ¬ v.val < 5) :
    ∃ p ∈ T, 6 ≤ p.val ∧ p.val < 13 := by
  have hnosink := in833_oriented_no_sinks T hs
  by_contra hn
  have hnoP : ∀ p ∈ T, ¬ (6 ≤ p.val ∧ p.val < 13) := by
    intro p hp hpP
    exact hn ⟨p, hp, hpP⟩
  have hR : (T.filter fun v => 13 ≤ v.val).Nonempty := by
    obtain ⟨v, hv⟩ := hne
    by_cases hvR : 13 ≤ v.val
    · exact ⟨v, Finset.mem_filter.mpr ⟨hv, hvR⟩⟩
    · have hvlow := hlow v hv
      have hvnosink := hnosink v hv
      have hvP := hnoP v hv
      have hvq : v.val = 5 := by omega
      obtain ⟨w, hw, ha⟩ := hs v hv
      change (v.val < 5 ∧ (w.val < v.val ∨ w.val = 5 ∨ (20 ≤ w.val ∧ v.val + w.val < 26))) ∨
        (v.val = 5 ∧ 13 ≤ w.val ∧ w.val < 20) ∨
        (6 ≤ v.val ∧ v.val < 13 ∧ (w.val < 6 ∨ w.val = 6 + (v.val - 6 + 1) % 7)) ∨
        (13 ≤ v.val ∧ v.val < 20 ∧ ((13 ≤ w.val ∧ w.val < v.val) ∨ (6 ≤ w.val ∧ v.val + w.val < 26))) at ha
      exact ⟨w, Finset.mem_filter.mpr ⟨hw, by omega⟩⟩
  let R := T.filter fun v => 13 ≤ v.val
  let r := R.min' hR
  have hrR : r ∈ R := Finset.min'_mem R hR
  have hrT : r ∈ T := (Finset.mem_filter.mp hrR).1
  have hr13 : 13 ≤ r.val := (Finset.mem_filter.mp hrR).2
  have hr20 := hnosink r hrT
  obtain ⟨w, hwT, ha⟩ := hs r hrT
  have hnoPw := hnoP w hwT
  change (r.val < 5 ∧ (w.val < r.val ∨ w.val = 5 ∨ (20 ≤ w.val ∧ r.val + w.val < 26))) ∨
    (r.val = 5 ∧ 13 ≤ w.val ∧ w.val < 20) ∨
    (6 ≤ r.val ∧ r.val < 13 ∧ (w.val < 6 ∨ w.val = 6 + (r.val - 6 + 1) % 7)) ∨
    (13 ≤ r.val ∧ r.val < 20 ∧ ((13 ≤ w.val ∧ w.val < r.val) ∨ (6 ≤ w.val ∧ r.val + w.val < 26))) at ha
  have hwR : w ∈ R := Finset.mem_filter.mpr ⟨hwT, by omega⟩
  have hwmin : r.val ≤ w.val := Finset.min'_le R w hwR
  omega

private theorem in833_oriented_cycle_successor {α : Type} [DecidableEq α]
    (D : Digraph α) (C : Finset α) (hC : digraph_directed_cycle_on D C) :
    C.Nonempty ∧ ∀ v ∈ C, ∃ w ∈ C, D.Adj v w := by
  obtain ⟨l, hnodup, hlen, hset, hchain, a, b, hhead, hlast, hclose⟩ := hC
  have ha : a ∈ l := by
    cases l with
    | nil => simp at hhead
    | cons x xs =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst a
      simp
  have haC : a ∈ C := by rw [← hset, List.mem_toFinset]; exact ha
  refine ⟨⟨a, haC⟩, ?_⟩
  intro v hv
  have hvL : v ∈ l := by rw [← hset, List.mem_toFinset] at hv; exact hv
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hvL
  by_cases his : i + 1 < l.length
  · refine ⟨l[i+1], ?_, ?_⟩
    · rw [← hset, List.mem_toFinset]
      exact List.getElem_mem _
    · rw [← heq]
      exact hchain.getElem i his
  · have hilast : i = l.length - 1 := by omega
    have hidx : l[i]? = some b := by
      simpa [List.getLast?_eq_getElem?, ← hilast] using hlast
    have heqB : l[i] = b := by simpa [List.getElem?_eq_getElem hi] using hidx
    refine ⟨a, haC, ?_⟩
    rw [← heq, heqB]
    exact hclose


private def in833_oriented_next (p : Fin 26) : Fin 26 :=
  ⟨6 + (p.val - 6 + 1) % 7, by have := Nat.mod_lt (p.val - 6 + 1) (by decide : 0 < 7); omega⟩

private theorem in833_oriented_parent_neighbors
    (T : Finset (Fin 26))
    (hlow : ∀ v ∈ T, ¬ v.val < 5)
    (p : Fin 26) (hp6 : 6 ≤ p.val) (hp13 : p.val < 13) :
    (T.filter fun w => digraph_oriented_cut20_sharp_example.Adj p w) ⊆ {5, in833_oriented_next p} := by
  intro w hw
  obtain ⟨hwT, ha⟩ := Finset.mem_filter.mp hw
  have hwlow := hlow w hwT
  change (p.val < 5 ∧ (w.val < p.val ∨ w.val = 5 ∨ (20 ≤ w.val ∧ p.val + w.val < 26))) ∨
    (p.val = 5 ∧ 13 ≤ w.val ∧ w.val < 20) ∨
    (6 ≤ p.val ∧ p.val < 13 ∧ (w.val < 6 ∨ w.val = 6 + (p.val - 6 + 1) % 7)) ∨
    (13 ≤ p.val ∧ p.val < 20 ∧ ((13 ≤ w.val ∧ w.val < p.val) ∨ (6 ≤ w.val ∧ p.val + w.val < 26))) at ha
  have hval : w.val = 5 ∨ w.val = (in833_oriented_next p).val := by
    change w.val = 5 ∨ w.val = 6 + (p.val - 6 + 1) % 7
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hval with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

private theorem in833_oriented_cycle_of_parents
    (T : Finset (Fin 26))
    (hstep : ∀ p ∈ T, 6 ≤ p.val → p.val < 13 → in833_oriented_next p ∈ T)
    (hex : ∃ p ∈ T, 6 ≤ p.val ∧ p.val < 13) :
    ∀ p : Fin 26, 6 ≤ p.val → p.val < 13 → p ∈ T := by
  have h67 : (6 : Fin 26) ∈ T → (7 : Fin 26) ∈ T := by
    intro h
    simpa [in833_oriented_next] using hstep 6 h (by decide) (by decide)
  have h78 : (7 : Fin 26) ∈ T → (8 : Fin 26) ∈ T := by
    intro h
    simpa [in833_oriented_next] using hstep 7 h (by decide) (by decide)
  have h89 : (8 : Fin 26) ∈ T → (9 : Fin 26) ∈ T := by
    intro h
    simpa [in833_oriented_next] using hstep 8 h (by decide) (by decide)
  have h910 : (9 : Fin 26) ∈ T → (10 : Fin 26) ∈ T := by
    intro h
    simpa [in833_oriented_next] using hstep 9 h (by decide) (by decide)
  have h1011 : (10 : Fin 26) ∈ T → (11 : Fin 26) ∈ T := by
    intro h
    simpa [in833_oriented_next] using hstep 10 h (by decide) (by decide)
  have h1112 : (11 : Fin 26) ∈ T → (12 : Fin 26) ∈ T := by
    intro h
    simpa [in833_oriented_next] using hstep 11 h (by decide) (by decide)
  have h126 : (12 : Fin 26) ∈ T → (6 : Fin 26) ∈ T := by
    intro h
    simpa [in833_oriented_next] using hstep 12 h (by decide) (by decide)
  obtain ⟨p, hp, hp6, hp13⟩ := hex
  have hp6T : (6 : Fin 26) ∈ T := by
    fin_cases p <;> (try norm_num at hp6) <;> (try norm_num at hp13) <;> aesop
  have hp7T := h67 hp6T
  have hp8T := h78 hp7T
  have hp9T := h89 hp8T
  have hp10T := h910 hp9T
  have hp11T := h1011 hp10T
  have hp12T := h1112 hp11T
  intro p hp6 hp13
  fin_cases p <;> (try norm_num at hp6) <;> (try norm_num at hp13) <;> assumption

private theorem in833_oriented_every_successor_set_hits_parent
    (T : Finset (Fin 26)) (hne : T.Nonempty)
    (hs : ∀ v ∈ T, ∃ w ∈ T, digraph_oriented_cut20_sharp_example.Adj v w) :
    ∃ p ∈ T, 6 ≤ p.val ∧ p.val < 13 := by
  have hnosink := in833_oriented_no_sinks T hs
  by_contra hn
  have hnoP : ∀ p ∈ T, ¬ (6 ≤ p.val ∧ p.val < 13) := by
    intro p hp hpP
    exact hn ⟨p, hp, hpP⟩
  have hnoR : ∀ r ∈ T, ¬ 13 ≤ r.val := by
    intro r hr hrR
    let R := T.filter fun v => 13 ≤ v.val
    have hR : R.Nonempty := ⟨r, Finset.mem_filter.mpr ⟨hr, hrR⟩⟩
    let x := R.min' hR
    have hxR : x ∈ R := Finset.min'_mem R hR
    have hxT : x ∈ T := (Finset.mem_filter.mp hxR).1
    have hx13 : 13 ≤ x.val := (Finset.mem_filter.mp hxR).2
    have hx20 := hnosink x hxT
    obtain ⟨w, hwT, ha⟩ := hs x hxT
    have hnoPw := hnoP w hwT
    change (x.val < 5 ∧ (w.val < x.val ∨ w.val = 5 ∨ (20 ≤ w.val ∧ x.val + w.val < 26))) ∨
      (x.val = 5 ∧ 13 ≤ w.val ∧ w.val < 20) ∨
      (6 ≤ x.val ∧ x.val < 13 ∧ (w.val < 6 ∨ w.val = 6 + (x.val - 6 + 1) % 7)) ∨
      (13 ≤ x.val ∧ x.val < 20 ∧ ((13 ≤ w.val ∧ w.val < x.val) ∨ (6 ≤ w.val ∧ x.val + w.val < 26))) at ha
    have hwR : w ∈ R := Finset.mem_filter.mpr ⟨hwT, by omega⟩
    have hwmin : x.val ≤ w.val := Finset.min'_le R w hwR
    omega
  have hq : (5 : Fin 26) ∉ T := by
    intro hqT
    obtain ⟨w, hw, ha⟩ := hs 5 hqT
    have hwnR := hnoR w hw
    change ((5 : Fin 26).val < 5 ∧ (w.val < (5 : Fin 26).val ∨ w.val = 5 ∨ (20 ≤ w.val ∧ (5 : Fin 26).val + w.val < 26))) ∨
      ((5 : Fin 26).val = 5 ∧ 13 ≤ w.val ∧ w.val < 20) ∨
      (6 ≤ (5 : Fin 26).val ∧ (5 : Fin 26).val < 13 ∧ (w.val < 6 ∨ w.val = 6 + ((5 : Fin 26).val - 6 + 1) % 7)) ∨
      (13 ≤ (5 : Fin 26).val ∧ (5 : Fin 26).val < 20 ∧ ((13 ≤ w.val ∧ w.val < (5 : Fin 26).val) ∨ (6 ≤ w.val ∧ (5 : Fin 26).val + w.val < 26))) at ha
    omega
  have hlow : ∀ v ∈ T, ¬ v.val < 5 := by
    intro v hv hv5
    obtain ⟨x, hx, hx5, hsub⟩ := in833_oriented_low_witness T hnosink ⟨v, hv, hv5⟩
    obtain ⟨w, hwT, ha⟩ := hs x hx
    have hwq : w ∈ ({5} : Finset (Fin 26)) := hsub (Finset.mem_filter.mpr ⟨hwT, ha⟩)
    have : w = 5 := by simpa using hwq
    subst w
    exact hq hwT
  obtain ⟨v, hv⟩ := hne
  have hvlo := hlow v hv
  have hvP := hnoP v hv
  have hvR := hnoR v hv
  have hv20 := hnosink v hv
  have hvq : v.val = 5 := by omega
  apply hq
  have : v = 5 := Fin.ext hvq
  simpa [this] using hv

private theorem in833_oriented_low_free_of_avoid_target
    (T : Finset (Fin 26))
    (hs : ∀ v ∈ T, ∃ w ∈ T, digraph_oriented_cut20_sharp_example.Adj v w)
    (hq : (5 : Fin 26) ∉ T) :
    ∀ v ∈ T, ¬ v.val < 5 := by
  intro v hv hv5
  have hnosink := in833_oriented_no_sinks T hs
  obtain ⟨x, hx, hx5, hsub⟩ := in833_oriented_low_witness T hnosink ⟨v, hv, hv5⟩
  obtain ⟨w, hw, ha⟩ := hs x hx
  have hwq : w ∈ ({5} : Finset (Fin 26)) := hsub (Finset.mem_filter.mpr ⟨hw, ha⟩)
  have : w = 5 := by simpa using hwq
  subst w
  exact hq hw

private theorem in833_oriented_cycle_avoids_target_contains_parents
    (C : Finset (Fin 26)) (hc : digraph_directed_cycle_on digraph_oriented_cut20_sharp_example C)
    (hq : (5 : Fin 26) ∉ C) :
    ∀ p : Fin 26, 6 ≤ p.val → p.val < 13 → p ∈ C := by
  obtain ⟨hne, hs⟩ := in833_oriented_cycle_successor digraph_oriented_cut20_sharp_example C hc
  have hlow := in833_oriented_low_free_of_avoid_target C hs hq
  have hex := in833_oriented_every_successor_set_hits_parent C hne hs
  apply in833_oriented_cycle_of_parents C _ hex
  intro p hp hp6 hp13
  obtain ⟨w, hw, ha⟩ := hs p hp
  have hm := in833_oriented_parent_neighbors C hlow p hp6 hp13
    (Finset.mem_filter.mpr ⟨hw, ha⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h
  · subst w
    exact False.elim (hq hw)
  · simpa [h] using hw

private theorem in833_oriented_no_two :
    ¬ ∃ c : Fin 2 → Finset (Fin 26),
      (∀ i, digraph_directed_cycle_on digraph_oriented_cut20_sharp_example (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j)) := by
  rintro ⟨c, hc, hd⟩
  have hd01 : Disjoint (c 0) (c 1) := hd (by decide)
  by_cases hq : (5 : Fin 26) ∈ c 0
  · have hq1 : (5 : Fin 26) ∉ c 1 := (Finset.disjoint_left.mp hd01) hq
    have hall := in833_oriented_cycle_avoids_target_contains_parents (c 1) (hc 1) hq1
    obtain ⟨hne, hs⟩ := in833_oriented_cycle_successor digraph_oriented_cut20_sharp_example (c 0) (hc 0)
    obtain ⟨p, hp, hp6, hp13⟩ := in833_oriented_every_successor_set_hits_parent (c 0) hne hs
    exact (Finset.disjoint_left.mp hd01) hp (hall p hp6 hp13)
  · have hall := in833_oriented_cycle_avoids_target_contains_parents (c 0) (hc 0) hq
    obtain ⟨hne, hs⟩ := in833_oriented_cycle_successor digraph_oriented_cut20_sharp_example (c 1) (hc 1)
    obtain ⟨p, hp, hp6, hp13⟩ := in833_oriented_every_successor_set_hits_parent (c 1) hne hs
    exact (Finset.disjoint_left.mp hd01) (hall p hp6 hp13) hp

private theorem in833_oriented_robust
    (T : Finset (Fin 26)) (hne : T.Nonempty)
    (hmin : ∀ v ∈ T, 2 ≤ (T.filter fun w => digraph_oriented_cut20_sharp_example.Adj v w).card) :
    3 ≤ (T.filter fun v => (T.filter fun w => digraph_oriented_cut20_sharp_example.Adj v w).card < 3).card := by
  have hs : ∀ v ∈ T, ∃ w ∈ T, digraph_oriented_cut20_sharp_example.Adj v w := by
    intro v hv
    have hp : 0 < (T.filter fun w => digraph_oriented_cut20_sharp_example.Adj v w).card := by have := hmin v hv; omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hp
    exact ⟨w, (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩
  have hnosink := in833_oriented_no_sinks T hs
  have hlow : ∀ v ∈ T, ¬ v.val < 5 := by
    intro v hv hv5
    obtain ⟨x, hx, hx5, hsub⟩ := in833_oriented_low_witness T hnosink ⟨v, hv, hv5⟩
    have hcard := Finset.card_le_card hsub
    have hminx := hmin x hx
    simp only [Finset.card_singleton] at hcard
    omega
  have hex := in833_oriented_every_successor_set_hits_parent T hne hs
  have hstep : ∀ p ∈ T, 6 ≤ p.val → p.val < 13 → in833_oriented_next p ∈ T := by
    intro p hp hp6 hp13
    by_contra hn
    have hsub : (T.filter fun w => digraph_oriented_cut20_sharp_example.Adj p w) ⊆ ({5} : Finset (Fin 26)) := by
      intro w hw
      have hpairs := in833_oriented_parent_neighbors T hlow p hp6 hp13 hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpairs
      rcases hpairs with h | h
      · simpa using h
      · have hwT := (Finset.mem_filter.mp hw).1
        exact False.elim (hn (by simpa [h] using hwT))
    have hcard := Finset.card_le_card hsub
    have hminp := hmin p hp
    simp only [Finset.card_singleton] at hcard
    omega
  have hall := in833_oriented_cycle_of_parents T hstep hex
  let P : Finset (Fin 26) := Finset.univ.filter fun p => 6 ≤ p.val ∧ p.val < 13
  have hP : P ⊆ T.filter fun v => (T.filter fun w => digraph_oriented_cut20_sharp_example.Adj v w).card < 3 := by
    intro p hp
    have hpval := (Finset.mem_filter.mp hp).2
    have hpT := hall p hpval.1 hpval.2
    have hsub := in833_oriented_parent_neighbors T hlow p hpval.1 hpval.2
    have hcard := Finset.card_le_card hsub
    have hpair : ({5, in833_oriented_next p} : Finset (Fin 26)).card ≤ 2 := Finset.card_le_two
    exact Finset.mem_filter.mpr ⟨hpT, by omega⟩
  have hPcard : P.card = 7 := by decide
  have hle := Finset.card_le_card hP
  omega

theorem digraph_oriented_cut20_sharp_example_certificate :
    let D := digraph_oriented_cut20_sharp_example
    let B : Finset (Fin 26) := Finset.univ.filter fun v => v.val < 20
    (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
    (∀ v ∈ B, (Finset.univ.filter fun w => D.Adj v w).card = 7) ∧
    (∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card) = 20 ∧
    (¬ ∃ c : Fin 2 → Finset (Fin 26), (∀ i, digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j))) ∧
    (∀ T : Finset (Fin 26), T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      3 ≤ (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card) := by
  exact ⟨in833_oriented_cut20_orientation, in833_oriented_cut20_degree,
    in833_oriented_cut20_boundary, in833_oriented_no_two, in833_oriented_robust⟩
