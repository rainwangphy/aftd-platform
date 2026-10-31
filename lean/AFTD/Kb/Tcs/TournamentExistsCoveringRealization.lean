import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphInvert
import AFTD.Kb.Tcs.DigraphOutCount
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_exists_covering_realization

Topic: graphs   Node: 31987b236484

Provenance: formalization of a published result. Source: arXiv:2610.40521 Lemma 6

Let d be a realizable degree vector of an n-vertex tournament, and let v, w be vertices satisfying d v < d w. Then there exists a tournament T realizing d in which w covers v (that is, w -> v and w -> x for every out-neighbor x of v).
-/

theorem tecx_invert_tournament {n : ℕ} (T : Digraph (Fin n)) (hT : digraph_is_tournament T)
    (X : Set (Fin n)) : digraph_is_tournament (digraph_invert T X) := by
  refine ⟨fun x h => ?_, fun x y hxy => ?_⟩
  · rcases h with ⟨-, -, h⟩ | ⟨-, h⟩ <;> exact hT.1 x h
  · have h1 := hT.2 x y hxy
    have h2 := hT.2 y x hxy.symm
    simp only [digraph_invert]
    by_cases hx : x ∈ X <;> by_cases hy : y ∈ X <;> simp [hx, hy] <;> tauto

open Classical in
theorem tecx_first {n : ℕ} (T : Digraph (Fin n)) (hT : digraph_is_tournament T) (a b c : Fin n)
    (hab : T.Adj a b) (hbc : T.Adj b c) (hca : T.Adj c a) :
    (Finset.univ.filter (fun y => (digraph_invert T {a, b, c}).Adj a y)).card =
      (Finset.univ.filter (fun y => T.Adj a y)).card := by
  have hne_ab : a ≠ b := fun h => hT.1 a (h ▸ hab)
  have hne_bc : b ≠ c := fun h => hT.1 b (h ▸ hbc)
  have hne_ca : c ≠ a := fun h => hT.1 c (h ▸ hca)
  have hba : ¬ T.Adj b a := (hT.2 a b hne_ab).1 hab
  have hac : ¬ T.Adj a c := (hT.2 c a hne_ca).1 hca
  have hirr := hT.1
  have e : Finset.univ.filter (fun y => (digraph_invert T {a, b, c}).Adj a y) =
      insert c ((Finset.univ.filter (fun y => T.Adj a y)).erase b) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase,
      digraph_invert, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h1 : y = a
    · subst h1; simp [hirr, hne_ca.symm]
    by_cases h2 : y = b
    · subst h2; simp [hba, hne_bc]
    by_cases h3 : y = c
    · subst h3; simp [hca]
    simp [h1, h2, h3]
  rw [e, Finset.card_insert_of_notMem (by simp [hac]), Finset.card_erase_of_mem (by simp [hab])]
  have : 0 < (Finset.univ.filter (fun y => T.Adj a y)).card :=
    Finset.card_pos.2 ⟨b, by simp [hab]⟩
  omega

open Classical in
theorem tecx_flip {n : ℕ} (T : Digraph (Fin n)) (hT : digraph_is_tournament T) (a b c : Fin n)
    (hab : T.Adj a b) (hbc : T.Adj b c) (hca : T.Adj c a) :
    digraph_is_tournament (digraph_invert T {a, b, c}) ∧
      ∀ i, digraph_out_count (digraph_invert T {a, b, c}) i = digraph_out_count T i := by
  refine ⟨tecx_invert_tournament T hT _, fun i => ?_⟩
  unfold digraph_out_count
  by_cases hia : i = a
  · subst hia; exact tecx_first T hT i b c hab hbc hca
  by_cases hib : i = b
  · subst hib
    have hs : ({a, i, c} : Set (Fin n)) = {i, c, a} := by ext; simp; tauto
    rw [hs]; exact tecx_first T hT i c a hbc hca hab
  by_cases hic : i = c
  · subst hic
    have hs : ({a, b, i} : Set (Fin n)) = {i, a, b} := by ext; simp; tauto
    rw [hs]; exact tecx_first T hT i a b hca hab hbc
  congr 1
  ext y
  simp [digraph_invert, hia, hib, hic]

theorem tecx_adj_out {n : ℕ} (T : Digraph (Fin n)) (X : Set (Fin n)) {u y : Fin n} (hu : u ∉ X) :
    (digraph_invert T X).Adj u y ↔ T.Adj u y := by
  simp only [digraph_invert]; tauto

theorem tecx_adj_out' {n : ℕ} (T : Digraph (Fin n)) (X : Set (Fin n)) {u y : Fin n} (hy : y ∉ X) :
    (digraph_invert T X).Adj u y ↔ T.Adj u y := by
  simp only [digraph_invert]; tauto

theorem tecx_adj_in {n : ℕ} (T : Digraph (Fin n)) (X : Set (Fin n)) {u y : Fin n} (hu : u ∈ X)
    (hy : y ∈ X) : (digraph_invert T X).Adj u y ↔ T.Adj y u := by
  simp only [digraph_invert]; tauto

open Classical in
/-- For any realizable degree vector d and vertices v, w with d(v) < d(w), there is a realization of d where w covers v. -/
theorem tournament_exists_covering_realization {n : ℕ} (d : Fin n → ℕ)
    (hd : ∃ T : Digraph (Fin n), digraph_is_tournament T ∧ ∀ i : Fin n, digraph_out_count T i = d i)
    (v w : Fin n) (hvw : d v < d w) :
    ∃ T : Digraph (Fin n), (digraph_is_tournament T ∧ ∀ i : Fin n, digraph_out_count T i = d i) ∧
      (T.Adj w v ∧ ∀ x, T.Adj v x → T.Adj w x) := by
  obtain ⟨T0, hT0⟩ := hd
  have hvw' : v ≠ w := fun h => by rw [h] at hvw; exact lt_irrefl _ hvw
  let μ : Digraph (Fin n) → ℕ := fun T =>
    (Finset.univ.filter (fun x => T.Adj v x ∧ ¬ T.Adj w x)).card + (if T.Adj v w then 1 else 0)
  suffices H : ∀ k, ∀ T : Digraph (Fin n),
      (digraph_is_tournament T ∧ ∀ i : Fin n, digraph_out_count T i = d i) → μ T = k →
      ∃ T : Digraph (Fin n), (digraph_is_tournament T ∧ ∀ i : Fin n, digraph_out_count T i = d i) ∧
        (T.Adj w v ∧ ∀ x, T.Adj v x → T.Adj w x) from H _ T0 hT0 rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro T hT hk
  obtain ⟨hTt, hTd⟩ := hT
  by_cases hA : ∀ x, ¬ (T.Adj v x ∧ ¬ T.Adj w x)
  · refine ⟨T, ⟨hTt, hTd⟩, ?_, fun x hx => ?_⟩
    · have : ¬ T.Adj v w := fun h => hA w ⟨h, hTt.1 w⟩
      exact (hTt.2 w v hvw'.symm).2 this
    · by_contra h; exact hA x ⟨hx, h⟩
  push Not at hA
  obtain ⟨x0, hvx0, hwx0⟩ := hA
  have hx0A : x0 ∈ Finset.univ.filter (fun x => T.Adj v x ∧ ¬ T.Adj w x) := by simp [hvx0, hwx0]
  have hcount : (Finset.univ.filter (fun x => T.Adj v x ∧ ¬ T.Adj w x)).card <
      (Finset.univ.filter (fun x => T.Adj w x ∧ ¬ T.Adj v x)).card := by
    have hv := hTd v
    have hw := hTd w
    unfold digraph_out_count at hv hw
    have e1 := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun y => T.Adj v y)) (fun y => T.Adj w y)
    have e2 := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun y => T.Adj w y)) (fun y => T.Adj v y)
    simp only [Finset.filter_filter] at e1 e2
    have e3 : (Finset.univ.filter (fun y => T.Adj v y ∧ T.Adj w y)) =
        Finset.univ.filter (fun y => T.Adj w y ∧ T.Adj v y) := by
      ext y; simp [and_comm]
    rw [e3] at e1
    omega
  obtain ⟨z, hzB, hzv⟩ := Finset.exists_mem_ne
    (s := Finset.univ.filter (fun x => T.Adj w x ∧ ¬ T.Adj v x))
    (by have := Finset.card_pos.2 ⟨x0, hx0A⟩; omega) v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzB
  obtain ⟨hwz, hvz⟩ := hzB
  have hzv' : T.Adj z v := (hTt.2 z v hzv).2 hvz
  have hzw : z ≠ w := fun h => hTt.1 w (h ▸ hwz)
  have hlt : ∃ T', (digraph_is_tournament T' ∧ ∀ i : Fin n, digraph_out_count T' i = d i) ∧
      μ T' < μ T := by
    by_cases hx1 : ∃ x, T.Adj v x ∧ ¬ T.Adj w x ∧ x ≠ w
    · obtain ⟨x, hvx, hwx, hxw⟩ := hx1
      have hxv : x ≠ v := fun h => hTt.1 v (h ▸ hvx)
      have hxz : x ≠ z := fun h => hvz (h ▸ hvx)
      have hxw' : T.Adj x w := (hTt.2 x w hxw).2 hwx
      have hxA : x ∈ Finset.univ.filter (fun x => T.Adj v x ∧ ¬ T.Adj w x) := by simp [hvx, hwx]
      by_cases hzx : T.Adj z x
      · -- reverse the cycle w → z → x → w
        obtain ⟨h1, h2⟩ := tecx_flip T hTt w z x hwz hzx hxw'
        refine ⟨_, ⟨h1, fun i => (h2 i).trans (hTd i)⟩, ?_⟩
        have hvX : v ∉ ({w, z, x} : Set (Fin n)) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; push Not
          exact ⟨hvw', hzv.symm, hxv.symm⟩
        have hsub : Finset.univ.filter (fun y => (digraph_invert T {w, z, x}).Adj v y ∧
            ¬ (digraph_invert T {w, z, x}).Adj w y) ⊆
            (Finset.univ.filter (fun x => T.Adj v x ∧ ¬ T.Adj w x)).erase x := by
          intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, tecx_adj_out T _ hvX] at hy
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
          have hwX : w ∈ ({w, z, x} : Set (Fin n)) := by simp
          by_cases hyx : y = x
          · subst hyx
            exact absurd ((tecx_adj_in T _ hwX (by simp)).2 hxw') hy.2
          by_cases hyz : y = z
          · subst hyz; exact absurd hy.1 hvz
          by_cases hyw : y = w
          · subst hyw; exact ⟨hyx, hy.1, hTt.1 _⟩
          have hyX : y ∉ ({w, z, x} : Set (Fin n)) := by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; push Not; exact ⟨hyw, hyz, hyx⟩
          exact ⟨hyx, hy.1, fun h => hy.2 ((tecx_adj_out' T _ hyX).2 h)⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hxA] at hc
        have hpos := Finset.card_pos.2 ⟨x, hxA⟩
        have hind : (digraph_invert T {w, z, x}).Adj v w ↔ T.Adj v w := tecx_adj_out T _ hvX
        simp only [μ, hind]
        omega
      · -- reverse the cycle v → x → z → v
        have hxz' : T.Adj x z := (hTt.2 x z hxz).2 hzx
        obtain ⟨h1, h2⟩ := tecx_flip T hTt v x z hvx hxz' hzv'
        refine ⟨_, ⟨h1, fun i => (h2 i).trans (hTd i)⟩, ?_⟩
        have hwX : w ∉ ({v, x, z} : Set (Fin n)) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; push Not
          exact ⟨hvw'.symm, fun h => hxw h.symm, hzw.symm⟩
        have hvX : v ∈ ({v, x, z} : Set (Fin n)) := by simp
        have hsub : Finset.univ.filter (fun y => (digraph_invert T {v, x, z}).Adj v y ∧
            ¬ (digraph_invert T {v, x, z}).Adj w y) ⊆
            (Finset.univ.filter (fun x => T.Adj v x ∧ ¬ T.Adj w x)).erase x := by
          intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, tecx_adj_out T _ hwX] at hy
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hyx : y = x
          · subst hyx
            exact absurd ((tecx_adj_in T _ hvX (by simp)).1 hy.1) ((hTt.2 v y hxv.symm).1 hvx)
          by_cases hyz : y = z
          · subst hyz; exact absurd hwz hy.2
          by_cases hyv : y = v
          · subst hyv; exact absurd hy.1 ((tecx_invert_tournament T hTt _).1 y)
          have hyX : y ∉ ({v, x, z} : Set (Fin n)) := by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; push Not; exact ⟨hyv, hyx, hyz⟩
          exact ⟨hyx, (tecx_adj_out' T _ hyX).1 hy.1, hy.2⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hxA] at hc
        have hpos := Finset.card_pos.2 ⟨x, hxA⟩
        have hind : (digraph_invert T {v, x, z}).Adj v w ↔ T.Adj v w := tecx_adj_out' T _ hwX
        simp only [μ, hind]
        omega
    · push Not at hx1
      have hvw2 : T.Adj v w := by
        have := hx1 x0 hvx0 hwx0; rw [← this]; exact hvx0
      -- reverse the cycle v → w → z → v
      obtain ⟨h1, h2⟩ := tecx_flip T hTt v w z hvw2 hwz hzv'
      refine ⟨_, ⟨h1, fun i => (h2 i).trans (hTd i)⟩, ?_⟩
      have hvX : v ∈ ({v, w, z} : Set (Fin n)) := by simp
      have hwX : w ∈ ({v, w, z} : Set (Fin n)) := by simp
      have hsub : Finset.univ.filter (fun y => (digraph_invert T {v, w, z}).Adj v y ∧
          ¬ (digraph_invert T {v, w, z}).Adj w y) ⊆ {z} := by
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        simp only [Finset.mem_singleton]
        by_contra hyz
        by_cases hyv : y = v
        · subst hyv; exact absurd hy.1 ((tecx_invert_tournament T hTt _).1 y)
        by_cases hyw : y = w
        · subst hyw
          exact absurd ((tecx_adj_in T _ hvX hwX).1 hy.1) ((hTt.2 v y hvw').1 hvw2)
        have hyX : y ∉ ({v, w, z} : Set (Fin n)) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; push Not; exact ⟨hyv, hyw, hyz⟩
        exact hyw (hx1 y ((tecx_adj_out' T _ hyX).1 hy.1)
          (fun h => hy.2 ((tecx_adj_out' T _ hyX).2 h)))
      have hc := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hc
      have hpos := Finset.card_pos.2 ⟨x0, hx0A⟩
      have hind : ¬ (digraph_invert T {v, w, z}).Adj v w := fun h =>
        (hTt.2 v w hvw').1 hvw2 ((tecx_adj_in T _ hvX hwX).1 h)
      simp only [μ, hind, hvw2, if_true, if_false]
      omega
  obtain ⟨T', hT', hlt'⟩ := hlt
  exact ih (μ T') (hk ▸ hlt') T' hT' rfl
