import AFTD.Prelude
import AFTD.Kb.Physics.HardCoreVarSize
import AFTD.Kb.Physics.Lift20PolyVariancePerVertex

/-!
# petersen_lift20_graph_exists

Topic: statistical_mechanics   Node: 93f9a653aab4

Provenance: helper lemma. step towards op_1354_triangle_free_cubic_petersen_variance_crossover

There exists a 20-vertex simple graph G (the Petersen 2-lift / dodecahedron) with decidable adjacency which is 3-regular, triangle-free, and whose per-vertex hard-core variance equals lift20_poly_variance_per_vertex x for all activities x.
-/

def in1189_adjB (a b : Fin 20) : Bool :=
  (a.val < 10 && b.val < 10 && ((a.val + 1) % 10 == b.val || (b.val + 1) % 10 == a.val)) ||
  (a.val < 10 && b.val == a.val + 10) || (b.val < 10 && a.val == b.val + 10) ||
  (10 ≤ a.val && 10 ≤ b.val &&
    ((a.val - 10 + 2) % 10 == b.val - 10 || (b.val - 10 + 2) % 10 == a.val - 10))

def in1189_G : SimpleGraph (Fin 20) where
  Adj a b := in1189_adjB a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance in1189_inst : DecidableRel in1189_G.Adj := fun a b =>
  inferInstanceAs (Decidable (in1189_adjB a b = true))

/-- number of independent `k`-subsets of the list `l` (fuel-bounded include/exclude recursion) -/
def in1189_cnt {V : Type*} (adj : V → V → Bool) : ℕ → List V → ℕ → ℕ
  | 0, _, k => if k = 0 then 1 else 0
  | _ + 1, [], k => if k = 0 then 1 else 0
  | f + 1, v :: rest, k => in1189_cnt adj f rest k +
      (match k with
        | 0 => 0
        | k + 1 => in1189_cnt adj f (rest.filter (fun w => !adj v w)) k)

theorem in1189_nil {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    ((∅ : Finset V).powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V) ∧ I.card = k)).card
      = if k = 0 then 1 else 0 := by
  classical
  rw [Finset.powerset_empty]
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl, Finset.filter_singleton, if_pos ⟨by simp, rfl⟩, Finset.card_singleton]
  · rw [if_neg hk, Finset.filter_singleton, if_neg (by rintro ⟨-, h⟩; exact hk (by simpa using h.symm)),
      Finset.card_empty]

theorem in1189_cnt_sound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (adj : V → V → Bool)
    (hadj : ∀ a b, G.Adj a b ↔ adj a b = true) :
    ∀ (f : ℕ) (l : List V), l.length ≤ f → l.Nodup → ∀ k,
      in1189_cnt adj f l k = (l.toFinset.powerset.filter
        (fun I : Finset V => G.IsIndepSet (I : Set V) ∧ I.card = k)).card := by
  classical
  intro f
  induction f with
  | zero =>
    intro l hl _ k
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [in1189_cnt.eq_1, List.toFinset_nil, in1189_nil]
  | succ f ih =>
    intro l hl hnd k
    cases l with
    | nil => rw [in1189_cnt.eq_2, List.toFinset_nil, in1189_nil]
    | cons v rest =>
      rw [List.nodup_cons] at hnd
      obtain ⟨hv, hnd⟩ := hnd
      simp only [List.length_cons] at hl
      set s := rest.toFinset with hs
      have hvs : v ∉ s := by rw [hs, List.mem_toFinset]; exact hv
      have key : in1189_cnt adj (f+1) (v :: rest) k = in1189_cnt adj f rest k +
          (match k with
            | 0 => 0
            | k + 1 => in1189_cnt adj f (rest.filter (fun w => !adj v w)) k) := by
        cases k <;> rfl
      rw [key, List.toFinset_cons, Finset.powerset_insert, Finset.filter_union,
        Finset.card_union_of_disjoint, ih rest (by omega) hnd k]
      · congr 1
        rw [Finset.filter_image]
        rw [Finset.card_image_of_injOn]
        · cases k with
          | zero =>
            dsimp only
            rw [eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro J _ h
            exact absurd h.2 (by rw [Finset.card_insert_of_notMem (fun hJ => hvs (by
              rename_i hJs; exact (Finset.mem_powerset.1 hJs) hJ))]; omega)
          | succ k =>
            dsimp only
            rw [ih (rest.filter (fun w => !adj v w)) (le_trans (List.length_filter_le _ _) (by omega))
              (hnd.filter _) k]
            congr 1
            ext J
            simp only [Finset.mem_filter, Finset.mem_powerset]
            constructor
            · rintro ⟨hJ, hind, hcard⟩
              have hJs : J ⊆ s := fun x hx => by
                have := hJ hx
                rw [List.mem_toFinset, List.mem_filter] at this
                rw [hs, List.mem_toFinset]; exact this.1
              have hJa : ∀ x ∈ J, adj v x = false := fun x hx => by
                have := hJ hx
                rw [List.mem_toFinset, List.mem_filter] at this
                simpa using this.2
              have hvJ : v ∉ J := fun h => hvs (hJs h)
              refine ⟨hJs, ?_, by rw [Finset.card_insert_of_notMem hvJ, hcard]⟩
              rw [Finset.coe_insert, SimpleGraph.isIndepSet_iff, Set.pairwise_insert]
              refine ⟨hind, fun x hx _ => ⟨fun h => ?_, fun h => ?_⟩⟩
              · have h' := (hadj v x).1 h
                simp [hJa x hx] at h'
              · have h' := (hadj v x).1 h.symm
                simp [hJa x hx] at h'
            · rintro ⟨hJs, hind, hcard⟩
              have hvJ : v ∉ J := fun h => hvs (hJs h)
              rw [Finset.coe_insert, SimpleGraph.isIndepSet_iff, Set.pairwise_insert] at hind
              rw [Finset.card_insert_of_notMem hvJ] at hcard
              refine ⟨fun x hx => ?_, by rw [SimpleGraph.isIndepSet_iff]; exact hind.1, by omega⟩
              rw [List.mem_toFinset, List.mem_filter]
              refine ⟨by rw [← List.mem_toFinset, ← hs]; exact hJs hx, ?_⟩
              have := (hind.2 x hx (fun h => hvJ (h ▸ hx))).1
              rw [hadj] at this
              simpa using this
        · intro J hJ J' hJ' he
          simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hJ hJ'
          have h1 : v ∉ J := fun h => hvs (hJ.1 h)
          have h2 : v ∉ J' := fun h => hvs (hJ'.1 h)
          rw [← Finset.erase_insert h1, ← Finset.erase_insert h2, he]
      · rw [Finset.disjoint_left]
        intro J hJ hJ'
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image] at hJ hJ'
        obtain ⟨⟨K, -, rfl⟩, -⟩ := hJ'
        exact hvs (hJ.1 (Finset.mem_insert_self _ _))

theorem in1189_counts : ∀ k : Fin 21, in1189_cnt in1189_adjB 20 (List.finRange 20) k.val =
    ![1, 20, 160, 660, 1510, 1912, 1240, 320, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] k := by
  decide +kernel

theorem in1189_card (k : ℕ) :
    ((Finset.univ.filter fun I : Finset (Fin 20) => in1189_G.IsIndepSet (I : Set (Fin 20))).filter
      (fun I => I.card = k)).card = in1189_cnt in1189_adjB 20 (List.finRange 20) k := by
  classical
  rw [in1189_cnt_sound in1189_G in1189_adjB (fun a b => Iff.rfl) 20 (List.finRange 20) (by simp)
    (List.nodup_finRange 20) k, Finset.filter_filter,
    show (List.finRange 20).toFinset = Finset.univ by ext; simp, Finset.powerset_univ]
  all_goals first | rfl | (congr 1) | simp

theorem in1189_sum (g : ℕ → ℝ) :
    ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin 20) => in1189_G.IsIndepSet (I : Set (Fin 20))),
      g I.card = ∑ k ∈ Finset.range 21, (in1189_cnt in1189_adjB 20 (List.finRange 20) k : ℝ) * g k := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.range 21)]
  · apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_congr rfl (fun I hI => by rw [(Finset.mem_filter.1 hI).2]), Finset.sum_const,
      nsmul_eq_mul, ← in1189_card k]
  · intro I _
    rw [Finset.mem_range]
    have := Finset.card_le_univ I
    rw [Fintype.card_fin] at this
    omega

/-- There exists a 20-vertex simple graph G with decidable adjacency which is 3-regular, triangle-free, and whose per-vertex hard-core variance equals lift20_poly_variance_per_vertex x for all activities x. -/
theorem petersen_lift20_graph_exists :
    ∃ (G : SimpleGraph (Fin 20)) (_ : DecidableRel G.Adj),
      G.IsRegularOfDegree 3 ∧ G.CliqueFree 3 ∧
      ∀ x : ℝ, hardCoreVarSize G (fun _ => x) / 20 = lift20_poly_variance_per_vertex x := by
  refine ⟨in1189_G, in1189_inst, ?_, ?_, ?_⟩
  · intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    revert v
    decide
  · intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.1 hs
    have notri : ∀ a b c : Fin 20, in1189_adjB a b = true → in1189_adjB a c = true →
        in1189_adjB b c = true → False := by decide
    exact notri a b c hab hac hbc
  · intro x
    have hc := in1189_counts
    have e0 : ∀ I : Finset (Fin 20), ∏ _v ∈ I, x = x ^ I.card := fun I => Finset.prod_const x
    simp only [hardCoreVarSize, lift20_poly_variance_per_vertex, e0]
    rw [in1189_sum (fun k => x ^ k), in1189_sum (fun k => x ^ k * (k : ℝ)),
      in1189_sum (fun k => x ^ k * ((k : ℝ) ^ 2))]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    have h := fun k : Fin 21 => hc k
    simp only [Fin.forall_fin_succ] at h
    simp only [show in1189_cnt in1189_adjB 20 (List.finRange 20) 0 = 1 from hc 0,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 1 = 20 from hc 1,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 2 = 160 from hc 2,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 3 = 660 from hc 3,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 4 = 1510 from hc 4,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 5 = 1912 from hc 5,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 6 = 1240 from hc 6,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 7 = 320 from hc 7,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 8 = 5 from hc 8,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 9 = 0 from hc 9,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 10 = 0 from hc 10,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 11 = 0 from hc 11,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 12 = 0 from hc 12,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 13 = 0 from hc 13,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 14 = 0 from hc 14,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 15 = 0 from hc 15,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 16 = 0 from hc 16,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 17 = 0 from hc 17,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 18 = 0 from hc 18,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 19 = 0 from hc 19,
      show in1189_cnt in1189_adjB 20 (List.finRange 20) 20 = 0 from hc 20]
    congr 1
    all_goals ring_nf
