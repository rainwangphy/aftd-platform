import AFTD.Prelude
import AFTD.Kb.Tcs.ForestCarpoolFinalDiscrepancy
import AFTD.Kb.Tcs.CarpoolStep
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.CarpoolDiscrepancies
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans
import AFTD.Kb.Tcs.Bit

/-!
# forest_carpool_component_coin_locality

Topic: online_algorithms   Node: 6e497cd27d49

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

Two coin assignments that agree on every edge in the final connected component of a fixed vertex give the same final greedy discrepancy at that vertex.
-/

namespace ForestCarpoolLocal

/-- greedy bit -/
def gbit {n : ℕ} (d : Fin n → ℤ) (e : Fin n × Fin n) (c : Bool) : Bool :=
  if d e.1 < d e.2 then true else if d e.2 < d e.1 then false else c

/-- greedy fold -/
def G (n : ℕ) : List (Fin n × Fin n) → List Bool → (Fin n → ℤ) → (Fin n → ℤ)
  | [], _, d => d
  | _, [], d => d
  | e :: es, c :: cs, d => G n es cs (carpool_step n d e (gbit d e c))

theorem scan_eq (n : ℕ) (es : List (Fin n × Fin n)) (cs : List Bool) (d z : Fin n → ℤ) :
    ((es.zip (carpool_greedy_orientations.aux n es cs d)).scanl
      (fun d (e, b) => carpool_step n d e b) d).getLastD z = G n es cs d := by
  induction es generalizing cs d z with
  | nil => simp [carpool_greedy_orientations.aux, G]
  | cons e es ih =>
    cases cs with
    | nil => simp [carpool_greedy_orientations.aux, G]
    | cons c cs =>
      simp only [carpool_greedy_orientations.aux, List.zip_cons_cons, List.scanl_cons,
        List.getLastD_cons, G]
      rw [← ih cs _ d]
      rfl

theorem final_eq (n : ℕ) (edges : List (Fin n × Fin n)) (r : Fin edges.length → Bool) :
    forest_carpool_final_discrepancy n edges r = G n edges (List.ofFn r) (fun _ => 0) := by
  unfold forest_carpool_final_discrepancy carpool_discrepancies carpool_greedy_orientations
  exact scan_eq n edges (List.ofFn r) _ _

theorem local_step (n : ℕ) (Γ : SimpleGraph (Fin n)) (w : Fin n)
    (e : Fin n × Fin n) (he : e.1 = e.2 ∨ Γ.Adj e.1 e.2)
    (d d' : Fin n → ℤ) (c c' : Bool)
    (hd : ∀ x, Γ.Reachable w x → d x = d' x)
    (hc : Γ.Reachable w e.1 → c = c') :
    ∀ x, Γ.Reachable w x →
      carpool_step n d e (gbit d e c) x = carpool_step n d' e (gbit d' e c') x := by
  intro x hx
  by_cases h1 : Γ.Reachable w e.1
  · have h2 : Γ.Reachable w e.2 := by
      rcases he with h | h
      · rwa [← h]
      · exact h1.trans h.reachable
    have hb : gbit d e c = gbit d' e c' := by
      unfold gbit; rw [hd _ h1, hd _ h2, hc h1]
    unfold carpool_step; rw [hb, hd x hx]
  · have h2 : ¬ Γ.Reachable w e.2 := by
      intro h2; apply h1
      rcases he with h | h
      · rwa [h]
      · exact h2.trans h.symm.reachable
    have hx1 : x ≠ e.1 := by rintro rfl; exact h1 hx
    have hx2 : x ≠ e.2 := by rintro rfl; exact h2 hx
    unfold carpool_step; simp [hx1, hx2, hd x hx]

theorem G_local (n : ℕ) (Γ : SimpleGraph (Fin n)) (w : Fin n) :
    ∀ (es : List (Fin n × Fin n)) (cs cs' : List Bool) (d d' : Fin n → ℤ),
    (∀ e ∈ es, e.1 = e.2 ∨ Γ.Adj e.1 e.2) →
    cs.length = cs'.length →
    (∀ j (hj : j < es.length), Γ.Reachable w es[j].1 → cs[j]? = cs'[j]?) →
    (∀ x, Γ.Reachable w x → d x = d' x) →
    ∀ x, Γ.Reachable w x → G n es cs d x = G n es cs' d' x := by
  intro es
  induction es with
  | nil => intro cs cs' d d' _ _ _ hd x hx; simp [G, hd x hx]
  | cons e es ih =>
    intro cs cs' d d' hes hlen hcoin hd x hx
    cases cs with
    | nil =>
      cases cs' with
      | nil => simp [G, hd x hx]
      | cons _ _ => simp at hlen
    | cons c cs =>
      cases cs' with
      | nil => simp at hlen
      | cons c' cs' =>
        simp only [G]
        refine ih cs cs' _ _ (fun e he => hes e (List.mem_cons_of_mem _ he))
          (by simpa using hlen) ?_ ?_ x hx
        · intro j hj hr
          have := hcoin (j + 1) (by simpa using hj) (by simpa using hr)
          simpa using this
        · refine local_step n Γ w e (hes e (List.mem_cons_self ..)) d d' c c' hd ?_
          intro hr
          have := hcoin 0 (by simp) (by simpa using hr)
          simpa using this

end ForestCarpoolLocal

theorem forest_carpool_component_coin_locality (n : ℕ)
    (edges : List (Fin n × Fin n)) (v : Fin n)
    (r s : Fin edges.length → Bool)
    (hcoins : ∀ i : Fin edges.length,
      (SimpleGraph.fromEdgeSet {s(e.1, e.2) | e ∈ edges}).Reachable v (edges.get i).1 →
      r i = s i) :
  forest_carpool_final_discrepancy n edges r v =
    forest_carpool_final_discrepancy n edges s v := by
  rw [ForestCarpoolLocal.final_eq, ForestCarpoolLocal.final_eq]
  refine ForestCarpoolLocal.G_local n (SimpleGraph.fromEdgeSet {s(e.1, e.2) | e ∈ edges}) v edges _ _ _ _ ?_
    (by simp) ?_ (fun _ _ => rfl) v (SimpleGraph.Reachable.refl v)
  · intro e he
    by_cases h : e.1 = e.2
    · exact Or.inl h
    · exact Or.inr (SimpleGraph.fromEdgeSet_adj _ |>.mpr ⟨⟨e, he, rfl⟩, h⟩)
  · intro j hj hr
    have := hcoins ⟨j, hj⟩ (by simpa using hr)
    simp [hj, this]
