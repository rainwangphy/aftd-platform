import AFTD.Prelude
import AFTD.Kb.Tcs.IsUniquelyCliqueSaturated

/-!
# uniquely_k4_saturated_max_degree_six_order_twelve

Topic: graphs   Node: affb4d3a767e

Provenance: formalization of a published result. Source: arXiv:2611.13656 Sec. 2; Collins and Cooper (cf. Hartke and Stolee 2012)

There exists a simple graph G on Fin 12 such that G is uniquely K_4-saturated and the maximum degree of G equals 6.
-/

set_option maxRecDepth 50000

lemma uniquely_k4_saturated_max_degree_six_order_twelve_existsUnique_iff_card
    {α : Type*} [Fintype α] [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    (∃! x, p x) ↔ (Finset.filter p Finset.univ).card = 1 := by
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨x, hx, huniq⟩
    use x; ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hy => huniq y hy, fun hy => by subst hy; exact hx⟩
  · rintro ⟨x, hx⟩
    have hxmem : x ∈ Finset.filter p Finset.univ := by rw [hx]; exact Finset.mem_singleton_self x
    rw [Finset.mem_filter] at hxmem
    refine ⟨x, hxmem.2, fun y hy => ?_⟩
    have hymem : y ∈ Finset.filter p Finset.univ := by simp [hy]
    rw [hx] at hymem
    exact Finset.mem_singleton.mp hymem

@[default_instance 2000]
instance uniquely_k4_saturated_max_degree_six_order_twelve_fastDecidableExistsUnique
    {α : Type*} [Fintype α] [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    Decidable (∃! x, p x) :=
  decidable_of_iff ((Finset.filter p Finset.univ).card = 1)
    (uniquely_k4_saturated_max_degree_six_order_twelve_existsUnique_iff_card p).symm

lemma uniquely_k4_saturated_max_degree_six_order_twelve_isNClique_iff
    {V : Type*} (G : SimpleGraph V) (n : ℕ) (s : Finset V) :
    G.IsNClique n s ↔ s.card = n ∧ G.IsClique (s : Set V) := by
  rw [SimpleGraph.isNClique_iff, and_comm]

@[default_instance 2000]
instance uniquely_k4_saturated_max_degree_six_order_twelve_fastDecidableIsNClique
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) (s : Finset V) :
    Decidable (G.IsNClique n s) :=
  decidable_of_iff (s.card = n ∧ G.IsClique (s : Set V))
    (uniquely_k4_saturated_max_degree_six_order_twelve_isNClique_iff G n s).symm

def uniquely_k4_saturated_max_degree_six_order_twelve_icoAdj (u v : Fin 12) : Bool :=
  let (a, b) := if u.val ≤ v.val then (u.val, v.val) else (v.val, u.val)
  if a == b then false
  else if a == 0 then b ≤ 5
  else if b == 11 then 6 ≤ a
  else if a ≤ 5 && b ≤ 5 then ((a - 1 + 5 - (b - 1)) % 5 == 1) || ((a - 1 + 5 - (b - 1)) % 5 == 4)
  else if 6 ≤ a && 6 ≤ b then ((a - 6 + 5 - (b - 6)) % 5 == 1) || ((a - 6 + 5 - (b - 6)) % 5 == 4)
  else if a ≤ 5 && 6 ≤ b then
    let x := a - 1
    let y := b - 6
    (y == x) || (y == (x + 1) % 5)
  else false

def uniquely_k4_saturated_max_degree_six_order_twelve_icoCompAdj (u v : Fin 12) : Bool :=
  u ≠ v && !uniquely_k4_saturated_max_degree_six_order_twelve_icoAdj u v

def uniquely_k4_saturated_max_degree_six_order_twelve_icoCompAdjRel (u v : Fin 12) : Prop :=
  uniquely_k4_saturated_max_degree_six_order_twelve_icoCompAdj u v = true

lemma uniquely_k4_saturated_max_degree_six_order_twelve_icoCompAdjRel_symm :
    ∀ (u v : Fin 12),
      uniquely_k4_saturated_max_degree_six_order_twelve_icoCompAdjRel u v →
      uniquely_k4_saturated_max_degree_six_order_twelve_icoCompAdjRel v u := by
  intro u v; dsimp [uniquely_k4_saturated_max_degree_six_order_twelve_icoCompAdjRel]; revert u v; decide

lemma uniquely_k4_saturated_max_degree_six_order_twelve_icoCompAdjRel_irrefl :
    ∀ (u : Fin 12),
      ¬ uniquely_k4_saturated_max_degree_six_order_twelve_icoCompAdjRel u u := by
  intro u; dsimp [uniquely_k4_saturated_max_degree_six_order_twelve_icoCompAdjRel]; revert u; decide

def uniquely_k4_saturated_max_degree_six_order_twelve_icoCompGraph : SimpleGraph (Fin 12) where
  Adj := uniquely_k4_saturated_max_degree_six_order_twelve_icoCompAdjRel
  symm := ⟨uniquely_k4_saturated_max_degree_six_order_twelve_icoCompAdjRel_symm⟩
  loopless := ⟨uniquely_k4_saturated_max_degree_six_order_twelve_icoCompAdjRel_irrefl⟩

instance uniquely_k4_saturated_max_degree_six_order_twelve_instDecRelAdj :
    DecidableRel uniquely_k4_saturated_max_degree_six_order_twelve_icoCompGraph.Adj := fun u v =>
  inferInstanceAs (Decidable (uniquely_k4_saturated_max_degree_six_order_twelve_icoCompAdj u v = true))

lemma uniquely_k4_saturated_max_degree_six_order_twelve_icoComp_maxDeg :
    uniquely_k4_saturated_max_degree_six_order_twelve_icoCompGraph.maxDegree = 6 := by decide

lemma uniquely_k4_saturated_max_degree_six_order_twelve_icoComp_sat :
    is_uniquely_clique_saturated uniquely_k4_saturated_max_degree_six_order_twelve_icoCompGraph 4 := by
  dsimp [is_uniquely_clique_saturated]
  decide

lemma uniquely_k4_saturated_max_degree_six_order_twelve_icoComp_maxDeg_classical :
    (@SimpleGraph.maxDegree (Fin 12) uniquely_k4_saturated_max_degree_six_order_twelve_icoCompGraph (Fin.fintype 12)
      fun a b => Classical.propDecidable (uniquely_k4_saturated_max_degree_six_order_twelve_icoCompGraph.Adj a b)) = 6 := by
  have h : (@SimpleGraph.maxDegree (Fin 12) uniquely_k4_saturated_max_degree_six_order_twelve_icoCompGraph (Fin.fintype 12)
      fun a b => Classical.propDecidable (uniquely_k4_saturated_max_degree_six_order_twelve_icoCompGraph.Adj a b)) =
    @SimpleGraph.maxDegree (Fin 12) uniquely_k4_saturated_max_degree_six_order_twelve_icoCompGraph _
      uniquely_k4_saturated_max_degree_six_order_twelve_instDecRelAdj := by congr!
  rw [h]
  exact uniquely_k4_saturated_max_degree_six_order_twelve_icoComp_maxDeg

open scoped Classical in
/-- There exists a uniquely K_4-saturated simple graph on 12 vertices with maximum degree 6 (the complement of the icosahedral graph). -/
theorem uniquely_k4_saturated_max_degree_six_order_twelve :
    ∃ (G : SimpleGraph (Fin 12)),
      is_uniquely_clique_saturated G 4 ∧ G.maxDegree = 6 :=
  ⟨uniquely_k4_saturated_max_degree_six_order_twelve_icoCompGraph,
   uniquely_k4_saturated_max_degree_six_order_twelve_icoComp_sat,
   uniquely_k4_saturated_max_degree_six_order_twelve_icoComp_maxDeg_classical⟩
