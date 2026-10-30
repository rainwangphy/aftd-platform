import AFTD.Prelude

/-!
# condorcet_integer_circulation_of_neighbor_mass

Topic: social_choice   Node: f5fb640efb96

Provenance: helper lemma. IN-380, OP-19 campaign session 8, 2026-10-30. Self-contained helper for the strict-half acyclic-separation route. The general unrestricted one-child equality was refuted in IN-372; this work repairs only the strict-half existence reduction. Standard finite matching, rational density, and circulation weak duality are used. No new election bound or research novelty is claimed. See lean/AFTD/Scratch/In380Oct30/HalfThresholdDerivation.txt.

For any finite directed relation and natural-number vertex weights w, assume every vertex set S has weight at most its outgoing neighborhood. Then there are natural-number edge multiplicities f, zero off the relation, whose row sums and column sums both equal w. This includes the zero-weight and loop cases.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_integer_circulation_of_neighbor_mass
    (m : ℕ) (R : Fin m → Fin m → Prop) [DecidableRel R] (w : Fin m → ℕ)
    (hHall : ∀ S : Finset (Fin m),
      (∑ a ∈ S, w a) ≤ ∑ b ∈ univ.filter (fun b => ∃ a ∈ S, R a b), w b) :
    ∃ f : Fin m → Fin m → ℕ,
      (∀ a b, ¬ R a b → f a b = 0) ∧
      (∀ a, ∑ b, f a b = w a) ∧ (∀ b, ∑ a, f a b = w b) := by
  classical
  let V := Σ a : Fin m, Fin (w a)
  have hcard (S : Finset (Fin m)) :
      (univ.filter (fun x : V => x.1 ∈ S)).card = ∑ a ∈ S, w a := by
    rw [card_eq_sum_ones,sum_filter]
    change (∑ x : (Σ a : Fin m, Fin (w a)), if x.1 ∈ S then 1 else 0) = _
    rw [Fintype.sum_sigma]
    rw [← Fintype.sum_ite_mem S w]
    apply sum_congr rfl
    intro a ha
    by_cases h : a ∈ S <;> simp [h]
  let neighbors : V → Finset V := fun x => univ.filter (fun y => R x.1 y.1)
  have hclones : ∀ B : Finset V, B.card ≤ (B.biUnion neighbors).card := by
    intro B
    let S := B.image Sigma.fst
    let N := univ.filter (fun b => ∃ a ∈ S, R a b)
    have hB : B ⊆ univ.filter (fun x : V => x.1 ∈ S) := by
      intro x hx
      exact mem_filter.mpr ⟨mem_univ _,mem_image.mpr ⟨x,hx,rfl⟩⟩
    have hN : B.biUnion neighbors = univ.filter (fun y : V => y.1 ∈ N) := by
      ext y
      simp only [mem_biUnion,neighbors,mem_filter,mem_univ,true_and,N,S,mem_image]
      constructor
      · rintro ⟨x,hx,hxy⟩
        exact ⟨x.1,⟨x,hx,rfl⟩,hxy⟩
      · rintro ⟨a,⟨x,hx,rfl⟩,hay⟩
        exact ⟨x,hx,hay⟩
    calc
      B.card ≤ (univ.filter (fun x : V => x.1 ∈ S)).card := card_le_card hB
      _ = ∑ a ∈ S, w a := hcard S
      _ ≤ ∑ a ∈ N, w a := hHall S
      _ = (B.biUnion neighbors).card := by rw [hN,hcard]
  obtain ⟨g,hginj,hg⟩ := (all_card_le_biUnion_card_iff_existsInjective' neighbors).mp hclones
  have hgbij : Function.Bijective g := hginj.bijective_of_finite
  let e : V ≃ V := Equiv.ofBijective g hgbij
  let f : Fin m → Fin m → ℕ := fun a b =>
    (univ.filter (fun x : V => x.1 = a ∧ (e x).1 = b)).card
  refine ⟨f,?_,?_,?_⟩
  · intro a b hab
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨_,ha,hb⟩ := mem_filter.mp hx
    have h := (mem_filter.mp (hg x)).2
    change R x.1 (e x).1 at h
    exact hab (ha ▸ hb ▸ h)
  · intro a
    have h := sum_card_fiberwise_eq_card_filter
      (univ.filter (fun x : V => x.1 = a)) univ (fun x : V => (e x).1)
    have heq : (∑ b, f a b) = (univ.filter (fun x : V => x.1 = a)).card := by
      simpa [f,filter_filter] using h
    rw [heq]
    simpa using hcard {a}
  · intro b
    have h := sum_card_fiberwise_eq_card_filter
      (univ.filter (fun x : V => (e x).1 = b)) univ (fun x : V => x.1)
    have heq : (∑ a, f a b) = (univ.filter (fun x : V => (e x).1 = b)).card := by
      simpa [f,filter_filter,and_comm] using h
    rw [heq,card_eq_sum_ones,sum_filter]
    rw [e.sum_comp (fun y : V => if y.1 = b then (1 : ℕ) else 0)]
    rw [← sum_filter,← card_eq_sum_ones]
    simpa using hcard {b}
