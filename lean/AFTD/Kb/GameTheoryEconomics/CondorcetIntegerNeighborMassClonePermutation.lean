import AFTD.Prelude

/-!
# condorcet_integer_neighbor_mass_clone_permutation

Topic: social_choice   Node: 8be2e4d46e2e

Provenance: helper lemma. IN-380, OP-19 campaign session8, 2026-10-30. Supporting reduction from the proved strict-half circulation bridge. Scratch ClosedWalk.lean passed trusted-axiom checking. Standard finite matching and orbit averaging; no research novelty or new election bound is claimed.

Finite weighted neighborhood inequalities imply an arrow-supported permutation on the finite set containing w(a) clones of every vertex a. This exposes the same matching construction used to build the integer circulation.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_integer_neighbor_mass_clone_permutation
    (m : ℕ) (R : Fin m → Fin m → Prop) [DecidableRel R] (w : Fin m → ℕ)
    (hHall : ∀ S : Finset (Fin m),
      (∑ a ∈ S, w a) ≤ ∑ b ∈ univ.filter (fun b => ∃ a ∈ S, R a b), w b) :
    ∃ e : Equiv.Perm (Σ a : Fin m, Fin (w a)), ∀ x, R x.1 (e x).1 := by
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
  refine ⟨e,?_⟩
  intro x
  exact (mem_filter.mp (hg x)).2
