import AFTD.Prelude
import AFTD.Kb.Tcs.Op869RepeatedColorIncidence
import AFTD.Kb.Tcs.Op869DisjointReservedCopies

/-!
# op869_repeated_colors_have_reservations

Topic: online_algorithms   Node: 86c4212a4450

Provenance: helper lemma. arXiv:2610.41516, Section 2.2

If every one of KqD copies contains at least q colors and fewer than K colors occur globally, choose q distinct colors and D disjoint copies per color in which it occurs.
-/

/-- A finite combinatorial step in the three-colorable online-coloring simulation. -/
theorem op869_repeated_colors_have_reservations {α β : Type} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop) [DecidableRel R] (K q D : ℕ)
    (hq : 1 ≤ q) (hqK : q ≤ K) (hD : 1 ≤ D) (hA : A.card = K * q * D)
    (hB : B.card < K) (hd : ∀ a ∈ A, q ≤ (B.filter (R a)).card) :
    ∃ color : Fin q → β, Function.Injective color ∧ (∀ i, color i ∈ B) ∧
      ∃ reserve : Fin q → Finset α,
        (∀ i, (reserve i).card = D ∧ ∀ a ∈ reserve i, a ∈ A ∧ R a (color i)) ∧
        ∀ i j, i ≠ j → Disjoint (reserve i) (reserve j) := by
  classical
  let H := B.filter (fun b => q * D ≤ (A.filter (fun a => R a b)).card)
  have hH : q ≤ H.card := op869_repeated_color_incidence A B R K q D hq hqK hD hA hB hd
  obtain ⟨T, hTH, hT⟩ := Finset.exists_subset_card_eq hH
  let e : Fin q ≃ {b // b ∈ T} := (Fintype.equivFinOfCardEq (by simpa using hT)).symm
  let color : Fin q → β := fun i => (e i).1
  have hinj : Function.Injective color := Subtype.val_injective.comp e.injective
  have hcolor : ∀ i, color i ∈ H := fun i => hTH (e i).2
  let S : Fin q → Finset α := fun i => A.filter (fun a => R a (color i))
  have hS : ∀ i, q * D ≤ (S i).card := by
    intro i
    exact (Finset.mem_filter.mp (hcolor i)).2
  obtain ⟨reserve, hreserve, hdisj⟩ := op869_disjoint_reserved_copies q D S hS
  refine ⟨color, hinj, ?_, reserve, ?_, hdisj⟩
  · intro i
    exact (Finset.mem_filter.mp (hcolor i)).1
  · intro i
    refine ⟨(hreserve i).2, ?_⟩
    intro a ha
    exact Finset.mem_filter.mp ((hreserve i).1 ha)
