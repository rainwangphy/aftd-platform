import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMnwAllocation
import AFTD.Kb.GameTheoryEconomics.NashWelfare
import AFTD.Kb.GameTheoryEconomics.UtilitarianWelfare
import AFTD.Kb.GameTheoryEconomics.Mnw2Core
import AFTD.Kb.GameTheoryEconomics.Mnw2SumGroups
import AFTD.Kb.GameTheoryEconomics.Mnw2BundleValue

/-!
# mnw_two_agents_welfare_le

Topic: fair_division   Node: 4f5efdbb9eb6

Provenance: original. Related work: settles the two-agent gap of The Price of Fairness for Indivisible Goods, arXiv:1905.04910, Theorem 5.4 (price and strong price of MNW in [27/23, 5/4]): the upper bound 27/23 is new, so the value is exactly 27/23

For two agents with additive, nonnegative, normalized valuations (v_i(M) = 1) over any number m of goods, every maximum Nash welfare allocation N satisfies 23 · SW(O) ≤ 27 · SW(N) for every allocation O. Hence the price of MNW and the strong price of MNW for two agents are at most 27/23, improving the upper bound 5/4 of arXiv:1905.04910 Theorem 5.4 and matching its lower bound. Proof: group the goods by their owners under O and N and apply the core inequality to the constraints that N beats O and the four allocations giving agent 0 exactly A, C, A∪B∪C and A∪C∪D.
-/

/-- Price of MNW for two agents is at most 27/23: any MNW allocation has at least 23/27 of the welfare of any allocation. -/
theorem mnw_two_agents_welfare_le (m : ℕ) (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) (hn : ∀ i, ∑ g, v i g = 1) (N O : Fin m → Fin 2) (hN : is_mnw_allocation v N) : 23 * utilitarian_welfare v O ≤ 27 * utilitarian_welfare v N := by
  obtain ⟨p, hp⟩ : ∃ x, ∑ g ∈ Finset.univ.filter (fun g => O g = 0 ∧ N g = 0), v 0 g = x := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ x, ∑ g ∈ Finset.univ.filter (fun g => O g = 1 ∧ N g = 0), v 0 g = x := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ x, ∑ g ∈ Finset.univ.filter (fun g => O g = 0 ∧ N g = 1), v 0 g = x := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ x, ∑ g ∈ Finset.univ.filter (fun g => O g = 1 ∧ N g = 1), v 0 g = x := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ x, ∑ g ∈ Finset.univ.filter (fun g => O g = 0 ∧ N g = 0), v 1 g = x := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ x, ∑ g ∈ Finset.univ.filter (fun g => O g = 1 ∧ N g = 0), v 1 g = x := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ x, ∑ g ∈ Finset.univ.filter (fun g => O g = 0 ∧ N g = 1), v 1 g = x := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ x, ∑ g ∈ Finset.univ.filter (fun g => O g = 1 ∧ N g = 1), v 1 g = x := ⟨_, rfl⟩
  have nn : ∀ i (F : Finset (Fin m)), 0 ≤ ∑ g ∈ F, v i g := fun i F => Finset.sum_nonneg fun g _ => hv i g
  have h1 : p + q + r + s = 1 := by
    have e := mnw2_sum_groups (v 0) O N (fun _ _ => 1)
    simp only [one_mul] at e
    rw [← hn 0, e, hp, hq, hr, hs]
  have h2 : α + β + γ + δ = 1 := by
    have e := mnw2_sum_groups (v 1) O N (fun _ _ => 1)
    simp only [one_mul] at e
    rw [← hn 1, e, hα, hβ, hγ, hδ]
  have hval : ∀ (τ : Fin m → Fin 2) (T : Fin 2 → Fin 2 → Fin 2), (∀ g, τ g = T (O g) (N g)) →
      nash_welfare v τ = ((if T 0 0 = 0 then 1 else 0) * p + (if T 1 0 = 0 then 1 else 0) * q + (if T 0 1 = 0 then 1 else 0) * r + (if T 1 1 = 0 then 1 else 0) * s) * ((if T 0 0 = 1 then 1 else 0) * α + (if T 1 0 = 1 then 1 else 0) * β + (if T 0 1 = 1 then 1 else 0) * γ + (if T 1 1 = 1 then 1 else 0) * δ) ∧ utilitarian_welfare v τ = ((if T 0 0 = 0 then 1 else 0) * p + (if T 1 0 = 0 then 1 else 0) * q + (if T 0 1 = 0 then 1 else 0) * r + (if T 1 1 = 0 then 1 else 0) * s) + ((if T 0 0 = 1 then 1 else 0) * α + (if T 1 0 = 1 then 1 else 0) * β + (if T 0 1 = 1 then 1 else 0) * γ + (if T 1 1 = 1 then 1 else 0) * δ) := by
    intro τ T hτ
    rw [nash_welfare, utilitarian_welfare, Fin.prod_univ_two, Fin.sum_univ_two,
      mnw2_bundle_value (v 0) O N τ T hτ 0, mnw2_bundle_value (v 1) O N τ T hτ 1,
      hp, hq, hr, hs, hα, hβ, hγ, hδ]
    exact ⟨rfl, rfl⟩
  obtain ⟨nN, uN⟩ := hval N (fun _ b => b) (fun _ => rfl)
  obtain ⟨nO, uO⟩ := hval O (fun a _ => a) (fun _ => rfl)
  have cO := hN O
  have cA := hN (fun g => if O g = 0 ∧ N g = 0 then 0 else 1)
  have cC := hN (fun g => if O g = 0 ∧ N g = 1 then 0 else 1)
  have cABC := hN (fun g => if O g = 1 ∧ N g = 1 then 1 else 0)
  have cACD := hN (fun g => if O g = 1 ∧ N g = 0 then 1 else 0)
  rw [(hval _ (fun a b => if a = 0 ∧ b = 0 then 0 else 1) (fun _ => rfl)).1] at cA
  rw [(hval _ (fun a b => if a = 0 ∧ b = 1 then 0 else 1) (fun _ => rfl)).1] at cC
  rw [(hval _ (fun a b => if a = 1 ∧ b = 1 then 1 else 0) (fun _ => rfl)).1] at cABC
  rw [(hval _ (fun a b => if a = 1 ∧ b = 0 then 1 else 0) (fun _ => rfl)).1] at cACD
  rw [nO] at cO
  rw [nN] at cO cA cC cABC cACD
  rw [uN, uO]
  simp at cO cA cC cABC cACD ⊢
  have key := mnw2_core p q r s α β γ δ (by rw [← hp]; exact nn 0 _) (by rw [← hq]; exact nn 0 _) (by rw [← hr]; exact nn 0 _) (by rw [← hs]; exact nn 0 _)
    (by rw [← hα]; exact nn 1 _) (by rw [← hβ]; exact nn 1 _) (by rw [← hγ]; exact nn 1 _) (by rw [← hδ]; exact nn 1 _) h1 h2
    (by linear_combination cO) (by linear_combination cA) (by linear_combination cC)
    (by linear_combination cABC) (by linear_combination cACD)
  linear_combination key
