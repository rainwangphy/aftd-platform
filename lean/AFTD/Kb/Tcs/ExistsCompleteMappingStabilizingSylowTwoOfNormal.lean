import AFTD.Prelude
import AFTD.Kb.Tcs.GroupIsCompleteMapping

/-!
# exists_complete_mapping_stabilizing_sylow_two_of_normal

Topic: combinatorics   Node: 1c1c2f2de871

Provenance: formalization of a published result. Source: arXiv:2610.17631 (Complete mappings stabilizing Sylow 2-subgroups in central quotients of special linear groups), Lemma 3.2.

Let G be a finite group, N a normal subgroup and P a Sylow 2-subgroup of G. If N has a complete mapping stabilizing P ∩ N and G/N has a complete mapping stabilizing PN/N, then G has a complete mapping stabilizing P.
-/

theorem exists_complete_mapping_stabilizing_sylow_two_of_normal {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (P : Sylow 2 G)
    (hN : ∃ φ : N → N, group_is_complete_mapping φ ∧
      φ '' {x : N | (x : G) ∈ (P : Subgroup G)} = {x : N | (x : G) ∈ (P : Subgroup G)})
    (hQ : ∃ θ : G ⧸ N → G ⧸ N, group_is_complete_mapping θ ∧
      θ '' ((P : Subgroup G).map (QuotientGroup.mk' N) : Set (G ⧸ N)) =
        ((P : Subgroup G).map (QuotientGroup.mk' N) : Set (G ⧸ N))) :
    ∃ θ : G → G, group_is_complete_mapping θ ∧
      θ '' ((P : Subgroup G) : Set G) = ((P : Subgroup G) : Set G) := by
  classical
  obtain ⟨φ, ⟨hφ, hφc⟩, hφP⟩ := hN
  obtain ⟨τ, ⟨hτ, hτc⟩, hτP⟩ := hQ
  have hφP' : ∀ n : N, (n : G) ∈ (P : Subgroup G) → (φ n : G) ∈ (P : Subgroup G) := by
    intro n hn
    have : φ n ∈ φ '' {x : N | (x : G) ∈ (P : Subgroup G)} := ⟨n, hn, rfl⟩
    rw [hφP] at this
    exact this
  have hτP' : ∀ t, t ∈ (P : Subgroup G).map (QuotientGroup.mk' N) →
      τ t ∈ (P : Subgroup G).map (QuotientGroup.mk' N) := by
    intro t ht
    have : τ t ∈ τ '' ((P : Subgroup G).map (QuotientGroup.mk' N) : Set (G ⧸ N)) := ⟨t, ht, rfl⟩
    rw [hτP] at this
    exact this
  -- representatives, chosen in P over the image of P
  have hrep : ∀ t : G ⧸ N, ∃ g : G, (g : G ⧸ N) = t ∧
      (t ∈ (P : Subgroup G).map (QuotientGroup.mk' N) → g ∈ (P : Subgroup G)) := by
    intro t
    by_cases ht : t ∈ (P : Subgroup G).map (QuotientGroup.mk' N)
    · obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 ht
      exact ⟨p, rfl, fun _ => hp⟩
    · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
      exact ⟨g, rfl, fun h => absurd h ht⟩
  choose x hx hxP using hrep
  have hmkN : ∀ n : N, ((n : G) : G ⧸ N) = 1 := fun n => (QuotientGroup.eq_one_iff (n : G)).2 n.2
  let A : (G ⧸ N) × N → G := fun p => x p.1 * x (τ p.1) * (p.2 : G) * (x (τ p.1))⁻¹
  let B : (G ⧸ N) × N → G := fun p => x (τ p.1) * (φ p.2 : G)
  have hAmk : ∀ p, ((A p : G) : G ⧸ N) = p.1 := by
    intro p
    simp only [A, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx, hmkN]
    group
  have hBmk : ∀ p, ((B p : G) : G ⧸ N) = τ p.1 := by
    intro p
    simp only [B, QuotientGroup.mk_mul, hx, hmkN, mul_one]
  have hAB : ∀ p, A p * B p = x p.1 * x (τ p.1) * ((p.2 * φ p.2 : N) : G) := by
    intro p
    simp only [A, B, Subgroup.coe_mul]
    group
  have hcard : Nat.card G ≤ Nat.card ((G ⧸ N) × N) := by
    rw [Nat.card_prod, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hAinj : Function.Injective A := by
    rintro ⟨t, n⟩ ⟨t', n'⟩ h
    have ht : t = t' := by
      have e1 := hAmk (t, n)
      have e2 := hAmk (t', n')
      rw [h] at e1
      exact e1.symm.trans e2
    subst ht
    simp only [A, mul_left_inj, mul_right_inj] at h
    exact Prod.ext rfl (Subtype.ext h)
  have hBinj : Function.Injective B := by
    rintro ⟨t, n⟩ ⟨t', n'⟩ h
    have ht : t = t' := hτ.1 (by rw [← hBmk (t, n), ← hBmk (t', n'), h])
    subst ht
    simp only [B, mul_right_inj] at h
    exact Prod.ext rfl (hφ.1 (Subtype.ext h))
  have hCinj : Function.Injective fun p => A p * B p := by
    rintro ⟨t, n⟩ ⟨t', n'⟩ h
    have h' : A (t, n) * B (t, n) = A (t', n') * B (t', n') := h
    have ht : t = t' := by
      apply hτc.1
      have e1 := hAmk (t, n)
      have e2 := hBmk (t, n)
      have e3 := hAmk (t', n')
      have e4 := hBmk (t', n')
      have := congrArg (fun g : G => (g : G ⧸ N)) h'
      simp only [QuotientGroup.mk_mul] at this
      rw [e1, e2, e3, e4] at this
      exact this
    subst ht
    rw [hAB, hAB] at h'
    simp only [mul_right_inj] at h'
    exact Prod.ext rfl (hφc.1 (Subtype.ext h'))
  have hAbij : Function.Bijective A := hAinj.bijective_of_nat_card_le hcard
  have hBbij : Function.Bijective B := hBinj.bijective_of_nat_card_le hcard
  have hCbij : Function.Bijective fun p => A p * B p := hCinj.bijective_of_nat_card_le hcard
  let eA := Equiv.ofBijective A hAbij
  have heA : ∀ g, A (eA.symm g) = g := fun g => eA.apply_symm_apply g
  refine ⟨fun g => B (eA.symm g), ⟨hBbij.comp eA.symm.bijective, ?_⟩, ?_⟩
  · have : (fun g => g * B (eA.symm g)) = (fun p => A p * B p) ∘ eA.symm := by
      funext g
      simp only [Function.comp, heA]
    rw [this]
    exact hCbij.comp eA.symm.bijective
  · have hsub : (fun g => B (eA.symm g)) '' ((P : Subgroup G) : Set G) ⊆ ((P : Subgroup G) : Set G) := by
      rintro _ ⟨g, hg, rfl⟩
      set p := eA.symm g with hp
      have hAp : A p = g := heA g
      have hq : p.1 ∈ (P : Subgroup G).map (QuotientGroup.mk' N) := by
        rw [← hAmk p, hAp]
        exact Subgroup.mem_map_of_mem _ hg
      have h1 := hxP _ hq
      have h2 := hxP _ (hτP' _ hq)
      have hn : ((p.2 : N) : G) ∈ (P : Subgroup G) := by
        have : ((p.2 : N) : G) = (x p.1 * x (τ p.1))⁻¹ * g * x (τ p.1) := by
          rw [← hAp]
          simp only [A]
          group
        rw [this]
        exact mul_mem (mul_mem (inv_mem (mul_mem h1 h2)) hg) h2
      exact mul_mem h2 (hφP' _ hn)
    have hinj : Function.Injective fun g => B (eA.symm g) := hBinj.comp eA.symm.injective
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_image_of_injective _ hinj])
