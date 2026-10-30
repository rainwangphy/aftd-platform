import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetDimensionLeThreeIffAcyclicWeightSeparation
import AFTD.Kb.GameTheoryEconomics.CondorcetPrivateTripleStationarityObstruction
import AFTD.Kb.GameTheoryEconomics.CondorcetReversalTensorAcyclicHalfCoverIff
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_dimension_le_three_iff_oriented_acyclic_weight_separation

Topic: social_choice   Node: 25130f68cbba

Provenance: helper lemma. IN-362 exact structural reformulation for OP-19. Standard categorical product and homomorphism pullback, using the already Lean-verified19-vertex oriented S3 relation. Background products/fractional colouring: https://www.ub.edu/comb/koljaknauer/Gil_manuscript.pdf . No new election bound, novel research theorem, or research advance is claimed.

The unchanged universal strict three-candidate election conjecture is equivalent to the strict acyclic-weight-separation assertion restricted to ORIENTED finite relations: R(a,b) excludes R(b,a), but completeness is not assumed. The relation must still give an outside common predecessor for every set of at most three vertices. The auxiliary construction lifts any S3 integer acyclic half-cover on m vertices to an oriented S3 half-cover on19*m vertices, preserving the number of voters. Thus reciprocal edges can be eliminated from a hypothetical counterexample; one may focus on arbitrary incomplete oriented S3 relations. No graph-size bound or universal weight construction is supplied.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_triple_predecessor_tensor
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (R : A → A → Prop) (T : B → B → Prop)
    (hR : ∀ J : Finset A, J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hT : ∀ J : Finset B, J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, T a b) :
    ∀ J : Finset (A × B), J.card ≤ 3 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a.1 b.1 ∧ T a.2 b.2 := by
  classical
  intro J hJ
  obtain ⟨a,ha,haR⟩ := hR (J.image Prod.fst) (card_image_le.trans hJ)
  obtain ⟨b,hb,hbT⟩ := hT (J.image Prod.snd) (card_image_le.trans hJ)
  refine ⟨(a,b),?_,?_⟩
  · intro hab
    exact ha (mem_image.mpr ⟨(a,b),hab,rfl⟩)
  · intro c hc
    exact ⟨haR c.1 (mem_image.mpr ⟨c,hc,rfl⟩), hbT c.2 (mem_image.mpr ⟨c,hc,rfl⟩)⟩

theorem condorcet_oriented_tensor_auxiliary_s3 :
    ∀ J : Finset (Fin 19), J.card ≤ 3 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, condorcet_private_stationary_relation a b := by
  intro J hJ
  obtain ⟨K,hJK,_,hK⟩ := exists_subsuperset_card_eq (subset_univ J) hJ
    (show 3 ≤ (univ : Finset (Fin 19)).card by decide)
  obtain ⟨a,b,c,_,_,_,hKabc⟩ := card_eq_three.mp hK
  obtain ⟨r,hra,hrb,hrc⟩ := condorcet_private_stationary_s3 a b c
  have hr : ∀ x ∈ K, condorcet_private_stationary_relation r x := by
    intro x hx
    rw [hKabc] at hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hra
    · exact hrb
    · exact hrc
  refine ⟨r,?_,fun x hx => hr x (hJK hx)⟩
  intro hrJ
  exact condorcet_private_stationary_tournament.1 r (hr r (hJK hrJ))

theorem condorcet_oriented_tensor_half_cover_lift
    (m n : ℕ) (R : Fin m → Fin m → Prop) (U : Fin n → Finset (Fin m))
    (hR : ∀ J : Finset (Fin m), J.card ≤ 3 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (hhalf : ∀ a, n ≤ 2 * (univ.filter fun v => a ∈ U v).card) :
    ∃ (Q : Fin (m * 19) → Fin (m * 19) → Prop)
      (V : Fin n → Finset (Fin (m * 19))),
      (∀ a b, Q a b → ¬ Q b a) ∧
      (∀ J : Finset (Fin (m * 19)), J.card ≤ 3 →
        ∃ a, a ∉ J ∧ ∀ b ∈ J, Q a b) ∧
      (∀ v, WellFounded (fun a b : {a : Fin (m * 19) // a ∈ V v} => Q a.val b.val)) ∧
      (∀ a, n ≤ 2 * (univ.filter fun v => a ∈ V v).card) := by
  classical
  let e : Fin m × Fin 19 ≃ Fin (m * 19) := finProdFinEquiv
  let Q : Fin (m * 19) → Fin (m * 19) → Prop := fun a b =>
    R (e.symm a).1 (e.symm b).1 ∧
      condorcet_private_stationary_relation (e.symm a).2 (e.symm b).2
  obtain ⟨V,hV,hcount⟩ := condorcet_tensor_half_cover_pullback Q R
    (fun a => (e.symm a).1) (fun a b hab => hab.1) n U hU
  refine ⟨Q,V,?_,?_,hV,?_⟩
  · intro a b hab hba
    have habT := hab.2
    have hbaT := hba.2
    by_cases heq : (e.symm a).2 = (e.symm b).2
    · rw [heq] at habT
      exact condorcet_private_stationary_tournament.1 _ habT
    · exact (condorcet_private_stationary_tournament.2 _ _ heq).mp habT hbaT
  · intro J hJ
    obtain ⟨a,ha,haR⟩ := condorcet_triple_predecessor_tensor R
      condorcet_private_stationary_relation hR condorcet_oriented_tensor_auxiliary_s3
      (J.image e.symm) (card_image_le.trans hJ)
    refine ⟨e a,?_,?_⟩
    · intro hea
      exact ha (mem_image.mpr ⟨e a,hea,e.symm_apply_apply a⟩)
    · intro b hb
      have h := haR (e.symm b) (mem_image.mpr ⟨b,hb,rfl⟩)
      change R (e.symm (e a)).1 (e.symm b).1 ∧
        condorcet_private_stationary_relation (e.symm (e a)).2 (e.symm b).2
      simpa only [e.symm_apply_apply] using h
  · intro a
    rw [hcount a]
    exact hhalf (e.symm a).1

theorem condorcet_dimension_le_three_iff_oriented_acyclic_weight_separation :
    (∀ (n m : ℕ) (P : Fin n → Equiv.Perm (Fin m)), 0 < n →
      ∃ S : Finset (Fin m), S.card ≤ 3 ∧ is_condorcet_winning_set P S) ↔
    (∀ (m : ℕ) (R : Fin m → Fin m → Prop),
      (∀ a b, R a b → ¬ R b a) →
      (∀ J : Finset (Fin m), J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b) →
      ∃ w : Fin m → ℝ, (∀ a, 0 ≤ w a) ∧
        ∀ A : Finset (Fin m),
          WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
          2 * (∑ a ∈ A, w a) < ∑ a, w a) := by
  constructor
  · intro hmain m R _ hR
    exact condorcet_dimension_le_three_iff_acyclic_weight_separation.mp hmain m R hR
  · intro horiented
    apply condorcet_dimension_le_three_iff_acyclic_weight_separation.mpr
    intro m R hR
    apply (condorcet_half_cover_acyclic_half_cover_duality m R).mp
    rintro ⟨n,U,hn,hU,hhalf⟩
    obtain ⟨Q,V,hQasym,hQroot,hV,hVhalf⟩ :=
      condorcet_oriented_tensor_half_cover_lift m n R U hR hU hhalf
    obtain ⟨w,hw,hsep⟩ := horiented (m * 19) Q hQasym hQroot
    exact condorcet_half_cover_finite_weighted_half_cover_exclusion (m * 19) n hn V hVhalf
      w hw (fun v => hsep _ (hV v))
