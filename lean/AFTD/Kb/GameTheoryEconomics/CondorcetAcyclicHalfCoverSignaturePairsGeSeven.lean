import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# condorcet_acyclic_half_cover_signature_pairs_ge_seven

Topic: social_choice   Node: ae8de2ce3092

Provenance: helper lemma. IN-372 supporting structural diagnostic for OP-19, 2026-10-30. Exact finite certificates and source/counting arguments documented in In372Oct30/ResearchNotes.txt. No novelty or research advance is claimed; the main election statement remains unchanged.

Let a relation on Fin m have an outside common predecessor for every set of at most three vertices, and let a positive finite family of vertex subsets each induce a well-founded relation. Suppose their membership is represented by c Boolean activity columns and a label and sign for each vertex, where each column is exactly balanced across the n subsets for each Boolean value. Then c is at least seven. Labels need not be distinct or surjective. This is a necessary condition for a half-cover encoded by complementary activity signatures, with no bound on the number of vertices or signature multiplicities.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_balanced_signature_pair_agreement
    (n c : ℕ) (hn : 0 < n) (B : Fin n → Fin c → Bool)
    (hbal : ∀ j b, 2 * (univ.filter fun v => B v j = b).card = n)
    (hthree : ∀ v w z, ∃ j, B v j = B w j ∧ B w j = B z j)
    (v w : Fin n) :
    3 ≤ (univ.filter fun j => B v j = B w j).card := by
  classical
  let S := univ.filter fun j => B v j = B w j
  change 3 ≤ S.card
  by_contra h
  have hsmall : S.card ≤ 2 := by omega
  have hne : S.Nonempty := by
    obtain ⟨j,hj,_⟩ := hthree v w v
    exact ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩⟩
  have hcpos := card_pos.mpr hne
  have hcover : ∀ z, ∃ j ∈ S, B z j = B v j := by
    intro z
    obtain ⟨j,hvw,hwz⟩ := hthree v w z
    exact ⟨j,mem_filter.mpr ⟨mem_univ _,hvw⟩,(hvw.trans hwz).symm⟩
  by_cases hone : S.card = 1
  · obtain ⟨j,hj⟩ := card_eq_one.mp hone
    have hall : (univ.filter fun z => B z j = B v j) = univ := by
      ext z
      simp only [mem_filter, mem_univ, true_and, iff_true]
      obtain ⟨i,hi,hiz⟩ := hcover z
      rw [hj] at hi
      simpa only [mem_singleton.mp hi] using hiz
    have hh := hbal j (B v j)
    rw [hall] at hh
    simp only [card_univ, Fintype.card_fin] at hh
    omega
  · have htwo : S.card = 2 := by omega
    obtain ⟨j,k,hjk,hS⟩ := card_eq_two.mp htwo
    let X := univ.filter fun z => B z j = B v j
    let Y := univ.filter fun z => B z k = B v k
    have hfull : X ∪ Y = univ := by
      ext z
      simp only [mem_union, mem_univ, iff_true]
      obtain ⟨i,hi,hiz⟩ := hcover z
      rw [hS] at hi
      simp only [mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact Or.inl (mem_filter.mpr ⟨mem_univ _,hiz⟩)
      · exact Or.inr (mem_filter.mpr ⟨mem_univ _,hiz⟩)
    have hinter : 0 < (X ∩ Y).card := by
      apply card_pos.mpr
      exact ⟨v,mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,
        mem_filter.mpr ⟨mem_univ _,rfl⟩⟩⟩
    have hcount := card_union_add_card_inter X Y
    rw [hfull] at hcount
    simp only [card_univ, Fintype.card_fin] at hcount
    have hX : 2 * X.card = n := hbal j (B v j)
    have hY : 2 * Y.card = n := hbal k (B v k)
    omega

theorem condorcet_balanced_three_agree_seven_coordinates
    (n c : ℕ) (hn : 0 < n) (B : Fin n → Fin c → Bool)
    (hbal : ∀ j b, 2 * (univ.filter fun v => B v j = b).card = n)
    (hthree : ∀ v w z, ∃ j, B v j = B w j ∧ B w j = B z j) :
    7 ≤ c := by
  classical
  let v : Fin n := ⟨0,hn⟩
  let f : Fin n → ℕ := fun w => (univ.filter fun j => B v j = B w j).card
  have hmin : ∀ w, 3 ≤ f w :=
    fun w => condorcet_balanced_signature_pair_agreement n c hn B hbal hthree v w
  have hself : f v = c := by simp [f]
  have hswap : (∑ w, f w) = ∑ j : Fin c, (univ.filter fun w => B v j = B w j).card := by
    simp only [f, card_eq_sum_ones, sum_filter]
    exact sum_comm
  have hcount : 2 * (∑ w, f w) = c * n := by
    rw [hswap, mul_sum]
    have heach : ∀ j : Fin c, 2 * (univ.filter fun w => B v j = B w j).card = n := by
      intro j
      simpa only [eq_comm] using hbal j (B v j)
    simp_rw [heach]
    simp
  have hle : 3 * n ≤ ∑ w, f w := by
    have h := sum_le_sum (s := (univ : Finset (Fin n))) (fun w _ => hmin w)
    simpa [Nat.mul_comm] using h
  have hsix : 6 ≤ c := by
    by_contra h
    have hc : c ≤ 5 := by omega
    nlinarith
  have hlt : 3 * n < ∑ w, f w := by
    have h := sum_lt_sum (s := (univ : Finset (Fin n))) (fun w _ => hmin w)
      ⟨v,mem_univ _,by rw [hself]; omega⟩
    simpa [Nat.mul_comm] using h
  by_contra h
  have hc : c ≤ 6 := by omega
  nlinarith

theorem condorcet_acyclic_three_sources_omit
    (m n : ℕ) (R : Fin m → Fin m → Prop) (U : Fin n → Finset (Fin m))
    (hroot : ∀ J : Finset (Fin m), J.card ≤ 3 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val)) :
    ∀ v w z, ∃ a, a ∉ U v ∧ a ∉ U w ∧ a ∉ U z := by
  classical
  obtain ⟨r,_,_⟩ := hroot ∅ (by simp)
  have hsources : ∀ v, ∃ b, ∀ a ∈ U v, ¬R a b := by
    intro v
    by_cases hne : (U v).Nonempty
    · obtain ⟨a,ha⟩ := hne
      obtain ⟨b,_,hmin⟩ := (hU v).has_min Set.univ ⟨⟨a,ha⟩,Set.mem_univ _⟩
      exact ⟨b.val,fun a ha hab => hmin ⟨a,ha⟩ (Set.mem_univ _) hab⟩
    · exact ⟨r,fun a ha => False.elim (hne ⟨a,ha⟩)⟩
  choose b hb using hsources
  intro v w z
  obtain ⟨a,_,ha⟩ := hroot {b v,b w,b z} (by
    have h := card_insert_le (b v) ({b w,b z} : Finset (Fin m))
    have h2 : ({b w,b z} : Finset (Fin m)).card ≤ 2 := card_le_two
    omega)
  exact ⟨a,fun hv => hb v a hv (ha _ (by simp)),
    fun hw => hb w a hw (ha _ (by simp)),fun hz => hb z a hz (ha _ (by simp))⟩

theorem condorcet_acyclic_half_cover_signature_pairs_ge_seven
    (m n c : ℕ) (hn : 0 < n) (R : Fin m → Fin m → Prop)
    (U : Fin n → Finset (Fin m))
    (hroot : ∀ J : Finset (Fin m), J.card ≤ 3 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (B : Fin n → Fin c → Bool) (label : Fin m → Fin c) (sign : Fin m → Bool)
    (hbal : ∀ j b, 2 * (univ.filter fun v => B v j = b).card = n)
    (hmem : ∀ a v, a ∈ U v ↔ B v (label a) = sign a) :
    7 ≤ c := by
  apply condorcet_balanced_three_agree_seven_coordinates n c hn B hbal
  intro v w z
  obtain ⟨a,hv,hw,hz⟩ := condorcet_acyclic_three_sources_omit m n R U hroot hU v w z
  have hv' : B v (label a) ≠ sign a := fun h => hv ((hmem a v).mpr h)
  have hw' : B w (label a) ≠ sign a := fun h => hw ((hmem a w).mpr h)
  have hz' : B z (label a) ≠ sign a := fun h => hz ((hmem a z).mpr h)
  have hbool : ∀ x y b : Bool, x ≠ b → y ≠ b → x = y := by decide
  exact ⟨label a,hbool _ _ _ hv' hw',hbool _ _ _ hw' hz'⟩
