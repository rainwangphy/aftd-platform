import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetCoverRankRelation

/-!
# condorcet_stable_fractional_tight_cover_obstruction

Topic: social_choice   Node: 5b8ec14075ca

Provenance: helper lemma. IN-391, OP-19 campaign session10, 2026-10-30. Method diagnostic for the stable-fractional-matching route suggested by On a lemma of Scarf, Theorem2.1, https://doi.org/10.1016/S0095-8956%2802%2900028-X. Experiment9879 supplies the finite orders; the uniqueness and all-solutions rounding obstruction are proved here in Lean. This is not a Condorcet counterexample and no election bound or research novelty is claimed.

There are twenty three-element activity sets on six vertices, covering each vertex ten times, and injective local rankings. A stable fractional matching exists, but every such matching is exactly the uniform weight1/3. For every stable fractional matching and every set J of at most three vertices, some tight activity set is disjoint from J. The rank-compatible relation explicitly fails S3. Hence changing the stable fractional solution cannot guarantee three-vertex coverage of all tight sets for an arbitrary supplied half-cover family. The statement does not concern the family of all induced acyclic sets.
-/

open Finset BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option synthInstance.maxSize 10000
def condorcet_stable_gap_sets : Fin 20 → Finset (Fin 6) := ![{0,1,2},{0,1,3},{0,1,4},{0,1,5},{0,2,3},{0,2,4},{0,2,5},{0,3,4},{0,3,5},{0,4,5},{1,2,3},{1,2,4},{1,2,5},{1,3,4},{1,3,5},{1,4,5},{2,3,4},{2,3,5},{2,4,5},{3,4,5}]
def condorcet_stable_gap_rank : Fin 20 → Fin 6 → ℕ := ![![0,1,2,9,10,11],![0,1,8,2,10,11],![1,2,8,9,0,11],![1,2,8,9,10,0],![2,7,0,1,10,11],![0,7,2,9,1,11],![2,7,0,9,10,1],![1,7,8,0,2,11],![2,7,8,0,10,1],![2,7,8,9,0,1],![6,0,1,2,10,11],![6,0,1,9,2,11],![6,0,1,9,10,2],![6,1,8,0,2,11],![6,2,8,1,10,0],![6,1,8,9,0,2],![6,7,0,1,2,11],![6,7,0,1,10,2],![6,7,2,9,0,1],![6,7,8,0,1,2]]
def condorcet_stable_gap_next : Fin 6 → Fin 6 := ![1,2,3,4,5,0]

theorem condorcet_stable_gap_uniform (w : Fin 6 → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hcap : ∀ v, (∑ a ∈ condorcet_stable_gap_sets v, w a) ≤ 1)
    (hstable : ∀ a, ∃ v, a ∈ condorcet_stable_gap_sets v ∧
      (∑ b ∈ condorcet_stable_gap_sets v, w b) = 1 ∧
      ∀ b ∈ condorcet_stable_gap_sets v, 0 < w b →
        condorcet_stable_gap_rank v b ≤ condorcet_stable_gap_rank v a) :
    ∀ a, w a = 1 / 3 := by
  have hcyc : ∀ a v, a ∈ condorcet_stable_gap_sets v →
      condorcet_stable_gap_next a ∈ condorcet_stable_gap_sets v →
      condorcet_stable_gap_rank v a < condorcet_stable_gap_rank v (condorcet_stable_gap_next a) := by decide
  have hreplace : ∀ (v : Fin 20) (a b : Fin 6),
      a ∈ condorcet_stable_gap_sets v → b ∉ condorcet_stable_gap_sets v →
      ∃ z, condorcet_stable_gap_sets z = insert b ((condorcet_stable_gap_sets v).erase a) := by decide
  have hmono : ∀ a, w (condorcet_stable_gap_next a) ≤ w a := by
    intro a
    by_cases hpos : 0 < w (condorcet_stable_gap_next a)
    · obtain ⟨v,hav,hload,horder⟩ := hstable a
      have hb : condorcet_stable_gap_next a ∉ condorcet_stable_gap_sets v := by
        intro hb
        exact (not_lt_of_ge (horder _ hb hpos)) (hcyc a v hav hb)
      obtain ⟨z,hz⟩ := hreplace v a (condorcet_stable_gap_next a) hav hb
      have hc := hcap z
      rw [hz, sum_insert (fun h => hb (mem_of_mem_erase h))] at hc
      have hs := sum_erase_add (condorcet_stable_gap_sets v) w hav
      rw [hload] at hs
      linarith
    · exact (le_of_not_gt hpos).trans (hw a)
  have h0 : w 1 ≤ w 0 := hmono 0
  have h1 : w 2 ≤ w 1 := hmono 1
  have h2 : w 3 ≤ w 2 := hmono 2
  have h3 : w 4 ≤ w 3 := hmono 3
  have h4 : w 5 ≤ w 4 := hmono 4
  have h5 : w 0 ≤ w 5 := hmono 5
  have heq1 : w 1 = w 0 := by linarith
  have heq2 : w 2 = w 0 := by linarith
  have heq3 : w 3 = w 0 := by linarith
  have heq4 : w 4 = w 0 := by linarith
  have heq5 : w 5 = w 0 := by linarith
  have heq : ∀ a : Fin 6, w a = w 0 := by
    intro a
    fin_cases a
    · rfl
    · exact heq1
    · exact heq2
    · exact heq3
    · exact heq4
    · exact heq5
  obtain ⟨v,_,hload,_⟩ := hstable 0
  have hcard : ∀ v, (condorcet_stable_gap_sets v).card = 3 := by decide
  simp_rw [heq] at hload
  rw [sum_const,hcard] at hload
  norm_num at hload
  intro a
  rw [heq]
  linarith

theorem condorcet_stable_fractional_tight_cover_obstruction :
    ∃ (U : Fin 20 → Finset (Fin 6)) (p : Fin 20 → Fin 6 → ℕ),
      (∀ v, (U v).card = 3) ∧
      (∀ a, (univ.filter fun v => a ∈ U v).card = 10) ∧
      (∀ v, Function.Injective (p v)) ∧
      (∃ w : Fin 6 → ℝ, (∀ a, 0 ≤ w a) ∧
        (∀ v, (∑ a ∈ U v, w a) ≤ 1) ∧
        ∀ a, ∃ v, a ∈ U v ∧ (∑ b ∈ U v, w b) = 1 ∧
          ∀ b ∈ U v, 0 < w b → p v b ≤ p v a) ∧
      (∀ w : Fin 6 → ℝ, (∀ a, 0 ≤ w a) →
        (∀ v, (∑ a ∈ U v, w a) ≤ 1) →
        (∀ a, ∃ v, a ∈ U v ∧ (∑ b ∈ U v, w b) = 1 ∧
          ∀ b ∈ U v, 0 < w b → p v b ≤ p v a) →
        ∀ a, w a = 1 / 3) ∧
      (∀ w : Fin 6 → ℝ, (∀ a, 0 ≤ w a) →
        (∀ v, (∑ a ∈ U v, w a) ≤ 1) →
        (∀ a, ∃ v, a ∈ U v ∧ (∑ b ∈ U v, w b) = 1 ∧
          ∀ b ∈ U v, 0 < w b → p v b ≤ p v a) →
        ∀ J : Finset (Fin 6), J.card ≤ 3 →
          ∃ v, (∑ a ∈ U v, w a) = 1 ∧ ∀ a ∈ J, a ∉ U v) ∧
      ¬(∀ J : Finset (Fin 6), J.card ≤ 3 →
        ∃ a, a ∉ J ∧ ∀ b ∈ J, condorcet_cover_rank_relation U p a b) := by
  let U := condorcet_stable_gap_sets
  let p := condorcet_stable_gap_rank
  have hcard : ∀ v, (U v).card = 3 := by decide
  have hload : ∀ v, (∑ a ∈ U v, (1 / 3 : ℝ)) = 1 := by
    intro v
    rw [sum_const,hcard]
    norm_num
  refine ⟨U,p,hcard,?_,?_,?_,?_,?_,?_⟩
  · decide
  · decide
  · have hlast : ∀ a, ∃ v, a ∈ U v ∧ ∀ b ∈ U v, p v b ≤ p v a := by decide
    refine ⟨fun _ => 1/3,fun _ => by norm_num,fun v => (hload v).le,?_⟩
    intro a
    obtain ⟨v,hav,hv⟩ := hlast a
    exact ⟨v,hav,hload v,fun b hb _ => hv b hb⟩
  · exact condorcet_stable_gap_uniform
  · have hmiss : ∀ J : Finset (Fin 6), J.card ≤ 3 → ∃ v : Fin 20, ∀ a ∈ J, a ∉ U v := by decide
    intro w hw hc hs J hJ
    obtain ⟨v,hv⟩ := hmiss J hJ
    refine ⟨v,?_,hv⟩
    have heq := condorcet_stable_gap_uniform w hw hc hs
    simp_rw [heq]
    exact hload v
  · unfold condorcet_cover_rank_relation
    decide
