import AFTD.Prelude
import AFTD.Kb.Tcs.PerfectMatchingReplaceFinitePairedVertices

/-!
# forced_matching_edge_blocks_four_and_six_switches

Topic: graphs   Node: fb5e00318e16

Provenance: helper lemma. OP-1957 first forced-edge bridge partition.

A forced matching edge blocks the specified four- and six-vertex switches.
-/

theorem forced_matching_edge_blocks_four_and_six_switches {V : Type*} (G : SimpleGraph V)
    (P : G.Subgraph) (hP : P.IsPerfectMatching) (u v : V) (huv : P.Adj u v)
    (hforced : ∀ Q : G.Subgraph, Q.IsPerfectMatching → Q.Adj u v) :
    (¬ ∃ a b, Function.Injective (![u,v,a,b] : Fin 4 → V) ∧ P.Adj a b ∧ G.Adj v a ∧ G.Adj u b) ∧
    (¬ ∃ a b c d, Function.Injective (![u,v,a,b,c,d] : Fin 6 → V) ∧ P.Adj a b ∧ P.Adj c d ∧ G.Adj v b ∧ G.Adj a c ∧ G.Adj u d) := by
  classical
  constructor
  · rintro ⟨a,b,hf,hab,hva,hub⟩
    let f : Fin 4 → V := ![u,v,a,b]
    let τ : Fin 4 → Fin 4 := ![1,0,3,2]
    let σ : Fin 4 → Fin 4 := ![3,2,1,0]
    have hτ : ∀ i, P.Adj (f i) (f (τ i)) := by
      intro i
      fin_cases i <;> simp [f,τ,huv,huv.symm,hab,hab.symm]
    have hσ : ∀ i, σ (σ i) = i := by intro i; fin_cases i <;> simp [σ]
    have hnew : ∀ i, G.Adj (f i) (f (σ i)) := by
      intro i
      fin_cases i <;> simp [f,σ,hva,hva.symm,hub,hub.symm]
    obtain ⟨Q,hQ,-,hQnew⟩ := perfect_matching_replace_finite_paired_vertices G P ⊥ hP bot_le 4 f hf τ σ hτ hσ hnew (by simp)
    have hva' : Q.Adj v a := by simpa [f,σ] using hQnew 1
    have huv' := hforced Q hQ
    have hau : a = u := hQ.1.eq_of_adj_left hva' huv'.symm
    have hneq : a ≠ u := by
      intro h
      have h' : (2 : Fin 4) = 0 := hf (by simpa [f] using h)
      exact (by decide : (2 : Fin 4) ≠ 0) h'
    exact hneq hau
  · rintro ⟨a,b,c,d,hf,hab,hcd,hvb,hac,hud⟩
    let f : Fin 6 → V := ![u,v,a,b,c,d]
    let τ : Fin 6 → Fin 6 := ![1,0,3,2,5,4]
    let σ : Fin 6 → Fin 6 := ![5,3,4,1,2,0]
    have hτ : ∀ i, P.Adj (f i) (f (τ i)) := by
      intro i
      fin_cases i <;> simp [f,τ,huv,huv.symm,hab,hab.symm,hcd,hcd.symm]
    have hσ : ∀ i, σ (σ i) = i := by intro i; fin_cases i <;> simp [σ]
    have hnew : ∀ i, G.Adj (f i) (f (σ i)) := by
      intro i
      fin_cases i <;> simp [f,σ,hvb,hvb.symm,hac,hac.symm,hud,hud.symm]
    obtain ⟨Q,hQ,-,hQnew⟩ := perfect_matching_replace_finite_paired_vertices G P ⊥ hP bot_le 6 f hf τ σ hτ hσ hnew (by simp)
    have hvb' : Q.Adj v b := by simpa [f,σ] using hQnew 1
    have huv' := hforced Q hQ
    have hbu : b = u := hQ.1.eq_of_adj_left hvb' huv'.symm
    have hneq : b ≠ u := by
      intro h
      have h' : (3 : Fin 6) = 0 := hf (by simpa [f] using h)
      exact (by decide : (3 : Fin 6) ≠ 0) h'
    exact hneq hbu
