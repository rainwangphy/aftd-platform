import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphOrientedRegularCut20Extension
import AFTD.Kb.Tcs.DigraphOrientedCut20SharpExampleCertificate
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphOrientedCut20SharpExample

/-!
# digraph_oriented_regular_cut20_extension_certificate

Topic: graphs   Node: a5ca17b15a4a

Provenance: helper lemma. Finite construction and checks in experiment 26337; the independent set records the limitation for the critical reduction.

The extended example is oriented, seven-outregular, arc-dominated and strongly connected, with a twenty-vertex part of cut twenty and no two disjoint cycles; its common-predecessor graph has an independent set of four.
-/

private instance in833_regular_extension_decAdj : DecidableRel digraph_oriented_regular_cut20_extension.Adj := by
  unfold digraph_oriented_regular_cut20_extension
  infer_instance

open Relation

def to26 (x : Fin 104) : Fin 26 :=
  if h : x.val < 26 then ⟨x.val, h⟩ else 0

lemma to26_val {x : Fin 104} (h : x.val < 20) : (to26 x).val = x.val := by
  dsimp [to26]
  have : x.val < 26 := by omega
  rw [dif_pos this]

theorem adj_agree :
    ∀ (u v : Fin 104), u.val < 20 → v.val < 20 →
    (digraph_oriented_regular_cut20_extension.Adj u v ↔
     digraph_oriented_cut20_sharp_example.Adj (to26 u) (to26 v)) := by
  intro u v hu hv
  have h1 := to26_val hu
  have h2 := to26_val hv
  dsimp [digraph_oriented_regular_cut20_extension, digraph_oriented_cut20_sharp_example]
  rw [h1, h2]
  have hu20 : ¬ (20 ≤ u.val) := by omega
  simp [hu20]

lemma to26_injOn_B : Set.InjOn to26 {x : Fin 104 | x.val < 20} := by
  intro u hu v hv heq
  apply Fin.ext
  rw [← to26_val (show u.val < 20 from hu), ← to26_val (show v.val < 20 from hv)]
  exact congrArg Fin.val heq

lemma cycle_transfer (s : Finset (Fin 104))
    (hs : ∀ x ∈ s, x.val < 20)
    (hc : digraph_directed_cycle_on digraph_oriented_regular_cut20_extension s) :
    digraph_directed_cycle_on digraph_oriented_cut20_sharp_example (s.image to26) := by
  rcases hc with ⟨l, hnodup, hlen, hto, hchain, a, b, hhead, hlast, hadj⟩
  have hmem : ∀ x ∈ l, x ∈ s := fun x hx => by rw [← hto]; exact List.mem_toFinset.mpr hx
  have hsub' : ∀ x ∈ l, x.val < 20 := fun x hx => hs x (hmem x hx)
  refine ⟨l.map to26, ?_, ?_, ?_, ?_, to26 a, to26 b, ?_, ?_, ?_⟩
  · exact List.Nodup.map_on (fun x hx y hy hxy => to26_injOn_B (hsub' x hx) (hsub' y hy) hxy) hnodup
  · rwa [List.length_map]
  · ext y
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hmem x hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; rw [← hto] at hx; exact ⟨x, List.mem_toFinset.mp hx, rfl⟩
  · rw [List.isChain_map]
    apply List.IsChain.imp_of_mem_imp _ hchain
    intro x y hx hy hxy
    rwa [← adj_agree x y (hsub' x hx) (hsub' y hy)]
  · rw [List.head?_map, hhead]; rfl
  · rw [List.getLast?_map, hlast]; rfl
  · have ha : a.val < 20 := hsub' a (List.mem_of_mem_head? hhead)
    have hb : b.val < 20 := hsub' b (List.mem_of_mem_getLast? hlast)
    rwa [← adj_agree b a hb ha]

def leaders : Finset (Fin 104) := {0, 20, 27, 34, 41, 48, 55, 62, 69, 76, 83, 90, 97}

lemma reflTransGen_leaders (v : Fin 104) (hv : v ∈ leaders) :
    ReflTransGen digraph_oriented_regular_cut20_extension.Adj 0 v := by
  have a0_20 : digraph_oriented_regular_cut20_extension.Adj 0 20 := by decide
  have a20_27 : digraph_oriented_regular_cut20_extension.Adj 20 27 := by decide
  have a27_34 : digraph_oriented_regular_cut20_extension.Adj 27 34 := by decide
  have a34_41 : digraph_oriented_regular_cut20_extension.Adj 34 41 := by decide
  have a41_48 : digraph_oriented_regular_cut20_extension.Adj 41 48 := by decide
  have a48_55 : digraph_oriented_regular_cut20_extension.Adj 48 55 := by decide
  have a55_62 : digraph_oriented_regular_cut20_extension.Adj 55 62 := by decide
  have a62_69 : digraph_oriented_regular_cut20_extension.Adj 62 69 := by decide
  have a69_76 : digraph_oriented_regular_cut20_extension.Adj 69 76 := by decide
  have a76_83 : digraph_oriented_regular_cut20_extension.Adj 76 83 := by decide
  have a83_90 : digraph_oriented_regular_cut20_extension.Adj 83 90 := by decide
  have a90_97 : digraph_oriented_regular_cut20_extension.Adj 90 97 := by decide
  have p0 : ReflTransGen digraph_oriented_regular_cut20_extension.Adj 0 0 := ReflTransGen.refl
  have p20 : ReflTransGen digraph_oriented_regular_cut20_extension.Adj 0 20 := ReflTransGen.single a0_20
  have p27 := p20.trans (ReflTransGen.single a20_27)
  have p34 := p27.trans (ReflTransGen.single a27_34)
  have p41 := p34.trans (ReflTransGen.single a34_41)
  have p48 := p41.trans (ReflTransGen.single a41_48)
  have p55 := p48.trans (ReflTransGen.single a48_55)
  have p62 := p55.trans (ReflTransGen.single a55_62)
  have p69 := p62.trans (ReflTransGen.single a62_69)
  have p76 := p69.trans (ReflTransGen.single a69_76)
  have p83 := p76.trans (ReflTransGen.single a76_83)
  have p90 := p83.trans (ReflTransGen.single a83_90)
  have p97 := p90.trans (ReflTransGen.single a90_97)
  simp only [leaders, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

lemma reflTransGen_all (u v : Fin 104) :
    ReflTransGen digraph_oriented_regular_cut20_extension.Adj u v := by
  have hto : ∀ u : Fin 104, u = 0 ∨ digraph_oriented_regular_cut20_extension.Adj u 0 ∨
      (∃ w : Fin 104, digraph_oriented_regular_cut20_extension.Adj u w ∧ digraph_oriented_regular_cut20_extension.Adj w 0) ∨
      (∃ w₁ : Fin 104, ∃ w₂ : Fin 104, digraph_oriented_regular_cut20_extension.Adj u w₁ ∧ digraph_oriented_regular_cut20_extension.Adj w₁ w₂ ∧ digraph_oriented_regular_cut20_extension.Adj w₂ 0) := by decide
  have hfrom : ∀ v : Fin 104, (v ∈ leaders) ∨ (∃ s ∈ leaders, digraph_oriented_regular_cut20_extension.Adj s v) ∨
      (∃ s ∈ leaders, ∃ w : Fin 104, digraph_oriented_regular_cut20_extension.Adj s w ∧ digraph_oriented_regular_cut20_extension.Adj w v) := by decide
  have u_to_0 : ReflTransGen digraph_oriented_regular_cut20_extension.Adj u 0 := by
    rcases hto u with rfl | h1 | ⟨w, h1, h2⟩ | ⟨w₁, w₂, h1, h2, h3⟩
    · exact ReflTransGen.refl
    · exact ReflTransGen.single h1
    · exact (ReflTransGen.single h1).tail h2
    · exact ((ReflTransGen.single h1).tail h2).tail h3
  have zero_to_v : ReflTransGen digraph_oriented_regular_cut20_extension.Adj 0 v := by
    rcases hfrom v with hv | ⟨s, hs, h1⟩ | ⟨s, hs, w, h1, h2⟩
    · exact reflTransGen_leaders v hv
    · exact (reflTransGen_leaders s hs).tail h1
    · exact ((reflTransGen_leaders s hs).tail h1).tail h2
  exact u_to_0.trans zero_to_v

theorem digraph_oriented_regular_cut20_extension_certificate :
    let D := digraph_oriented_regular_cut20_extension
    let B : Finset (Fin 104) := Finset.univ.filter fun v => v.val < 20
    let I : Finset (Fin 104) := {0,13,28,35}
    (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
    (∀ v, (Finset.univ.filter fun w => D.Adj v w).card = 7) ∧
    (∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v) ∧
    (∀ u v, Relation.ReflTransGen D.Adj u v) ∧
    (∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card) = 20 ∧
    (¬ ∃ c : Fin 2 → Finset (Fin 104), (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j))) ∧
    (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ ∃ w, D.Adj w u ∧ D.Adj w v) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · exact reflTransGen_all
  · decide
  · rintro ⟨c, hcyc, hdisj⟩
    refine digraph_oriented_cut20_sharp_example_certificate.2.2.2.1
      ⟨fun i => (c i).image to26, ?_, ?_⟩
    · intro i
      exact cycle_transfer (c i)
        (fun x hx => by have := (hcyc i).1 hx; simpa using this) (hcyc i).2
    · intro i j hij
      refine Finset.disjoint_left.2 fun x hx1 hx2 => ?_
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx1
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.1 hx2
      have hia : a.val < 20 := by have := (hcyc i).1 ha; simpa using this
      have hjb : b.val < 20 := by have := (hcyc j).1 hb; simpa using this
      have hab : a = b := to26_injOn_B hia hjb hba.symm
      have hdis : Disjoint (c i) (c j) := hdisj hij
      rw [← hab] at hb
      exact (Finset.disjoint_left.1 hdis ha) hb
  · decide
