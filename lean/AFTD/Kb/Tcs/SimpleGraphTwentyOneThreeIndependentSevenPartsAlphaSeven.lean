import AFTD.Prelude

/-!
# simple_graph_twenty_one_three_independent_seven_parts_alpha_seven

Topic: combinatorics   Node: 25988fb71b1d

Provenance: original. Related work: OP-926, experiment 14350; this witnesses feasibility of the constraints for one triple of outside classes.

There is a triangle-free simple graph on 21 vertices, of maximum degree at most eight, in which each of the three consecutive seven-vertex classes is independent and there is no independent set of eight vertices.
-/

def simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_mask : Nat → Nat
  | 0 => 82944   | 1 => 1839104 | 2 => 21376   | 3 => 800768  | 4 => 1724672
  | 5 => 1425536 | 6 => 1040384 | 7 => 655396  | 8 => 327700  | 9 => 1605636
  | 10 => 524289 | 11 => 213000 | 12 => 65566  | 13 => 1048648| 14 => 2165
  | 15 => 608    | 16 => 6497   | 17 => 2256   | 18 => 362    | 19 => 1754
  | 20 => 8754
  | _ => 0

def simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_graph : SimpleGraph (Fin 21) :=
  SimpleGraph.fromRel (fun u v => (simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_mask u.val).testBit v.val = true)

instance simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_dec :
    DecidableRel simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_graph.Adj :=
  fun a b => by unfold simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_graph SimpleGraph.fromRel; infer_instance

def simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A : Fin 7 → Fin 21 := fun i => ⟨i.val, by omega⟩
def simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B : Fin 7 → Fin 21 := fun i => ⟨i.val + 7, by omega⟩
def simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C : Fin 7 → Fin 21 := fun i => ⟨i.val + 14, by omega⟩

lemma simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A_inj :
    Function.Injective simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A := by
  intro a b h
  have hv : a.val = b.val := by simpa [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A] using congrArg Fin.val h
  exact Fin.ext hv
lemma simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B_inj :
    Function.Injective simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B := by
  intro a b h
  have hv : a.val + 7 = b.val + 7 := by simpa [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B] using congrArg Fin.val h
  exact Fin.ext (by omega)
lemma simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C_inj :
    Function.Injective simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C := by
  intro a b h
  have hv : a.val + 14 = b.val + 14 := by simpa [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C] using congrArg Fin.val h
  exact Fin.ext (by omega)

def simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_NcA (X : Finset (Fin 7)) : Finset (Fin 7) :=
  Finset.univ.filter (fun c => ∃ a ∈ X, simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_graph.Adj (simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A a) (simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C c))
def simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_NcB (Y : Finset (Fin 7)) : Finset (Fin 7) :=
  Finset.univ.filter (fun c => ∃ b ∈ Y, simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_graph.Adj (simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B b) (simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C c))

set_option maxHeartbeats 4000000 in
lemma simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_expansion :
    ∀ X Y : Finset (Fin 7),
      (∀ a ∈ X, ∀ b ∈ Y, ¬ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_graph.Adj (simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A a) (simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B b)) →
      X.card + Y.card ≤ ((simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_NcA X) ∪ (simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_NcB Y)).card := by
  decide

theorem simple_graph_twenty_one_three_independent_seven_parts_alpha_seven :
    ∃ (G : SimpleGraph (Fin 21)) (d : DecidableRel G.Adj),
      letI := d
      (∀ v, G.degree v ≤ 8) ∧
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c) ∧
      (∀ a b, a.val / 7 = b.val / 7 → ¬ G.Adj a b) ∧
      Gᶜ.CliqueFree 8 := by
  refine ⟨simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_graph,
    simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_dec, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · intro t ht
    have hindep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b →
        ¬ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_graph.Adj a b := by
      intro a ha b hb hne
      have hcl := ht.isClique ha hb hne
      rw [SimpleGraph.compl_adj] at hcl
      exact hcl.2
    set X : Finset (Fin 7) := Finset.univ.filter (fun a => simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A a ∈ t) with hXdef
    set Y : Finset (Fin 7) := Finset.univ.filter (fun b => simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B b ∈ t) with hYdef
    set Z : Finset (Fin 7) := Finset.univ.filter (fun c => simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C c ∈ t) with hZdef
    have memX : ∀ a, a ∈ X ↔ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A a ∈ t := by intro a; simp [hXdef]
    have memY : ∀ b, b ∈ Y ↔ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B b ∈ t := by intro b; simp [hYdef]
    have memZ : ∀ c, c ∈ Z ↔ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C c ∈ t := by intro c; simp [hZdef]
    have hcompat : ∀ a ∈ X, ∀ b ∈ Y, ¬ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_graph.Adj (simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A a) (simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B b) := by
      intro a ha b hb
      have hae := (memX a).mp ha
      have hbe := (memY b).mp hb
      have hne : simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A a ≠ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B b := by
        intro h
        have hv := congrArg Fin.val h
        simp only [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A,
          simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B] at hv
        omega
      exact hindep _ hae _ hbe hne
    have hexp := simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_expansion X Y hcompat
    set W : Finset (Fin 7) := simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_NcA X ∪ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_NcB Y with hWdef
    have hZdisj : Disjoint Z W := by
      rw [Finset.disjoint_left]
      intro c hcZ hcW
      have hcCe := (memZ c).mp hcZ
      have hcW' : c ∈ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_NcA X ∪ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_NcB Y := by
        rw [← hWdef]; exact hcW
      rw [Finset.mem_union] at hcW'
      rcases hcW' with hcA | hcB
      · have hcA' : ∃ a ∈ X, simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_graph.Adj (simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A a) (simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C c) := by
          simpa [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_NcA] using hcA
        obtain ⟨a, haX, hadj⟩ := hcA'
        have haAe := (memX a).mp haX
        have hne : simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A a ≠ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C c := by
          intro h
          have hv := congrArg Fin.val h
          simp only [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A,
            simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C] at hv
          omega
        exact hindep _ haAe _ hcCe hne hadj
      · have hcB' : ∃ b ∈ Y, simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_graph.Adj (simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B b) (simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C c) := by
          simpa [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_NcB] using hcB
        obtain ⟨b, hbY, hadj⟩ := hcB'
        have hbBe := (memY b).mp hbY
        have hne : simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B b ≠ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C c := by
          intro h
          have hv := congrArg Fin.val h
          simp only [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B,
            simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C] at hv
          omega
        exact hindep _ hbBe _ hcCe hne hadj
    have hZle : Z.card + W.card ≤ 7 := by
      have hcardu := Finset.card_union_of_disjoint hZdisj
      rw [← hcardu]
      have hsub : Z ∪ W ⊆ (Finset.univ : Finset (Fin 7)) := Finset.subset_univ _
      have hle := Finset.card_le_card hsub
      simpa using hle
    have hpart : t = (t.filter (fun v => v.val < 7)) ∪ (t.filter (fun v => 7 ≤ v.val ∧ v.val < 14)) ∪ (t.filter (fun v => 14 ≤ v.val)) := by
      ext v
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hv
        rcases Nat.lt_or_ge v.val 7 with h | h
        · exact Or.inl (Or.inl ⟨hv, h⟩)
        · rcases Nat.lt_or_ge v.val 14 with h2 | h2
          · exact Or.inl (Or.inr ⟨hv, h, h2⟩)
          · exact Or.inr ⟨hv, h2⟩
      · rintro ((⟨hv, _⟩ | ⟨hv, _, _⟩) | ⟨hv, _⟩) <;> exact hv
    have hd12 : Disjoint (t.filter (fun v => v.val < 7)) (t.filter (fun v => 7 ≤ v.val ∧ v.val < 14)) := by
      rw [Finset.disjoint_left]; intro v hv1 hv2
      simp only [Finset.mem_filter] at hv1 hv2; omega
    have hd13 : Disjoint (t.filter (fun v => v.val < 7)) (t.filter (fun v => 14 ≤ v.val)) := by
      rw [Finset.disjoint_left]; intro v hv1 hv2
      simp only [Finset.mem_filter] at hv1 hv2; omega
    have hd23 : Disjoint (t.filter (fun v => 7 ≤ v.val ∧ v.val < 14)) (t.filter (fun v => 14 ≤ v.val)) := by
      rw [Finset.disjoint_left]; intro v hv1 hv2
      simp only [Finset.mem_filter] at hv1 hv2; omega
    have hd012 : Disjoint ((t.filter (fun v => v.val < 7)) ∪ (t.filter (fun v => 7 ≤ v.val ∧ v.val < 14))) (t.filter (fun v => 14 ≤ v.val)) := by
      rw [Finset.disjoint_left]; intro v hv hv2
      rw [Finset.mem_union] at hv
      rcases hv with hv | hv
      · exact (Finset.disjoint_left.mp hd13) hv hv2
      · exact (Finset.disjoint_left.mp hd23) hv hv2
    have hcardt : t.card = (t.filter (fun v => v.val < 7)).card + (t.filter (fun v => 7 ≤ v.val ∧ v.val < 14)).card + (t.filter (fun v => 14 ≤ v.val)).card := by
      conv_lhs => rw [hpart]
      rw [Finset.card_union_of_disjoint hd012, Finset.card_union_of_disjoint hd12]
    have hXimg : X.image simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A = t.filter (fun v => v.val < 7) := by
      ext v
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, hXdef]
      constructor
      · rintro ⟨a, hae, rfl⟩
        exact ⟨hae, by simpa [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A] using a.isLt⟩
      · rintro ⟨hvt, hv7⟩
        refine ⟨⟨v.val, hv7⟩, ?_, ?_⟩
        · have hh : simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A ⟨v.val, hv7⟩ = v := Fin.ext (by simp [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A])
          rw [hh]; exact hvt
        · exact Fin.ext (by simp [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A])
    have hYimg : Y.image simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B = t.filter (fun v => 7 ≤ v.val ∧ v.val < 14) := by
      ext v
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, hYdef]
      constructor
      · rintro ⟨b, hbe, rfl⟩
        exact ⟨hbe, by simp [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B],
          by have := b.isLt; simp only [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B]; omega⟩
      · rintro ⟨hvt, hv7, hv14⟩
        refine ⟨⟨v.val - 7, by omega⟩, ?_, ?_⟩
        · have hh : simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B ⟨v.val - 7, by omega⟩ = v := Fin.ext (by simp [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B]; omega)
          rw [hh]; exact hvt
        · exact Fin.ext (by simp [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B]; omega)
    have hZimg : Z.image simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C = t.filter (fun v => 14 ≤ v.val) := by
      ext v
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, hZdef]
      constructor
      · rintro ⟨c, hce, rfl⟩
        exact ⟨hce, by simp [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C]⟩
      · rintro ⟨hvt, hv14⟩
        refine ⟨⟨v.val - 14, by omega⟩, ?_, ?_⟩
        · have hh : simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C ⟨v.val - 14, by omega⟩ = v := Fin.ext (by simp [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C]; omega)
          rw [hh]; exact hvt
        · exact Fin.ext (by simp [simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C]; omega)
    have hXcard : (t.filter (fun v => v.val < 7)).card = X.card := by
      rw [← hXimg, Finset.card_image_of_injective _ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_A_inj]
    have hYcard : (t.filter (fun v => 7 ≤ v.val ∧ v.val < 14)).card = Y.card := by
      rw [← hYimg, Finset.card_image_of_injective _ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_B_inj]
    have hZcard : (t.filter (fun v => 14 ≤ v.val)).card = Z.card := by
      rw [← hZimg, Finset.card_image_of_injective _ simple_graph_twenty_one_three_independent_seven_parts_alpha_seven_C_inj]
    have hcard : t.card = X.card + Y.card + Z.card := by
      rw [hcardt, hXcard, hYcard, hZcard]
    have h8 := ht.card_eq
    omega
