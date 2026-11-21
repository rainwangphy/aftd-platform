import AFTD.Prelude

/-!
# op874_bridgeless_local_cut_parity_obstruction

Topic: graphs   Node: 3f9090d7c8f5

Provenance: helper lemma. OP-874: eight-vertex obstruction to the distinct high-difference parity route; experiments 37120 and 37124

There is a connected bridgeless simple cubic graph on eight vertices with the displayed perfect matching and locally maximal matching cut, whose two displayed factor cycles are mixed, yet no three nonzero two-bit labels differ across every matching and same-bit factor edge while having xor zero on the displayed five-cycle.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
private def op874p8_label (d : Fin 3) : ℕ := d.val + 1
private def op874p8_xor5 (a b c d e : Fin 3) : ℕ :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (op874p8_label a) (op874p8_label b))
    (op874p8_label c)) (op874p8_label d)) (op874p8_label e)

private lemma op874p8_kernel : ∀ a b c d e : Fin 3,
    a ≠ b → b ≠ c → c ≠ a → d ≠ e → op874p8_xor5 a b c d e ≠ 0 := by decide

private theorem op874p8_no_labels :
    ¬ ∃ d : Fin 8 → Fin 3,
      (d 1 ≠ d 5 ∧ d 5 ≠ d 4 ∧ d 4 ≠ d 1 ∧ d 2 ≠ d 6) ∧
      op874p8_xor5 (d 1) (d 5) (d 4) (d 2) (d 6) = 0 := by
  rintro ⟨d, ⟨h15, h54, h41, h26⟩, hz⟩
  exact op874p8_kernel (d 1) (d 5) (d 4) (d 2) (d 6) h15 h54 h41 h26 hz


private def op874p8_matching : Finset (Sym2 (Fin 8)) :=
  {s(0,5), s(1,4), s(2,7), s(3,6)}
private def op874p8_factor : Finset (Sym2 (Fin 8)) :=
  {s(0,3), s(3,7), s(7,0), s(1,5), s(5,4), s(4,2), s(2,6), s(6,1)}
private def op874p8_bits : Fin 8 → Bool := ![false,false,true,true,false,false,true,true]
private def op874p8_mate : Fin 8 → Fin 8 := ![5,4,7,6,1,0,3,2]
private def op874p8_same (v : Fin 8) : ℕ :=
  (Finset.univ.filter fun w : Fin 8 => s(v,w) ∈ op874p8_factor ∧ op874p8_bits v = op874p8_bits w).card

private theorem op874p8_data :
    op874p8_matching.card = 4 ∧ op874p8_factor.card = 8 ∧
    Disjoint op874p8_matching op874p8_factor ∧
    (∀ v : Fin 8, (op874p8_matching.filter fun e => v ∈ e).card = 1) ∧
    (∀ v : Fin 8, (op874p8_factor.filter fun e => v ∈ e).card = 2) ∧
    (∀ v : Fin 8, op874p8_mate (op874p8_mate v) = v ∧ op874p8_mate v ≠ v ∧
      s(v,op874p8_mate v) ∈ op874p8_matching ∧
      op874p8_bits v = op874p8_bits (op874p8_mate v) ∧
      op874p8_same v + op874p8_same (op874p8_mate v) ≤ 2) ∧
    (¬ (op874p8_bits 0 = op874p8_bits 3 ∧ op874p8_bits 3 = op874p8_bits 7)) ∧
    (¬ (op874p8_bits 1 = op874p8_bits 5 ∧ op874p8_bits 5 = op874p8_bits 4 ∧
       op874p8_bits 4 = op874p8_bits 2 ∧ op874p8_bits 2 = op874p8_bits 6)) := by decide

private theorem op874p8_constraint_refutation :
    ¬ ∃ d : Fin 8 → Fin 3,
      (∀ u v, (s(u,v) ∈ op874p8_matching ∨
        (s(u,v) ∈ op874p8_factor ∧ op874p8_bits u = op874p8_bits v)) → d u ≠ d v) ∧
      op874p8_xor5 (d 1) (d 5) (d 4) (d 2) (d 6) = 0 := by
  rintro ⟨d, hd, hz⟩
  have h15 : d 1 ≠ d 5 := hd 1 5 (by decide)
  have h54 : d 5 ≠ d 4 := hd 5 4 (by decide)
  have h41 : d 4 ≠ d 1 := hd 4 1 (by decide)
  have h26 : d 2 ≠ d 6 := hd 2 6 (by decide)
  exact op874p8_kernel (d 1) (d 5) (d 4) (d 2) (d 6) h15 h54 h41 h26 hz


private def op874p8_graph : SimpleGraph (Fin 8) where
  Adj u v := u ≠ v ∧ s(u,v) ∈ (op874p8_matching ∪ op874p8_factor)
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

private instance : DecidableRel op874p8_graph.Adj := fun u v => by
  change Decidable (u ≠ v ∧ s(u,v) ∈ (op874p8_matching ∪ op874p8_factor))
  infer_instance

private theorem op874p8_connected : op874p8_graph.Connected := by decide


private theorem op874p8_avoid_edge : ∀ u v : Fin 8,
    (op874p8_graph.deleteEdges {s(u,v)}).Reachable u v := by
  intro u
  fin_cases u <;> decide

private theorem op874p8_bridgeless : ∀ e : Sym2 (Fin 8), ¬ op874p8_graph.IsBridge e := by
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.isBridge_iff, not_not]
    exact op874p8_avoid_edge u v

theorem op874_bridgeless_local_cut_parity_obstruction :
    let M : Finset (Sym2 (Fin 8)) := {s(0,5), s(1,4), s(2,7), s(3,6)}
    let F : Finset (Sym2 (Fin 8)) := {s(0,3), s(3,7), s(7,0), s(1,5), s(5,4), s(4,2), s(2,6), s(6,1)}
    let b : Fin 8 → Bool := ![false,false,true,true,false,false,true,true]
    let mate : Fin 8 → Fin 8 := ![5,4,7,6,1,0,3,2]
    let same := fun v : Fin 8 => (Finset.univ.filter fun w : Fin 8 => s(v,w) ∈ F ∧ b v = b w).card
    let lab := fun d : Fin 3 => d.val + 1
    let xor5 := fun a b c d e : Fin 3 => Nat.xor (Nat.xor (Nat.xor (Nat.xor (lab a) (lab b)) (lab c)) (lab d)) (lab e)
    ∃ G : SimpleGraph (Fin 8),
      G.Connected ∧ (∀ e : Sym2 (Fin 8), ¬ G.IsBridge e) ∧
      (∀ u v, G.Adj u v ↔ u ≠ v ∧ s(u,v) ∈ M ∪ F) ∧
      (M.card = 4 ∧ F.card = 8 ∧ Disjoint M F ∧
        (∀ v : Fin 8, (M.filter fun e => v ∈ e).card = 1) ∧
        (∀ v : Fin 8, (F.filter fun e => v ∈ e).card = 2) ∧
        (∀ v : Fin 8, mate (mate v) = v ∧ mate v ≠ v ∧ s(v,mate v) ∈ M ∧ b v = b (mate v) ∧ same v + same (mate v) ≤ 2) ∧
        (¬ (b 0 = b 3 ∧ b 3 = b 7)) ∧
        (¬ (b 1 = b 5 ∧ b 5 = b 4 ∧ b 4 = b 2 ∧ b 2 = b 6))) ∧
      ¬ ∃ d : Fin 8 → Fin 3,
        (∀ u v, (s(u,v) ∈ M ∨ (s(u,v) ∈ F ∧ b u = b v)) → d u ≠ d v) ∧
        xor5 (d 1) (d 5) (d 4) (d 2) (d 6) = 0 := by
  refine ⟨op874p8_graph, op874p8_connected, op874p8_bridgeless, ?_, op874p8_data, op874p8_constraint_refutation⟩
  intro u v
  rfl
