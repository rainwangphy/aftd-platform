import AFTD.Prelude

/-!
# op309_girth5_portfree_six_clique

Topic: graphs   Node: 3ef81a06bb1d

Provenance: helper lemma. OP-309; girth-five port-free fixed-forest certificate, experiments 41785–41788 and 41796.

The six port-pair constraints and 23 listed inequalities force six distinct colors.
-/

set_option maxRecDepth 10000

theorem op309_girth5_portfree_six_clique
    (x1 x2 x3 x5 x7 x10 x11 x12 x15 x16 x19 x20 x23 x24 x26 x27 x28 : Fin 5)
    (h0 : (x24 = x28) ∨ (x23 = x28))
    (h1 : (x10 = x19 ∧ x11 = x28) ∨ (x10 = x28 ∧ x11 = x19))
    (h2 : (x1 = x5 ∧ x2 = x7) ∨ (x1 = x7 ∧ x2 = x5))
    (h3 : (x3 = x15 ∧ x5 = x16) ∨ (x3 = x16 ∧ x5 = x15))
    (h4 : (x3 = x23 ∧ x12 = x26) ∨ (x3 = x26 ∧ x12 = x23))
    (h5 : (x1 = x11 ∧ x20 = x27) ∨ (x1 = x27 ∧ x20 = x11))
    (n1_2 : x1 ≠ x2)
    (n1_19 : x1 ≠ x19)
    (n1_20 : x1 ≠ x20)
    (n1_24 : x1 ≠ x24)
    (n2_19 : x2 ≠ x19)
    (n2_26 : x2 ≠ x26)
    (n3_5 : x3 ≠ x5)
    (n3_10 : x3 ≠ x10)
    (n3_12 : x3 ≠ x12)
    (n3_16 : x3 ≠ x16)
    (n5_10 : x5 ≠ x10)
    (n7_23 : x7 ≠ x23)
    (n7_24 : x7 ≠ x24)
    (n7_28 : x7 ≠ x28)
    (n10_11 : x10 ≠ x11)
    (n10_12 : x10 ≠ x12)
    (n10_15 : x10 ≠ x15)
    (n11_12 : x11 ≠ x12)
    (n11_24 : x11 ≠ x24)
    (n12_16 : x12 ≠ x16)
    (n12_28 : x12 ≠ x28)
    (n15_20 : x15 ≠ x20)
    (n26_27 : x26 ≠ x27)
    : False := by
  set_option maxHeartbeats 4000000 in
    have hn : ([x2,x19,x23,x26,x27,x28] : List (Fin 5)).Nodup := by
      rcases h3 with ⟨h3a,h3b⟩ | ⟨h3a,h3b⟩
      · rcases h0 with h0a | h0a
        · rcases h1 with ⟨h1a,h1b⟩ | ⟨h1a,h1b⟩
          · simp_all
          · rcases h5 with ⟨h5a,h5b⟩ | ⟨h5a,h5b⟩
            · simp_all
            · rcases h2 with ⟨h2a,h2b⟩ | ⟨h2a,h2b⟩
              · rcases h4 with ⟨h4a,h4b⟩ | ⟨h4a,h4b⟩
                · simp_all [List.nodup_cons, List.mem_cons, ne_comm]
                · simp_all [List.nodup_cons, List.mem_cons, ne_comm]
              · rcases h4 with ⟨h4a,h4b⟩ | ⟨h4a,h4b⟩
                · simp_all [List.nodup_cons, List.mem_cons, ne_comm]
                · simp_all [List.nodup_cons, List.mem_cons, ne_comm]
        · rcases h4 with ⟨h4a,h4b⟩ | ⟨h4a,h4b⟩
          · rcases h1 with ⟨h1a,h1b⟩ | ⟨h1a,h1b⟩
            · rcases h5 with ⟨h5a,h5b⟩ | ⟨h5a,h5b⟩
              · rcases h2 with ⟨h2a,h2b⟩ | ⟨h2a,h2b⟩
                · simp_all
                · simp_all
              · simp_all
            · simp_all
          · simp_all
      · simp_all
    have hlen := hn.length_le_card
    norm_num at hlen
