import AFTD.Prelude

/-!
# op309_four_pair_conflict_kernel

Topic: graphs   Node: 16e439f1d210

Provenance: helper lemma. OP-309 local P3 port pairing obstruction; experiments 41711-41716.

Four port pair identifications conflict with the listed inequalities.
-/

theorem op309_four_pair_conflict_kernel {α : Type*}
    (x0 x2 x3 x4 x10 x11 x14 x16 x17 x19 x20 : α)
    (h0 : (x0=x11 ∧ x3=x16) ∨ (x0=x16 ∧ x3=x11))
    (h1 : (x4=x14 ∧ x10=x17) ∨ (x4=x17 ∧ x10=x14))
    (h2 : (x0=x10 ∧ x2=x11) ∨ (x0=x11 ∧ x2=x10))
    (h3 : (x16=x19 ∧ x17=x20) ∨ (x16=x20 ∧ x17=x19))
    (n02 : x0≠x2) (n2_17 : x2≠x17) (n3_19 : x3≠x19)
    (n4_19 : x4≠x19) (n16_17 : x16≠x17) (n03 : x0≠x3)
    (n14_19 : x14≠x19) : False := by
  set_option maxHeartbeats 4000000 in
    rcases h0 with ⟨h01,h02⟩ | ⟨h01,h02⟩ <;>
    rcases h1 with ⟨h11,h12⟩ | ⟨h11,h12⟩ <;>
    rcases h2 with ⟨h21,h22⟩ | ⟨h21,h22⟩ <;>
    rcases h3 with ⟨h31,h32⟩ | ⟨h31,h32⟩ <;> simp_all
