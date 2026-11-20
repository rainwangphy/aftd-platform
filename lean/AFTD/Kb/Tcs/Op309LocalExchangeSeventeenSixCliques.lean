import AFTD.Prelude

/-!
# op309_local_exchange_seventeen_six_cliques

Topic: combinatorics   Node: d70a129f1205

Provenance: helper lemma. OP-309 ten-vertex local exchange obstruction; experiment 36463.

Each of the seventeen displayed selected-edge patterns forces a six-clique in the finite conflict relation and therefore prohibits five colors, as does every superset.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace In1099Clique

def edges : Fin 15 → (Fin 10 × Fin 10) := ![(0,4), (0,7), (0,9), (1,5), (1,6), (1,7), (2,5), (2,6), (2,8), (3,7), (3,8), (3,9), (4,8), (4,9), (5,6)]

abbrev adjacent (i j : Fin 15) : Prop :=
  i ≠ j ∧ (edges i).1 = (edges j).1 ∨
  i ≠ j ∧ (edges i).1 = (edges j).2 ∨
  i ≠ j ∧ (edges i).2 = (edges j).1 ∨
  i ≠ j ∧ (edges i).2 = (edges j).2

abbrev clash (R : Finset (Fin 15)) (i j : Fin 15) : Prop :=
  i ≠ j ∧ (adjacent i j ∨ ∃ k ∈ R, adjacent k i ∧ adjacent k j)

def certificates : List (Finset (Fin 15) × List (Fin 15)) := [
  ({3, 4}, [3, 4, 5, 6, 7, 14]),
  ({6, 7}, [3, 4, 6, 7, 8, 14]),
  ({0, 2, 10}, [0, 1, 2, 11, 12, 13]),
  ({0, 2, 13}, [0, 1, 2, 11, 12, 13]),
  ({0, 9, 11}, [1, 2, 9, 10, 11, 13]),
  ({0, 9, 13}, [0, 1, 2, 11, 12, 13]),
  ({0, 10, 11}, [2, 9, 10, 11, 12, 13]),
  ({1, 2, 9}, [0, 1, 2, 5, 9, 11]),
  ({1, 2, 11}, [0, 1, 2, 9, 11, 13]),
  ({1, 9, 11}, [1, 2, 5, 9, 10, 11]),
  ({1, 9, 13}, [0, 1, 2, 5, 9, 11]),
  ({2, 9, 11}, [1, 2, 9, 10, 11, 13]),
  ({2, 10, 12}, [0, 8, 10, 11, 12, 13]),
  ({10, 11, 12}, [8, 9, 10, 11, 12, 13]),
  ({10, 11, 13}, [2, 9, 10, 11, 12, 13]),
  ({10, 12, 13}, [0, 8, 10, 11, 12, 13]),
  ({11, 12, 13}, [0, 2, 10, 11, 12, 13])
]

def validCert (p : Finset (Fin 15) × List (Fin 15)) : Bool :=
  decide (p.2.length = 6 ∧ p.2.Pairwise (clash p.1))

theorem all_certificates_valid : certificates.all validCert = true := by decide

theorem clash_mono {S R : Finset (Fin 15)} (hsub : S ⊆ R)
    {i j : Fin 15} (h : clash S i j) : clash R i j := by
  obtain ⟨hne, hadj | ⟨k,hk,hki,hkj⟩⟩ := h
  · exact ⟨hne, Or.inl hadj⟩
  · exact ⟨hne, Or.inr ⟨k,hsub hk,hki,hkj⟩⟩

theorem certificate_forces_no_five_coloring
    (cert : Finset (Fin 15) × List (Fin 15)) (hcert : cert ∈ certificates)
    (R : Finset (Fin 15)) (hsub : cert.1 ⊆ R) (f : Fin 15 → Fin 5)
    (hcolors : ∀ i j, clash R i j → f i ≠ f j) : False := by
  have hv : validCert cert = true := (List.all_eq_true.mp all_certificates_valid) cert hcert
  have hv' : cert.2.length = 6 ∧ cert.2.Pairwise (clash cert.1) := of_decide_eq_true hv
  have hq : cert.2.Pairwise (clash R) := hv'.2.imp (fun h => clash_mono hsub h)
  have hcolors' : (cert.2.map f).Nodup := by
    apply List.pairwise_map.mpr
    exact hq.imp (fun h => hcolors _ _ h)
  have hcard := hcolors'.length_le_card
  simp only [List.length_map, hv'.1, Fintype.card_fin] at hcard
  omega

end In1099Clique

theorem op309_local_exchange_seventeen_six_cliques (cert : Finset (Fin 15) × List (Fin 15)) (hcert : cert ∈ In1099Clique.certificates) (R : Finset (Fin 15)) (hsub : cert.1 ⊆ R) (f : Fin 15 → Fin 5) (hcolors : ∀ i j, In1099Clique.clash R i j → f i ≠ f j) : False := by exact In1099Clique.certificate_forces_no_five_coloring cert hcert R hsub f hcolors
