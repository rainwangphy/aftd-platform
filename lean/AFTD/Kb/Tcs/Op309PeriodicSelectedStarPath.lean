import AFTD.Prelude

/-!
# op309_periodic_selected_star_path

Topic: graphs   Node: 1a6ced0447e1

Provenance: helper lemma. Periodic selected-star path expansion in the proposed four-color compressed-graph argument; experiment 31094.

For any three distinct colors k, 4, q, there is an infinite periodic sequence starting k,4 using only those colors, with distinct colors at distance one or two.
-/

set_option maxHeartbeats 1000000

def op309_periodic_star (k q : Fin 5) (i : ℕ) : Fin 5 :=
  if i % 3 = 0 then k else if i % 3 = 1 then 4 else q

theorem op309_periodic_star_start (k q : Fin 5) :
    op309_periodic_star k q 0 = k ∧ op309_periodic_star k q 1 = 4 := by
  simp [op309_periodic_star]

theorem op309_periodic_star_range (k q : Fin 5) (i : ℕ) :
    op309_periodic_star k q i = k ∨ op309_periodic_star k q i = 4 ∨
      op309_periodic_star k q i = q := by
  unfold op309_periodic_star
  split_ifs <;> simp

theorem op309_periodic_star_strong (k q : Fin 5)
    (hk : k ≠ 4) (hq : q ≠ 4) (hkq : k ≠ q)
    (i j : ℕ) (hij : i < j) (hdist : j ≤ i + 2) :
    op309_periodic_star k q i ≠ op309_periodic_star k q j := by
  have hres : i % 3 ≠ j % 3 := by omega
  unfold op309_periodic_star
  split_ifs <;> simp_all <;> omega

theorem op309_periodic_selected_star_path
    (k q : Fin 5) (hk : k ≠ 4) (hq : q ≠ 4) (hkq : k ≠ q) :
    ∃ c : ℕ → Fin 5, c 0 = k ∧ c 1 = 4 ∧
      (∀ i, c i = k ∨ c i = 4 ∨ c i = q) ∧
      (∀ i j, i < j → j ≤ i + 2 → c i ≠ c j) := by
  refine ⟨op309_periodic_star k q, ?_, ?_, ?_, ?_⟩
  · exact (op309_periodic_star_start k q).1
  · exact (op309_periodic_star_start k q).2
  · exact op309_periodic_star_range k q
  · exact op309_periodic_star_strong k q hk hq hkq
