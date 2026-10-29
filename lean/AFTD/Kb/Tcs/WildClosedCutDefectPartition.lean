import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteGraphUpperSubFourAddParity
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# wild_closed_cut_defect_partition

Topic: graphs   Node: 8fb1589c5012

Provenance: helper lemma. Order-independent first-moment helper for the constant-defect structural route in OP-306. Generalizes the accepted n=13 one-defect averaging lemma without asserting that the numerical hypothesis holds at all orders.

For a normalized minimum proper coloring on n vertices, an arbitrary finite family of vertex cuts D_j, and a nonnegative integer r, if n times the sum of d_j! times binomial(floor(n/2),floor(d_j/2)) times (n-d_j)! is strictly less than (r+1)n!, there is a permutation for which at most r cut-color pairs are closed.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1000000

theorem wild_closed_cut_defect_partition {n : ℕ} {J : Type*} [Fintype J]
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n))
    (m : Fin n ≃ Fin n)
    (hm : ∀ (i v : Fin n), (∀ w (hvw : v ≠ w), c ⟨s(v,w),wild_kn_mem hvw⟩ ≠ i) ↔ v = m i)
    (D : J → Finset (Fin n)) (r : ℕ)
    (hmass : n * (∑ j : J, (D j).card.factorial *
      Nat.choose (n/2) ((D j).card/2) * (n-(D j).card).factorial) < (r+1) * n.factorial) :
    ∃ σ : Equiv.Perm (Fin n),
      ((Finset.univ : Finset (J × Fin n)).filter (fun ji =>
        w279_closed c ji.2 ((D ji.1).image σ))).card ≤ r := by
  classical
  by_contra! h
  let Bad (σ : Equiv.Perm (Fin n)) : Finset (J × Fin n) :=
    Finset.univ.filter (fun ji => w279_closed c ji.2 ((D ji.1).image σ))
  have hlo : (r+1) * Nat.factorial n ≤ ∑ σ : Equiv.Perm (Fin n), (Bad σ).card := by
    have hi := Finset.card_nsmul_le_sum (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
      (f := fun σ => (Bad σ).card) (n := r+1) (fun σ _ => by exact h σ)
    rw [nsmul_eq_mul, mul_comm, Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hi
    exact_mod_cast hi
  have heq : (∑ σ : Equiv.Perm (Fin n), (Bad σ).card) =
      ∑ j : J, ∑ i : Fin n,
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => w279_closed c i ((D j).image σ))).card := by
    simp_rw [Bad, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hup : (∑ j : J, ∑ i : Fin n,
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => w279_closed c i ((D j).image σ))).card) ≤
      ∑ j : J, ∑ _i : Fin n, (D j).card.factorial *
        Nat.choose (n/2) ((D j).card/2) * (n-(D j).card).factorial := by
    exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => w3_closed_event_card c m hm (D j) i))
  have heval : (∑ j : J, ∑ _i : Fin n, (D j).card.factorial *
        Nat.choose (n/2) ((D j).card/2) * (n-(D j).card).factorial) =
      n * (∑ j : J, (D j).card.factorial * Nat.choose (n/2) ((D j).card/2) * (n-(D j).card).factorial) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    rfl
  omega
