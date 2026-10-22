import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsMultiRadioLabeling
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# exists_multi_radio_labeling_path

Topic: graphs   Node: 61144796d919

Provenance: helper lemma. step towards simple_graph_multi_radio_number_path_three_of_le

For all n, m, k there is an (m,k)-radio labeling of the path P_n: on vertex v put the m labels (k+1)*(m*v + a) for a < m.
-/

lemma exists_multi_radio_labeling_path_helper (x y a' b' m : ℕ) (ha : a' < m) (hb : b' < m)
    (hne : (x, a') ≠ (y, b')) : m * x + a' ≠ m * y + b' := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have : m * (x + 1) ≤ m * y := Nat.mul_le_mul_left m hlt
    nlinarith
  · subst heq
    intro h
    have : a' = b' := by omega
    exact hne (by rw [this])
  · have : m * (y + 1) ≤ m * x := Nat.mul_le_mul_left m hgt
    nlinarith

lemma exists_multi_radio_labeling_path_diff_ge (k u v : ℕ) (h : u ≠ v) :
    (k + 1 : ℤ) ≤ |(((k + 1) * u : ℕ) : ℤ) - (((k + 1) * v : ℕ) : ℤ)| := by
  push_cast
  rcases lt_trichotomy u v with hlt | heq | hgt
  · have : (u : ℤ) < (v : ℤ) := by exact_mod_cast hlt
    have : (k + 1 : ℤ) * (u : ℤ) < (k + 1 : ℤ) * (v : ℤ) := by
      nlinarith
    rw [abs_of_neg (by linarith)]
    have : (u : ℤ) + 1 ≤ (v : ℤ) := by omega
    nlinarith
  · exact (h heq).elim
  · have : (v : ℤ) < (u : ℤ) := by exact_mod_cast hgt
    have : (k + 1 : ℤ) * (v : ℤ) < (k + 1 : ℤ) * (u : ℤ) := by
      nlinarith
    rw [abs_of_pos (by linarith)]
    have : (v : ℤ) + 1 ≤ (u : ℤ) := by omega
    nlinarith

/-- Existence witness for the (m,k)-radio labeling predicate on paths; supplies nonemptiness of the set whose infimum is the (m,k)-radio number. -/
theorem exists_multi_radio_labeling_path (n m k : ℕ) :
    ∃ f : Fin n → Finset ℕ, simple_graph_is_multi_radio_labeling (SimpleGraph.pathGraph n) m k f := by
  use fun v => (Finset.range m).image (fun a => (k + 1) * (m * v.val + a))
  dsimp [simple_graph_is_multi_radio_labeling]
  constructor
  · intro v
    rw [Finset.card_image_of_injective, Finset.card_range]
    intro a b h
    have h2 := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) h
    omega
  · intro x y a ha b hb hne
    rw [Finset.mem_image] at ha hb
    rcases ha with ⟨a', ha', rfl⟩
    rcases hb with ⟨b', hb', rfl⟩
    rw [Finset.mem_range] at ha' hb'
    have hdiff : m * x.val + a' ≠ m * y.val + b' := by
      apply exists_multi_radio_labeling_path_helper x.val y.val a' b' m ha' hb'
      intro h_eq
      have hxy : x = y := Fin.ext (Prod.mk.inj h_eq).1
      have hab : a' = b' := (Prod.mk.inj h_eq).2
      subst hxy hab
      exact hne rfl
    have hge := exists_multi_radio_labeling_path_diff_ge k (m * x.val + a') (m * y.val + b') hdiff
    have hdist : 0 ≤ ((SimpleGraph.pathGraph n).dist x y : ℤ) := by positivity
    linarith
