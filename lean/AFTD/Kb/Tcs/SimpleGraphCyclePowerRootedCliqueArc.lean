import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerCliqueArc

/-!
# simple_graph_cycle_power_rooted_clique_arc

Topic: combinatorics   Node: 3ecfcbdd67dc

Provenance: helper lemma. Uniform actual-cover extraction for OP-205 / RT-1 following arXiv:2610.15635. The anchored-arc lemma is geometric bookkeeping. The saturation helpers double-count exact dyadic owners and active classes over a period; they do not classify class shapes or settle the graph covering value. No research advance is claimed.

Let n,k be natural numbers with n nonzero and n at least3k+1. Let c label the vertices of the k-th cycle power so that two distinct equal-labelled vertices are adjacent. If p and p+k have equal labels, every vertex having the label of p equals p+a for a natural offset a at most k.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_cycle_power_rooted_clique_arc
    (n k : ℕ) [NeZero n] (hn : 3*k+1 ≤ n)
    (c : ZMod n → ZMod n)
    (hc : ∀ u v, u ≠ v → c u = c v → (simple_graph_cycle_power n k).Adj u v)
    (p : ZMod n) (hp : c p = c (p+(k : ZMod n))) :
    ∀ u, c u = c p → ∃ a : ℕ, a ≤ k ∧ u = p+(a : ZMod n) := by
  classical
  let K : Finset (ZMod n) := univ.filter (fun u => c u = c p)
  have hmem (u : ZMod n) : u ∈ K ↔ c u = c p := by simp [K]
  have hK : K.Nonempty := ⟨p, (hmem p).mpr rfl⟩
  have hclique : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → (simple_graph_cycle_power n k).Adj u v := by
    intro u hu v hv hne
    exact hc u v hne (((hmem u).mp hu).trans ((hmem v).mp hv).symm)
  obtain ⟨r, hr, harc⟩ := simple_graph_cycle_power_clique_arc n k hn K hK hclique
  obtain ⟨a, ha, hpa⟩ := harc p ((hmem p).mpr rfl)
  obtain ⟨b, hb, hpb⟩ := harc (p+(k : ZMod n)) ((hmem _).mpr hp.symm)
  have he : ((a+k : ℕ) : ZMod n) = (b : ZMod n) := by
    apply add_left_cancel (a := r)
    calc
      r+((a+k : ℕ) : ZMod n) = (r+(a : ZMod n))+(k : ZMod n) := by push_cast; ring
      _ = p+(k : ZMod n) := by rw [← hpa]
      _ = r+(b : ZMod n) := hpb
  have hen : a+k=b := Nat.ModEq.eq_of_lt_of_lt
    ((ZMod.natCast_eq_natCast_iff (a+k) b n).mp he) (by omega) (by omega)
  have ha0 : a=0 := by omega
  have hpr : p=r := by simpa only [ha0, Nat.cast_zero, add_zero] using hpa
  intro u hu
  obtain ⟨i, hi, hui⟩ := harc u ((hmem u).mpr hu)
  exact ⟨i, hi, by simpa only [hpr] using hui⟩
