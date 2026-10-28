import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a00

Topic: combinatorics   Node: 9efdf1eba7b9

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_six_iff_seven_core: under the layer-free tight-cover constraints for k = 15 and 48 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a00_aux (x : ℤ → Fin 16 → Bool)
    (hcount : ∀ u : ℤ, (x (u - 1) 1).toNat + (x (u - 2) 2).toNat + (x (u - 3) 3).toNat + (x (u - 4) 4).toNat + (x (u - 5) 5).toNat + (x (u - 6) 6).toNat + (x (u - 7) 7).toNat + (x (u - 8) 8).toNat + (x (u - 9) 9).toNat + (x (u - 10) 10).toNat + (x (u - 11) 11).toNat + (x (u - 12) 12).toNat + (x (u - 13) 13).toNat + (x (u - 14) 14).toNat = 3)
    (hd14 : ∀ u : ℤ, (x u 14).toNat + (x (u - 1) 1).toNat = 1)
    (hd12 : ∀ u : ℤ, (x u 12).toNat + (x (u - 1) 1 && x (u - 1) 13).toNat + (x (u - 2) 2 && x (u - 2) 14).toNat + (x (u - 3) 3).toNat = 1)
    (hd8 : ∀ u : ℤ, (x u 8).toNat + (x (u - 1) 1 && x (u - 1) 9).toNat + (x (u - 2) 2 && x (u - 2) 10).toNat + (x (u - 3) 3 && x (u - 3) 11).toNat + (x (u - 4) 4 && x (u - 4) 12).toNat + (x (u - 5) 5 && x (u - 5) 13).toNat + (x (u - 6) 6 && x (u - 6) 14).toNat + (x (u - 7) 7).toNat = 1)
    (hcov1 : ∀ u : ℤ, 1 ≤ (x u 1).toNat + (x (u - 1) 1 && x (u - 1) 2).toNat + (x (u - 2) 2 && x (u - 2) 3).toNat + (x (u - 3) 3 && x (u - 3) 4).toNat + (x (u - 4) 4 && x (u - 4) 5).toNat + (x (u - 5) 5 && x (u - 5) 6).toNat + (x (u - 6) 6 && x (u - 6) 7).toNat + (x (u - 7) 7 && x (u - 7) 8).toNat + (x (u - 8) 8 && x (u - 8) 9).toNat + (x (u - 9) 9 && x (u - 9) 10).toNat + (x (u - 10) 10 && x (u - 10) 11).toNat + (x (u - 11) 11 && x (u - 11) 12).toNat + (x (u - 12) 12 && x (u - 12) 13).toNat + (x (u - 13) 13 && x (u - 13) 14).toNat + (x (u - 14) 14).toNat)
    (hcov2 : ∀ u : ℤ, 1 ≤ (x u 2).toNat + (x (u - 1) 1 && x (u - 1) 3).toNat + (x (u - 2) 2 && x (u - 2) 4).toNat + (x (u - 3) 3 && x (u - 3) 5).toNat + (x (u - 4) 4 && x (u - 4) 6).toNat + (x (u - 5) 5 && x (u - 5) 7).toNat + (x (u - 6) 6 && x (u - 6) 8).toNat + (x (u - 7) 7 && x (u - 7) 9).toNat + (x (u - 8) 8 && x (u - 8) 10).toNat + (x (u - 9) 9 && x (u - 9) 11).toNat + (x (u - 10) 10 && x (u - 10) 12).toNat + (x (u - 11) 11 && x (u - 11) 13).toNat + (x (u - 12) 12 && x (u - 12) 14).toNat + (x (u - 13) 13).toNat)
    (hcov3 : ∀ u : ℤ, 1 ≤ (x u 3).toNat + (x (u - 1) 1 && x (u - 1) 4).toNat + (x (u - 2) 2 && x (u - 2) 5).toNat + (x (u - 3) 3 && x (u - 3) 6).toNat + (x (u - 4) 4 && x (u - 4) 7).toNat + (x (u - 5) 5 && x (u - 5) 8).toNat + (x (u - 6) 6 && x (u - 6) 9).toNat + (x (u - 7) 7 && x (u - 7) 10).toNat + (x (u - 8) 8 && x (u - 8) 11).toNat + (x (u - 9) 9 && x (u - 9) 12).toNat + (x (u - 10) 10 && x (u - 10) 13).toNat + (x (u - 11) 11 && x (u - 11) 14).toNat + (x (u - 12) 12).toNat)
    (hcov4 : ∀ u : ℤ, 1 ≤ (x u 4).toNat + (x (u - 1) 1 && x (u - 1) 5).toNat + (x (u - 2) 2 && x (u - 2) 6).toNat + (x (u - 3) 3 && x (u - 3) 7).toNat + (x (u - 4) 4 && x (u - 4) 8).toNat + (x (u - 5) 5 && x (u - 5) 9).toNat + (x (u - 6) 6 && x (u - 6) 10).toNat + (x (u - 7) 7 && x (u - 7) 11).toNat + (x (u - 8) 8 && x (u - 8) 12).toNat + (x (u - 9) 9 && x (u - 9) 13).toNat + (x (u - 10) 10 && x (u - 10) 14).toNat + (x (u - 11) 11).toNat)
    (hcov5 : ∀ u : ℤ, 1 ≤ (x u 5).toNat + (x (u - 1) 1 && x (u - 1) 6).toNat + (x (u - 2) 2 && x (u - 2) 7).toNat + (x (u - 3) 3 && x (u - 3) 8).toNat + (x (u - 4) 4 && x (u - 4) 9).toNat + (x (u - 5) 5 && x (u - 5) 10).toNat + (x (u - 6) 6 && x (u - 6) 11).toNat + (x (u - 7) 7 && x (u - 7) 12).toNat + (x (u - 8) 8 && x (u - 8) 13).toNat + (x (u - 9) 9 && x (u - 9) 14).toNat + (x (u - 10) 10).toNat)
    (hcov6 : ∀ u : ℤ, 1 ≤ (x u 6).toNat + (x (u - 1) 1 && x (u - 1) 7).toNat + (x (u - 2) 2 && x (u - 2) 8).toNat + (x (u - 3) 3 && x (u - 3) 9).toNat + (x (u - 4) 4 && x (u - 4) 10).toNat + (x (u - 5) 5 && x (u - 5) 11).toNat + (x (u - 6) 6 && x (u - 6) 12).toNat + (x (u - 7) 7 && x (u - 7) 13).toNat + (x (u - 8) 8 && x (u - 8) 14).toNat + (x (u - 9) 9).toNat)
    (hcov7 : ∀ u : ℤ, 1 ≤ (x u 7).toNat + (x (u - 1) 1 && x (u - 1) 8).toNat + (x (u - 2) 2 && x (u - 2) 9).toNat + (x (u - 3) 3 && x (u - 3) 10).toNat + (x (u - 4) 4 && x (u - 4) 11).toNat + (x (u - 5) 5 && x (u - 5) 12).toNat + (x (u - 6) 6 && x (u - 6) 13).toNat + (x (u - 7) 7 && x (u - 7) 14).toNat + (x (u - 8) 8).toNat)
    (hcov9 : ∀ u : ℤ, 1 ≤ (x u 9).toNat + (x (u - 1) 1 && x (u - 1) 10).toNat + (x (u - 2) 2 && x (u - 2) 11).toNat + (x (u - 3) 3 && x (u - 3) 12).toNat + (x (u - 4) 4 && x (u - 4) 13).toNat + (x (u - 5) 5 && x (u - 5) 14).toNat + (x (u - 6) 6).toNat)
    (hcov10 : ∀ u : ℤ, 1 ≤ (x u 10).toNat + (x (u - 1) 1 && x (u - 1) 11).toNat + (x (u - 2) 2 && x (u - 2) 12).toNat + (x (u - 3) 3 && x (u - 3) 13).toNat + (x (u - 4) 4 && x (u - 4) 14).toNat + (x (u - 5) 5).toNat)
    (hcov11 : ∀ u : ℤ, 1 ≤ (x u 11).toNat + (x (u - 1) 1 && x (u - 1) 12).toNat + (x (u - 2) 2 && x (u - 2) 13).toNat + (x (u - 3) 3 && x (u - 3) 14).toNat + (x (u - 4) 4).toNat)
    (hcov13 : ∀ u : ℤ, 1 ≤ (x u 13).toNat + (x (u - 1) 1 && x (u - 1) 14).toNat + (x (u - 2) 2).toNat)
    (hp2 : ∀ p, x p 2 = true → x p 14 = true)
    (hp4 : ∀ p, x p 4 = true → x p 12 = true)
    (hp5 : ∀ p, x p 5 = true → x p 13 = true)
    (hp6 : ∀ p, x p 6 = true → x p 14 = true)
    (hp9 : ∀ p, x p 9 = true → x p 1 = true)
    (hp10 : ∀ p, x p 10 = true → x p 2 = true)
    (hp11 : ∀ p, x p 11 = true → x p 3 = true)
    (hp13 : ∀ p, x p 13 = true → x p 1 = true)
    (g0 : (x (-1) 5).toNat = 0)
    (g1 : (x (-1) 9).toNat = 0)
    (g2 : (x (-1) 13).toNat = 0)
    (g3 : (x 0 3).toNat = 0)
    (g4 : (x 0 7).toNat = 0)
    (g5 : (x 0 11).toNat = 0)
    (g6 : (x 0 13).toNat = 0)
    (g7 : (x 0 14).toNat = 1)
    (g8 : (x 1 5).toNat = 0)
    (g9 : (x 2 4).toNat = 0)
    (g10 : (x 3 11).toNat = 0)
    (g11 : (x 4 10).toNat = 0)
    (g12 : (x 5 9).toNat = 0)
    (g13 : (x 6 8).toNat = 0)
    (g14 : (x 6 7 && x 6 8).toNat = 0)
    (g15 : (x 5 8 && x 5 9).toNat = 0)
    (g16 : (x 4 9 && x 4 10).toNat = 0)
    (g17 : (x 3 10 && x 3 11).toNat = 0)
    (g18 : (x 2 4 && x 2 8).toNat = 0)
    (g19 : (x 1 5 && x 1 9).toNat = 0)
    (g20 : (x (-1) 7 && x (-1) 11).toNat = 0)
    (g21 : (x 6 4 && x 6 8).toNat = 0)
    (g22 : (x 5 5 && x 5 9).toNat = 0)
    (g23 : (x 4 6 && x 4 10).toNat = 0)
    (g24 : (x 3 7 && x 3 11).toNat = 0)
    (g25 : (x 0 3 && x 0 8).toNat = 0)
    (g26 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g27 : (x 6 3 && x 6 8).toNat = 0)
    (g28 : (x 5 4 && x 5 9).toNat = 0)
    (g29 : (x 4 5 && x 4 10).toNat = 0)
    (g30 : (x 3 6 && x 3 11).toNat = 0)
    (g31 : (x 6 2 && x 6 8).toNat = 0)
    (g32 : (x 5 3 && x 5 9).toNat = 0)
    (g33 : (x 4 4 && x 4 10).toNat = 0)
    (g34 : (x 3 5 && x 3 11).toNat = 0)
    (g35 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g36 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g37 : (x 0 3 && x 0 12).toNat = 0)
    (g38 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g39 : (x 4 1 && x 4 10).toNat = 0)
    (g40 : (x 3 2 && x 3 11).toNat = 0)
    (g41 : (x 0 1 && x 0 11).toNat = 0)
    (g42 : (x 3 1 && x 3 11).toNat = 0)
    (g43 : (x 2 4 && x 2 14).toNat = 0)
    (g44 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g45 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g46 : (x 0 3 && x 0 14).toNat = 0)
    (g47 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d27891 : (x 0 2 && x 0 13).toNat = 0 := by
    have r27892 := hand2 (x 0 2) (x 0 13)
    have b27893 := hb (x 0 13)
    have b27894 := hb (x 0 2 && x 0 13)
    clear * - r27892 b27893 b27894 g6
    omega
  have d27895 : (x 0 13 && x 0 14).toNat = 0 := by
    have r27896 := hand1 (x 0 13) (x 0 14)
    have b27897 := hb (x 0 13)
    have b27898 := hb (x 0 13 && x 0 14)
    clear * - r27896 b27897 b27898 g6
    omega
  have d27899 : (x 0 5).toNat = 0 := by
    have r27900 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
    have b27901 := hb (x 0 5)
    have b27902 := hb (x 0 13)
    clear * - r27900 b27901 b27902 g6
    omega
  have d27903 : (x 0 5 && x 0 14).toNat = 0 := by
    have r27904 := hand1 (x 0 5) (x 0 14)
    have b27905 := hb (x 0 5)
    have b27906 := hb (x 0 5 && x 0 14)
    clear * - r27904 b27905 b27906 d27899
    omega
  have d27907 : (x 0 5 && x 0 9).toNat = 0 := by
    have r27908 := hand1 (x 0 5) (x 0 9)
    have b27909 := hb (x 0 5)
    have b27910 := hb (x 0 5 && x 0 9)
    clear * - r27908 b27909 b27910 d27899
    omega
  have d27911 : (x (-2) 2).toNat = 1 := by
    have r27912 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27913 := hb (x (-2) 2)
    have b27914 := hb (x 0 13)
    have b27915 := hb (x (-1) 1 && x (-1) 14)
    clear * - r27912 b27913 b27914 b27915 g6 g47
    omega
  have d27916 : (x (-2) 14).toNat = 1 := by
    have r27917 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
    have b27918 := hb (x (-2) 2)
    have b27919 := hb (x (-2) 14)
    clear * - r27917 b27918 b27919 d27911
    omega
  have d27920 : (x (-3) 1).toNat = 0 := by
    have r27921 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27922 := hb (x (-3) 1)
    have b27923 := hb (x (-2) 14)
    clear * - r27921 b27922 b27923 d27916
    omega
  have d27924 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
    have r27925 := hand1 (x (-3) 1) (x (-3) 14)
    have b27926 := hb (x (-3) 1)
    have b27927 := hb (x (-3) 1 && x (-3) 14)
    clear * - r27925 b27926 b27927 d27920
    omega
  have d27928 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
    have r27929 := hand1 (x (-3) 1) (x (-3) 12)
    have b27930 := hb (x (-3) 1)
    have b27931 := hb (x (-3) 1 && x (-3) 12)
    clear * - r27929 b27930 b27931 d27920
    omega
  have d27932 : (x (-3) 13).toNat = 0 := by
    have r27933 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b27934 := hb (x (-3) 1)
    have b27935 := hb (x (-3) 13)
    clear * - r27933 b27934 b27935 d27920
    omega
  have d27936 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
    have r27937 := hand2 (x (-3) 2) (x (-3) 13)
    have b27938 := hb (x (-3) 13)
    have b27939 := hb (x (-3) 2 && x (-3) 13)
    clear * - r27937 b27938 b27939 d27932
    omega
  have d27940 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
    have r27941 := hand2 (x (-3) 4) (x (-3) 13)
    have b27942 := hb (x (-3) 13)
    have b27943 := hb (x (-3) 4 && x (-3) 13)
    clear * - r27941 b27942 b27943 d27932
    omega
  have d27944 : (x (-3) 9 && x (-3) 13).toNat = 0 := by
    have r27945 := hand2 (x (-3) 9) (x (-3) 13)
    have b27946 := hb (x (-3) 13)
    have b27947 := hb (x (-3) 9 && x (-3) 13)
    clear * - r27945 b27946 b27947 d27932
    omega
  have d27948 : (x (-3) 9).toNat = 0 := by
    have r27949 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
    have b27950 := hb (x (-3) 1)
    have b27951 := hb (x (-3) 9)
    clear * - r27949 b27950 b27951 d27920
    omega
  have d27952 : (x 0 12).toNat = 0 := by
    have r27953 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27954 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e27955 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b27956 := hb (x (-3) 3)
    have b27957 := hb (x (-2) 2)
    have b27958 := hb (x (-1) 13)
    have b27959 := hb (x 0 12)
    clear * - r27953 e27954 e27955 b27956 b27957 b27958 b27959 g2 d27911
    omega
  have d27960 : (x 0 1 && x 0 12).toNat = 0 := by
    have r27961 := hand2 (x 0 1) (x 0 12)
    have b27962 := hb (x 0 12)
    have b27963 := hb (x 0 1 && x 0 12)
    clear * - r27961 b27962 b27963 d27952
    omega
  have d27964 : (x 0 4).toNat = 0 := by
    have r27965 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b27966 := hb (x 0 4)
    have b27967 := hb (x 0 12)
    clear * - r27965 b27966 b27967 d27952
    omega
  have d27968 : (x 0 4 && x 0 14).toNat = 0 := by
    have r27969 := hand1 (x 0 4) (x 0 14)
    have b27970 := hb (x 0 4)
    have b27971 := hb (x 0 4 && x 0 14)
    clear * - r27969 b27970 b27971 d27964
    omega
  have d27972 : (x (-3) 3).toNat = 0 := by
    have r27973 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27974 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e27975 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b27976 := hb (x (-3) 3)
    have b27977 := hb (x (-2) 2)
    have b27978 := hb (x (-1) 13)
    have b27979 := hb (x 0 12)
    clear * - r27973 e27974 e27975 b27976 b27977 b27978 b27979 d27952 g2 d27911
    omega
  have d27980 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r27981 := hand1 (x (-3) 3) (x (-3) 14)
    have b27982 := hb (x (-3) 3)
    have b27983 := hb (x (-3) 3 && x (-3) 14)
    clear * - r27981 b27982 b27983 d27972
    omega
  have d27984 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
    have r27985 := hand1 (x (-3) 3) (x (-3) 12)
    have b27986 := hb (x (-3) 3)
    have b27987 := hb (x (-3) 3 && x (-3) 12)
    clear * - r27985 b27986 b27987 d27972
    omega
  have d27988 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
    have r27989 := hand1 (x (-3) 3) (x (-3) 10)
    have b27990 := hb (x (-3) 3)
    have b27991 := hb (x (-3) 3 && x (-3) 10)
    clear * - r27989 b27990 b27991 d27972
    omega
  have d27992 : (x (-3) 3 && x (-3) 7).toNat = 0 := by
    have r27993 := hand1 (x (-3) 3) (x (-3) 7)
    have b27994 := hb (x (-3) 3)
    have b27995 := hb (x (-3) 3 && x (-3) 7)
    clear * - r27993 b27994 b27995 d27972
    omega
  have d27996 : (x (-3) 11).toNat = 0 := by
    have r27997 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b27998 := hb (x (-3) 3)
    have b27999 := hb (x (-3) 11)
    clear * - r27997 b27998 b27999 d27972
    omega
  have d28000 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
    have r28001 := hand2 (x (-3) 2) (x (-3) 11)
    have b28002 := hb (x (-3) 11)
    have b28003 := hb (x (-3) 2 && x (-3) 11)
    clear * - r28001 b28002 b28003 d27996
    omega
  have d28004 : (x (-3) 6 && x (-3) 11).toNat = 0 := by
    have r28005 := hand2 (x (-3) 6) (x (-3) 11)
    have b28006 := hb (x (-3) 11)
    have b28007 := hb (x (-3) 6 && x (-3) 11)
    clear * - r28005 b28006 b28007 d27996
    omega
  cases h28008 : x 0 1
  · have f28009 : (x 0 1).toNat = 0 := by rw [h28008]; rfl
    have d28010 : (x 0 1 && x 0 14).toNat = 0 := by
      have r28011 := hand1 (x 0 1) (x 0 14)
      have b28012 := hb (x 0 1)
      have b28013 := hb (x 0 1 && x 0 14)
      clear * - r28011 b28012 b28013 f28009
      omega
    have d28014 : (x 0 9).toNat = 0 := by
      have r28015 : (x 0 9).toNat ≤ (x 0 1).toNat := himp _ _ (hp9 0)
      have b28016 := hb (x 0 1)
      have b28017 := hb (x 0 9)
      clear * - r28015 b28016 b28017 f28009
      omega
    cases h28018 : x 0 2
    · have f28019 : (x 0 2).toNat = 0 := by rw [h28018]; rfl
      cases h28020 : x 0 8
      · have f28021 : (x 0 8).toNat = 0 := by rw [h28020]; rfl
        have d28022 : (x 0 8 && x 0 14).toNat = 0 := by
          have r28023 := hand1 (x 0 8) (x 0 14)
          have b28024 := hb (x 0 8)
          have b28025 := hb (x 0 8 && x 0 14)
          clear * - r28023 b28024 b28025 f28021
          omega
        cases h28026 : x 1 1
        · have f28027 : (x 1 1).toNat = 0 := by rw [h28026]; rfl
          have d28028 : (x 1 1 && x 1 14).toNat = 0 := by
            have r28029 := hand1 (x 1 1) (x 1 14)
            have b28030 := hb (x 1 1)
            have b28031 := hb (x 1 1 && x 1 14)
            clear * - r28029 b28030 b28031 f28027
            omega
          have d28032 : (x 1 1 && x 1 12).toNat = 0 := by
            have r28033 := hand1 (x 1 1) (x 1 12)
            have b28034 := hb (x 1 1)
            have b28035 := hb (x 1 1 && x 1 12)
            clear * - r28033 b28034 b28035 f28027
            omega
          have d28036 : (x 1 13).toNat = 0 := by
            have r28037 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
            have b28038 := hb (x 1 1)
            have b28039 := hb (x 1 13)
            clear * - r28037 b28038 b28039 f28027
            omega
          have d28040 : (x 1 2 && x 1 13).toNat = 0 := by
            have r28041 := hand2 (x 1 2) (x 1 13)
            have b28042 := hb (x 1 13)
            have b28043 := hb (x 1 2 && x 1 13)
            clear * - r28041 b28042 b28043 d28036
            omega
          have d28044 : (x 2 13).toNat = 1 := by
            have r28045 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28046 := hb (x 0 2)
            have b28047 := hb (x 2 13)
            have b28048 := hb (x 1 1 && x 1 14)
            clear * - r28045 b28046 b28047 b28048 d28028 f28019
            omega
          have d28049 : (x 2 1).toNat = 1 := by
            have r28050 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
            have b28051 := hb (x 2 1)
            have b28052 := hb (x 2 13)
            clear * - r28050 b28051 b28052 d28044
            omega
          have d28053 : (x 3 14).toNat = 0 := by
            have r28054 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28055 := hb (x 2 1)
            have b28056 := hb (x 3 14)
            clear * - r28054 b28055 b28056 d28049
            omega
          have d28057 : (x 3 1 && x 3 14).toNat = 0 := by
            have r28058 := hand2 (x 3 1) (x 3 14)
            have b28059 := hb (x 3 14)
            have b28060 := hb (x 3 1 && x 3 14)
            clear * - r28058 b28059 b28060 d28053
            omega
          have d28061 : (x 3 2).toNat = 0 := by
            have r28062 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
            have b28063 := hb (x 3 2)
            have b28064 := hb (x 3 14)
            clear * - r28062 b28063 b28064 d28053
            omega
          have d28065 : (x (-1) 2).toNat = 1 := by
            have r28066 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28067 := hb (x (-1) 2)
            have b28068 := hb (x 1 13)
            have b28069 := hb (x 0 1 && x 0 14)
            clear * - r28066 b28067 b28068 b28069 d28036 d28010
            omega
          have d28070 : (x (-1) 14).toNat = 1 := by
            have r28071 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
            have b28072 := hb (x (-1) 2)
            have b28073 := hb (x (-1) 14)
            clear * - r28071 b28072 b28073 d28065
            omega
          have d28074 : (x (-2) 1).toNat = 0 := by
            have r28075 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28076 := hb (x (-2) 1)
            have b28077 := hb (x (-1) 14)
            clear * - r28075 b28076 b28077 d28070
            omega
          have d28078 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
            have r28079 := hand1 (x (-2) 1) (x (-2) 14)
            have b28080 := hb (x (-2) 1)
            have b28081 := hb (x (-2) 1 && x (-2) 14)
            clear * - r28079 b28080 b28081 d28074
            omega
          have d28082 : (x (-2) 13).toNat = 0 := by
            have r28083 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
            have b28084 := hb (x (-2) 1)
            have b28085 := hb (x (-2) 13)
            clear * - r28083 b28084 b28085 d28074
            omega
          have d28086 : (x (-3) 2).toNat = 1 := by
            have r28087 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28088 := hb (x (-3) 2)
            have b28089 := hb (x (-1) 13)
            have b28090 := hb (x (-2) 1 && x (-2) 14)
            clear * - r28087 b28088 b28089 b28090 g2 d28078
            omega
          have d28091 : (x (-3) 14).toNat = 1 := by
            have r28092 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
            have b28093 := hb (x (-3) 2)
            have b28094 := hb (x (-3) 14)
            clear * - r28092 b28093 b28094 d28086
            omega
          have d28095 : (x (-4) 1).toNat = 0 := by
            have r28096 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28097 := hb (x (-4) 1)
            have b28098 := hb (x (-3) 14)
            clear * - r28096 b28097 b28098 d28091
            omega
          have d28099 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
            have r28100 := hand1 (x (-4) 1) (x (-4) 14)
            have b28101 := hb (x (-4) 1)
            have b28102 := hb (x (-4) 1 && x (-4) 14)
            clear * - r28100 b28101 b28102 d28095
            omega
          have d28103 : (x (-4) 13).toNat = 0 := by
            have r28104 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
            have b28105 := hb (x (-4) 1)
            have b28106 := hb (x (-4) 13)
            clear * - r28104 b28105 b28106 d28095
            omega
          have d28107 : (x (-4) 2).toNat = 1 := by
            have r28108 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28109 := hb (x (-4) 2)
            have b28110 := hb (x (-2) 13)
            have b28111 := hb (x (-3) 1 && x (-3) 14)
            clear * - r28108 b28109 b28110 b28111 d28082 d27924
            omega
          have d28112 : (x (-5) 2).toNat = 1 := by
            have r28113 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28114 := hb (x (-5) 2)
            have b28115 := hb (x (-3) 13)
            have b28116 := hb (x (-4) 1 && x (-4) 14)
            clear * - r28113 b28114 b28115 b28116 d27932 d28099
            omega
          have d28117 : (x 1 12).toNat = 0 := by
            have r28118 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28119 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e28120 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b28121 := hb (x (-2) 3)
            have b28122 := hb (x (-1) 2)
            have b28123 := hb (x 0 13)
            have b28124 := hb (x 1 12)
            clear * - r28118 e28119 e28120 b28121 b28122 b28123 b28124 g6 d28065
            omega
          have d28125 : (x (-2) 3).toNat = 0 := by
            have r28126 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28127 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e28128 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b28129 := hb (x (-2) 3)
            have b28130 := hb (x (-1) 2)
            have b28131 := hb (x 0 13)
            have b28132 := hb (x 1 12)
            clear * - r28126 e28127 e28128 b28129 b28130 b28131 b28132 d28117 g6 d28065
            omega
          have d28133 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
            have r28134 := hand1 (x (-2) 3) (x (-2) 14)
            have b28135 := hb (x (-2) 3)
            have b28136 := hb (x (-2) 3 && x (-2) 14)
            clear * - r28134 b28135 b28136 d28125
            omega
          have d28137 : (x (-1) 12).toNat = 0 := by
            have r28138 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28139 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e28140 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b28141 := hb (x (-4) 3)
            have b28142 := hb (x (-3) 2)
            have b28143 := hb (x (-2) 13)
            have b28144 := hb (x (-1) 12)
            clear * - r28138 e28139 e28140 b28141 b28142 b28143 b28144 d28082 d28086
            omega
          have d28145 : (x (-1) 4).toNat = 0 := by
            have r28146 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
            have b28147 := hb (x (-1) 4)
            have b28148 := hb (x (-1) 12)
            clear * - r28146 b28147 b28148 d28137
            omega
          have d28149 : (x (-2) 12).toNat = 0 := by
            have r28150 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28151 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e28152 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b28153 := hb (x (-5) 3)
            have b28154 := hb (x (-4) 2)
            have b28155 := hb (x (-3) 13)
            have b28156 := hb (x (-2) 12)
            clear * - r28150 e28151 e28152 b28153 b28154 b28155 b28156 d27932 d28107
            omega
          have d28157 : (x (-2) 4).toNat = 0 := by
            have r28158 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
            have b28159 := hb (x (-2) 4)
            have b28160 := hb (x (-2) 12)
            clear * - r28158 b28159 b28160 d28149
            omega
          have d28161 : (x (-3) 12).toNat = 0 := by
            have r28162 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28163 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e28164 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b28165 := hb (x (-6) 3)
            have b28166 := hb (x (-5) 2)
            have b28167 := hb (x (-4) 13)
            have b28168 := hb (x (-3) 12)
            clear * - r28162 e28163 e28164 b28165 b28166 b28167 b28168 d28103 d28112
            omega
          have d28169 : (x (-3) 4).toNat = 0 := by
            have r28170 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
            have b28171 := hb (x (-3) 4)
            have b28172 := hb (x (-3) 12)
            clear * - r28170 b28171 b28172 d28161
            omega
          have d28173 : (x 2 1 && x 2 12).toNat = 1 := by
            have r28174 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28175 := hb (x (-1) 4)
            have b28176 := hb (x 3 11)
            have b28177 := hb (x 2 1 && x 2 12)
            have b28178 := hb (x 1 2 && x 1 13)
            have b28179 := hb (x 0 3 && x 0 14)
            clear * - r28174 b28175 b28176 b28177 b28178 b28179 g10 d28040 g46 d28145
            omega
          have d28180 : (x 2 12).toNat = 1 := by
            have r28181 := hand2 (x 2 1) (x 2 12)
            have b28182 := hb (x 2 12)
            have b28183 := hb (x 2 1 && x 2 12)
            clear * - r28181 b28182 b28183 d28173
            omega
          have d28184 : (x (-1) 3).toNat = 0 := by
            have r28185 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28186 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
            have e28187 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
            have b28188 := hb (x (-1) 3)
            have b28189 := hb (x 0 2)
            have b28190 := hb (x 1 13)
            have b28191 := hb (x 2 12)
            clear * - r28185 e28186 e28187 b28188 b28189 b28190 b28191 d28180 d28036 f28019
            omega
          have d28192 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
            have r28193 := hand1 (x (-1) 3) (x (-1) 14)
            have b28194 := hb (x (-1) 3)
            have b28195 := hb (x (-1) 3 && x (-1) 14)
            clear * - r28193 b28194 b28195 d28184
            omega
          have d28196 : (x 2 11).toNat = 1 := by
            have r28197 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28198 := hb (x (-2) 4)
            have b28199 := hb (x 2 11)
            have b28200 := hb (x 1 1 && x 1 12)
            have b28201 := hb (x 0 2 && x 0 13)
            have b28202 := hb (x (-1) 3 && x (-1) 14)
            clear * - r28197 b28198 b28199 b28200 b28201 b28202 d28032 d27891 d28192 d28157
            omega
          have d28203 : (x 2 3).toNat = 1 := by
            have r28204 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
            have b28205 := hb (x 2 3)
            have b28206 := hb (x 2 11)
            clear * - r28204 b28205 b28206 d28196
            omega
          have d28207 : (x 5 12).toNat = 0 := by
            have r28208 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28209 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e28210 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b28211 := hb (x 2 3)
            have b28212 := hb (x 3 2)
            have b28213 := hb (x 4 13)
            have b28214 := hb (x 5 12)
            clear * - r28208 e28209 e28210 b28211 b28212 b28213 b28214 d28061 d28203
            omega
          have d28215 : (x 4 13).toNat = 0 := by
            have r28216 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28217 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e28218 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b28219 := hb (x 2 3)
            have b28220 := hb (x 3 2)
            have b28221 := hb (x 4 13)
            have b28222 := hb (x 5 12)
            clear * - r28216 e28217 e28218 b28219 b28220 b28221 b28222 d28207 d28061 d28203
            omega
          have d28223 : (x 2 2).toNat = 1 := by
            have r28224 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28225 := hb (x 2 2)
            have b28226 := hb (x 4 13)
            have b28227 := hb (x 3 1 && x 3 14)
            clear * - r28224 b28225 b28226 b28227 d28215 d28057
            omega
          have d28228 : (x 4 12).toNat = 0 := by
            have r28229 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28230 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e28231 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b28232 := hb (x 1 3)
            have b28233 := hb (x 2 2)
            have b28234 := hb (x 3 13)
            have b28235 := hb (x 4 12)
            clear * - r28229 e28230 e28231 b28232 b28233 b28234 b28235 d28223
            omega
          have d28236 : (x 3 13).toNat = 0 := by
            have r28237 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28238 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e28239 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b28240 := hb (x 1 3)
            have b28241 := hb (x 2 2)
            have b28242 := hb (x 3 13)
            have b28243 := hb (x 4 12)
            clear * - r28237 e28238 e28239 b28240 b28241 b28242 b28243 d28228 d28223
            omega
          have d28244 : (x 1 3).toNat = 0 := by
            have r28245 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28246 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e28247 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b28248 := hb (x 1 3)
            have b28249 := hb (x 2 2)
            have b28250 := hb (x 3 13)
            have b28251 := hb (x 4 12)
            clear * - r28245 e28246 e28247 b28248 b28249 b28250 b28251 d28228 d28236 d28223
            omega
          have d28252 : (x 1 11).toNat = 0 := by
            have r28253 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
            have b28254 := hb (x 1 3)
            have b28255 := hb (x 1 11)
            clear * - r28253 b28254 b28255 d28244
            omega
          have r28256 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28257 := hb (x (-3) 4)
          have b28258 := hb (x 1 11)
          have b28259 := hb (x 0 1 && x 0 12)
          have b28260 := hb (x (-1) 2 && x (-1) 13)
          have b28261 := hb (x (-2) 3 && x (-2) 14)
          linarith only [r28256, b28257, b28258, b28259, b28260, b28261, d28252, d27960, g45, d28133, d28169]
        · have f28262 : (x 1 1).toNat = 1 := by rw [h28026]; rfl
          have d28263 : (x 2 14).toNat = 0 := by
            have r28264 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28265 := hb (x 1 1)
            have b28266 := hb (x 2 14)
            clear * - r28264 b28265 b28266 f28262
            omega
          have d28267 : (x 2 6).toNat = 0 := by
            have r28268 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
            have b28269 := hb (x 2 6)
            have b28270 := hb (x 2 14)
            clear * - r28268 b28269 b28270 d28263
            omega
          have d28271 : (x 2 6 && x 2 12).toNat = 0 := by
            have r28272 := hand1 (x 2 6) (x 2 12)
            have b28273 := hb (x 2 6)
            have b28274 := hb (x 2 6 && x 2 12)
            clear * - r28272 b28273 b28274 d28267
            omega
          have d28275 : (x 2 2).toNat = 0 := by
            have r28276 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
            have b28277 := hb (x 2 2)
            have b28278 := hb (x 2 14)
            clear * - r28276 b28277 b28278 d28263
            omega
          have d28279 : (x 2 2 && x 2 12).toNat = 0 := by
            have r28280 := hand1 (x 2 2) (x 2 12)
            have b28281 := hb (x 2 2)
            have b28282 := hb (x 2 2 && x 2 12)
            clear * - r28280 b28281 b28282 d28275
            omega
          have d28283 : (x 1 3 && x 1 13).toNat = 1 := by
            have r28284 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28285 := hb (x (-1) 5)
            have b28286 := hb (x 4 10)
            have b28287 := hb (x 3 1 && x 3 11)
            have b28288 := hb (x 2 2 && x 2 12)
            have b28289 := hb (x 1 3 && x 1 13)
            have b28290 := hb (x 0 4 && x 0 14)
            clear * - r28284 b28285 b28286 b28287 b28288 b28289 b28290 g11 g42 d28279 d27968 g0
            omega
          have d28291 : (x 1 13).toNat = 1 := by
            have r28292 := hand2 (x 1 3) (x 1 13)
            have b28293 := hb (x 1 13)
            have b28294 := hb (x 1 3 && x 1 13)
            clear * - r28292 b28293 b28294 d28283
            omega
          have d28295 : (x 2 12).toNat = 0 := by
            have r28296 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28297 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
            have e28298 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
            have b28299 := hb (x (-1) 3)
            have b28300 := hb (x 0 2)
            have b28301 := hb (x 1 13)
            have b28302 := hb (x 2 12)
            clear * - r28296 e28297 e28298 b28299 b28300 b28301 b28302 d28291 f28019
            omega
          have d28303 : (x 1 3).toNat = 1 := by
            have r28304 := hand1 (x 1 3) (x 1 13)
            have b28305 := hb (x 1 3)
            have b28306 := hb (x 1 3 && x 1 13)
            clear * - r28304 b28305 b28306 d28283
            omega
          have d28307 : (x 4 12).toNat = 0 := by
            have r28308 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28309 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e28310 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b28311 := hb (x 1 3)
            have b28312 := hb (x 2 2)
            have b28313 := hb (x 3 13)
            have b28314 := hb (x 4 12)
            clear * - r28308 e28309 e28310 b28311 b28312 b28313 b28314 d28275 d28303
            omega
          have d28315 : (x 4 2 && x 4 12).toNat = 0 := by
            have r28316 := hand2 (x 4 2) (x 4 12)
            have b28317 := hb (x 4 12)
            have b28318 := hb (x 4 2 && x 4 12)
            clear * - r28316 b28317 b28318 d28307
            omega
          have d28319 : (x 4 4).toNat = 0 := by
            have r28320 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b28321 := hb (x 4 4)
            have b28322 := hb (x 4 12)
            clear * - r28320 b28321 b28322 d28307
            omega
          have d28323 : (x 4 4 && x 4 13).toNat = 0 := by
            have r28324 := hand1 (x 4 4) (x 4 13)
            have b28325 := hb (x 4 4)
            have b28326 := hb (x 4 4 && x 4 13)
            clear * - r28324 b28325 b28326 d28319
            omega
          have d28327 : (x 3 13).toNat = 0 := by
            have r28328 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28329 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e28330 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b28331 := hb (x 1 3)
            have b28332 := hb (x 2 2)
            have b28333 := hb (x 3 13)
            have b28334 := hb (x 4 12)
            clear * - r28328 e28329 e28330 b28331 b28332 b28333 b28334 d28307 d28275 d28303
            omega
          have d28335 : (x 3 3 && x 3 13).toNat = 0 := by
            have r28336 := hand2 (x 3 3) (x 3 13)
            have b28337 := hb (x 3 13)
            have b28338 := hb (x 3 3 && x 3 13)
            clear * - r28336 b28337 b28338 d28327
            omega
          have d28339 : (x 3 5).toNat = 0 := by
            have r28340 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
            have b28341 := hb (x 3 5)
            have b28342 := hb (x 3 13)
            clear * - r28340 b28341 b28342 d28327
            omega
          have d28343 : (x 3 5 && x 3 14).toNat = 0 := by
            have r28344 := hand1 (x 3 5) (x 3 14)
            have b28345 := hb (x 3 5)
            have b28346 := hb (x 3 5 && x 3 14)
            clear * - r28344 b28345 b28346 d28339
            omega
          have r28347 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28348 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28349 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28350 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e28351 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e28352 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e28353 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e28354 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e28355 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have r28356 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28357 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e28358 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e28359 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e28360 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e28361 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e28362 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have r28363 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28364 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e28365 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e28366 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e28367 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e28368 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e28369 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have r28370 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28371 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
          have e28372 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
          have e28373 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
          have e28374 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
          have e28375 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
          have e28376 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
          have r28377 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28378 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e28379 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have r28380 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28381 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
          have e28382 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
          have r28383 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28384 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28385 : 1 ≤ (x 16 6).toNat + (x 15 1 && x 15 7).toNat + (x 14 2 && x 14 8).toNat + (x 13 3 && x 13 9).toNat + (x 12 4 && x 12 10).toNat + (x 11 5 && x 11 11).toNat + (x 10 6 && x 10 12).toNat + (x 9 7 && x 9 13).toNat + (x 8 8 && x 8 14).toNat + (x 7 9).toNat := by have q := hcov6 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28386 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28387 : 1 ≤ (x 21 9).toNat + (x 20 1 && x 20 10).toNat + (x 19 2 && x 19 11).toNat + (x 18 3 && x 18 12).toNat + (x 17 4 && x 17 13).toNat + (x 16 5 && x 16 14).toNat + (x 15 6).toNat := by have q := hcov9 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28388 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28389 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28390 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28391 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28392 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28393 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28394 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
          have r28395 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
          have r28396 : (x 15 6).toNat ≤ (x 15 14).toNat := himp _ _ (hp6 15)
          have r28397 : (x 16 5).toNat ≤ (x 16 13).toNat := himp _ _ (hp5 16)
          have r28398 : (x 17 4).toNat ≤ (x 17 12).toNat := himp _ _ (hp4 17)
          have r28399 := hand2 (x 7 1) (x 7 7)
          have r28400 := hand1 (x 1 7) (x 1 13)
          have r28401 := hand2 (x 15 1) (x 15 7)
          have r28402 := hand2 (x 14 2) (x 14 8)
          have r28403 := hand2 (x 13 3) (x 13 9)
          have r28404 := hand1 (x 12 4) (x 12 10)
          have r28405 := hand1 (x 11 5) (x 11 11)
          have r28406 := hand1 (x 10 6) (x 10 12)
          have r28407 := hand1 (x 9 7) (x 9 13)
          have r28408 := hand1 (x 8 8) (x 8 14)
          have r28409 := hand2 (x 7 1) (x 7 10)
          have r28410 := hand2 (x 6 2) (x 6 11)
          have r28411 := hand2 (x 5 3) (x 5 12)
          have r28412 := hand2 (x 20 1) (x 20 10)
          have r28413 := hand2 (x 19 2) (x 19 11)
          have r28414 := hand2 (x 18 3) (x 18 12)
          have r28415 := hand1 (x 17 4) (x 17 13)
          have r28416 := hand1 (x 16 5) (x 16 14)
          have r28417 := hand2 (x 5 1) (x 5 11)
          have r28418 := hand2 (x 13 1) (x 13 11)
          have r28419 := hand1 (x 12 2) (x 12 12)
          have r28420 := hand1 (x 11 3) (x 11 13)
          have r28421 := hand1 (x 10 4) (x 10 14)
          have r28422 := hand1 (x 13 1) (x 13 12)
          have r28423 := hand1 (x 12 2) (x 12 13)
          have r28424 := hand1 (x 11 3) (x 11 14)
          have r28425 := hand2 (x 3 1) (x 3 14)
          have r28426 := hand1 (x 13 1) (x 13 14)
          have r28427 := hand1 (x 16 1) (x 16 14)
          linarith only [r28347, r28348, r28349, e28350, e28351, e28352, e28353, e28354, e28355, r28356, e28357, e28358, e28359, e28360, e28361, e28362, r28363, e28364, e28365, e28366, e28367, e28368, e28369, r28370, e28371, e28372, e28373, e28374, e28375, e28376, r28377, e28378, e28379, r28380, e28381, e28382, r28383, r28384, r28385, r28386, r28387, r28388, r28389, r28390, r28391, r28392, r28393, r28394, r28395, r28396, r28397, r28398, r28399, r28400, r28401, r28402, r28403, r28404, r28405, r28406, r28407, r28408, r28409, r28410, r28411, r28412, r28413, r28414, r28415, r28416, r28417, r28418, r28419, r28420, r28421, r28422, r28423, r28424, r28425, r28426, r28427, g1, g7, g8, d28291, d28275, d28267, d28295, d28339, g10, d28319, g11, g12, g13, g31, g32, g33, g34, d28271, d28022, d28323, d28343, d28315, d28335, g43]
      · have f28540 : (x 0 8).toNat = 1 := by rw [h28020]; rfl
        have d28541 : (x (-2) 10).toNat = 0 := by
          have r28542 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28543 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e28544 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e28545 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e28546 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e28547 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e28548 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b28549 := hb (x (-7) 7)
          have b28550 := hb (x (-6) 6)
          have b28551 := hb (x (-5) 5)
          have b28552 := hb (x (-4) 4)
          have b28553 := hb (x (-3) 11)
          have b28554 := hb (x (-2) 10)
          have b28555 := hb (x (-1) 9)
          have b28556 := hb (x 0 8)
          clear * - r28542 e28543 e28544 e28545 e28546 e28547 e28548 b28549 b28550 b28551 b28552 b28553 b28554 b28555 b28556 f28540 g1 d27996
          omega
        have d28557 : (x (-4) 4).toNat = 0 := by
          have r28558 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28559 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e28560 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e28561 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e28562 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e28563 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e28564 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b28565 := hb (x (-7) 7)
          have b28566 := hb (x (-6) 6)
          have b28567 := hb (x (-5) 5)
          have b28568 := hb (x (-4) 4)
          have b28569 := hb (x (-3) 11)
          have b28570 := hb (x (-2) 10)
          have b28571 := hb (x (-1) 9)
          have b28572 := hb (x 0 8)
          clear * - r28558 e28559 e28560 e28561 e28562 e28563 e28564 b28565 b28566 b28567 b28568 b28569 b28570 b28571 b28572 f28540 g1 d28541 d27996
          omega
        have d28573 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
          have r28574 := hand1 (x (-4) 4) (x (-4) 13)
          have b28575 := hb (x (-4) 4)
          have b28576 := hb (x (-4) 4 && x (-4) 13)
          clear * - r28574 b28575 b28576 d28557
          omega
        have d28577 : (x (-2) 2 && x (-2) 13).toNat = 1 := by
          have r28578 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28579 := hb (x (-4) 4)
          have b28580 := hb (x 0 11)
          have b28581 := hb (x (-1) 1 && x (-1) 12)
          have b28582 := hb (x (-2) 2 && x (-2) 13)
          have b28583 := hb (x (-3) 3 && x (-3) 14)
          clear * - r28578 b28579 b28580 b28581 b28582 b28583 g5 g44 d27980 d28557
          omega
        have d28584 : (x (-2) 13).toNat = 1 := by
          have r28585 := hand2 (x (-2) 2) (x (-2) 13)
          have b28586 := hb (x (-2) 13)
          have b28587 := hb (x (-2) 2 && x (-2) 13)
          clear * - r28585 b28586 b28587 d28577
          omega
        have d28588 : (x (-2) 1).toNat = 1 := by
          have r28589 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
          have b28590 := hb (x (-2) 1)
          have b28591 := hb (x (-2) 13)
          clear * - r28589 b28590 b28591 d28584
          omega
        have d28592 : (x (-1) 14).toNat = 0 := by
          have r28593 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28594 := hb (x (-2) 1)
          have b28595 := hb (x (-1) 14)
          clear * - r28593 b28594 b28595 d28588
          omega
        have d28596 : (x (-1) 6).toNat = 0 := by
          have r28597 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
          have b28598 := hb (x (-1) 6)
          have b28599 := hb (x (-1) 14)
          clear * - r28597 b28598 b28599 d28592
          omega
        have d28600 : (x (-1) 2).toNat = 0 := by
          have r28601 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
          have b28602 := hb (x (-1) 2)
          have b28603 := hb (x (-1) 14)
          clear * - r28601 b28602 b28603 d28592
          omega
        have d28604 : (x 1 13).toNat = 1 := by
          have r28605 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28606 := hb (x (-1) 2)
          have b28607 := hb (x 1 13)
          have b28608 := hb (x 0 1 && x 0 14)
          clear * - r28605 b28606 b28607 b28608 d28010 d28600
          omega
        have d28609 : (x 2 12).toNat = 0 := by
          have r28610 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28611 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e28612 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b28613 := hb (x (-1) 3)
          have b28614 := hb (x 0 2)
          have b28615 := hb (x 1 13)
          have b28616 := hb (x 2 12)
          clear * - r28610 e28611 e28612 b28613 b28614 b28615 b28616 d28604 f28019
          omega
        have d28617 : (x 2 3 && x 2 12).toNat = 0 := by
          have r28618 := hand2 (x 2 3) (x 2 12)
          have b28619 := hb (x 2 12)
          have b28620 := hb (x 2 3 && x 2 12)
          clear * - r28618 b28619 b28620 d28609
          omega
        have d28621 : (x 1 4 && x 1 13).toNat = 1 := by
          have r28622 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28623 := hb (x (-1) 6)
          have b28624 := hb (x 5 9)
          have b28625 := hb (x 4 1 && x 4 10)
          have b28626 := hb (x 3 2 && x 3 11)
          have b28627 := hb (x 2 3 && x 2 12)
          have b28628 := hb (x 1 4 && x 1 13)
          have b28629 := hb (x 0 5 && x 0 14)
          clear * - r28622 b28623 b28624 b28625 b28626 b28627 b28628 b28629 g12 g39 g40 d28617 d27903 d28596
          omega
        have d28630 : (x 1 4).toNat = 1 := by
          have r28631 := hand1 (x 1 4) (x 1 13)
          have b28632 := hb (x 1 4)
          have b28633 := hb (x 1 4 && x 1 13)
          clear * - r28631 b28632 b28633 d28621
          omega
        have d28634 : (x 1 12).toNat = 1 := by
          have r28635 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
          have b28636 := hb (x 1 4)
          have b28637 := hb (x 1 12)
          clear * - r28635 b28636 b28637 d28630
          omega
        have d28638 : (x (-2) 3).toNat = 0 := by
          have r28639 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28640 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e28641 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b28642 := hb (x (-2) 3)
          have b28643 := hb (x (-1) 2)
          have b28644 := hb (x 0 13)
          have b28645 := hb (x 1 12)
          clear * - r28639 e28640 e28641 b28642 b28643 b28644 b28645 d28634 g6 d28600
          omega
        have d28646 : (x (-2) 11).toNat = 0 := by
          have r28647 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
          have b28648 := hb (x (-2) 3)
          have b28649 := hb (x (-2) 11)
          clear * - r28647 b28648 b28649 d28638
          omega
        have d28650 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
          have r28651 := hand2 (x (-2) 2) (x (-2) 11)
          have b28652 := hb (x (-2) 11)
          have b28653 := hb (x (-2) 2 && x (-2) 11)
          clear * - r28651 b28652 b28653 d28646
          omega
        have d28654 : (x (-5) 5).toNat = 0 := by
          have r28655 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28656 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e28657 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e28658 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e28659 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e28660 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e28661 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b28662 := hb (x (-7) 7)
          have b28663 := hb (x (-6) 6)
          have b28664 := hb (x (-5) 5)
          have b28665 := hb (x (-4) 4)
          have b28666 := hb (x (-3) 11)
          have b28667 := hb (x (-2) 10)
          have b28668 := hb (x (-1) 9)
          have b28669 := hb (x 0 8)
          clear * - r28655 e28656 e28657 e28658 e28659 e28660 e28661 b28662 b28663 b28664 b28665 b28666 b28667 b28668 b28669 f28540 g1 d28541 d27996 d28557
          omega
        have d28670 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
          have r28671 := hand1 (x (-5) 5) (x (-5) 14)
          have b28672 := hb (x (-5) 5)
          have b28673 := hb (x (-5) 5 && x (-5) 14)
          clear * - r28671 b28672 b28673 d28654
          omega
        have d28674 : (x (-6) 6).toNat = 1 := by
          have r28675 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28676 := hb (x (-6) 6)
          have b28677 := hb (x 0 9)
          have b28678 := hb (x (-1) 1 && x (-1) 10)
          have b28679 := hb (x (-2) 2 && x (-2) 11)
          have b28680 := hb (x (-3) 3 && x (-3) 12)
          have b28681 := hb (x (-4) 4 && x (-4) 13)
          have b28682 := hb (x (-5) 5 && x (-5) 14)
          clear * - r28675 b28676 b28677 b28678 b28679 b28680 b28681 b28682 d28014 g36 d28650 d27984 d28573 d28670
          omega
        have r28683 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28684 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e28685 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e28686 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e28687 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e28688 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e28689 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b28690 := hb (x (-7) 7)
        have b28691 := hb (x (-6) 6)
        have b28692 := hb (x (-5) 5)
        have b28693 := hb (x (-4) 4)
        have b28694 := hb (x (-3) 11)
        have b28695 := hb (x (-2) 10)
        have b28696 := hb (x (-1) 9)
        have b28697 := hb (x 0 8)
        linarith only [r28683, e28684, e28685, e28686, e28687, e28688, e28689, b28690, b28691, b28692, b28693, b28694, b28695, b28696, b28697, f28540, g1, d28541, d27996, d28557, d28654, d28674]
    · have f28698 : (x 0 2).toNat = 1 := by rw [h28018]; rfl
      have d28699 : (x 2 12).toNat = 0 := by
        have r28700 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28701 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e28702 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b28703 := hb (x (-1) 3)
        have b28704 := hb (x 0 2)
        have b28705 := hb (x 1 13)
        have b28706 := hb (x 2 12)
        clear * - r28700 e28701 e28702 b28703 b28704 b28705 b28706 f28698
        omega
      have d28707 : (x 2 1 && x 2 12).toNat = 0 := by
        have r28708 := hand2 (x 2 1) (x 2 12)
        have b28709 := hb (x 2 12)
        have b28710 := hb (x 2 1 && x 2 12)
        clear * - r28708 b28709 b28710 d28699
        omega
      have d28711 : (x 1 13).toNat = 0 := by
        have r28712 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28713 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e28714 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b28715 := hb (x (-1) 3)
        have b28716 := hb (x 0 2)
        have b28717 := hb (x 1 13)
        have b28718 := hb (x 2 12)
        clear * - r28712 e28713 e28714 b28715 b28716 b28717 b28718 d28699 f28698
        omega
      have d28719 : (x 1 2 && x 1 13).toNat = 0 := by
        have r28720 := hand2 (x 1 2) (x 1 13)
        have b28721 := hb (x 1 13)
        have b28722 := hb (x 1 2 && x 1 13)
        clear * - r28720 b28721 b28722 d28711
        omega
      have d28723 : (x (-1) 2).toNat = 1 := by
        have r28724 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b28725 := hb (x (-1) 2)
        have b28726 := hb (x 1 13)
        have b28727 := hb (x 0 1 && x 0 14)
        clear * - r28724 b28725 b28726 b28727 d28711 d28010
        omega
      have d28728 : (x (-1) 14).toNat = 1 := by
        have r28729 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
        have b28730 := hb (x (-1) 2)
        have b28731 := hb (x (-1) 14)
        clear * - r28729 b28730 b28731 d28723
        omega
      have d28732 : (x (-2) 1).toNat = 0 := by
        have r28733 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b28734 := hb (x (-2) 1)
        have b28735 := hb (x (-1) 14)
        clear * - r28733 b28734 b28735 d28728
        omega
      have d28736 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
        have r28737 := hand1 (x (-2) 1) (x (-2) 14)
        have b28738 := hb (x (-2) 1)
        have b28739 := hb (x (-2) 1 && x (-2) 14)
        clear * - r28737 b28738 b28739 d28732
        omega
      have d28740 : (x (-3) 2).toNat = 1 := by
        have r28741 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b28742 := hb (x (-3) 2)
        have b28743 := hb (x (-1) 13)
        have b28744 := hb (x (-2) 1 && x (-2) 14)
        clear * - r28741 b28742 b28743 b28744 g2 d28736
        omega
      have d28745 : (x (-2) 13).toNat = 0 := by
        have r28746 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
        have b28747 := hb (x (-2) 1)
        have b28748 := hb (x (-2) 13)
        clear * - r28746 b28747 b28748 d28732
        omega
      have d28749 : (x (-1) 12).toNat = 0 := by
        have r28750 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28751 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e28752 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b28753 := hb (x (-4) 3)
        have b28754 := hb (x (-3) 2)
        have b28755 := hb (x (-2) 13)
        have b28756 := hb (x (-1) 12)
        clear * - r28750 e28751 e28752 b28753 b28754 b28755 b28756 d28745 d28740
        omega
      have d28757 : (x (-1) 4).toNat = 0 := by
        have r28758 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
        have b28759 := hb (x (-1) 4)
        have b28760 := hb (x (-1) 12)
        clear * - r28758 b28759 b28760 d28749
        omega
      have r28761 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28762 := hb (x (-1) 4)
      have b28763 := hb (x 3 11)
      have b28764 := hb (x 2 1 && x 2 12)
      have b28765 := hb (x 1 2 && x 1 13)
      have b28766 := hb (x 0 3 && x 0 14)
      linarith only [r28761, b28762, b28763, b28764, b28765, b28766, g10, d28707, d28719, g46, d28757]
  · have f28767 : (x 0 1).toNat = 1 := by rw [h28008]; rfl
    have d28768 : (x 1 14).toNat = 0 := by
      have r28769 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28770 := hb (x 0 1)
      have b28771 := hb (x 1 14)
      clear * - r28769 b28770 b28771 f28767
      omega
    have d28772 : (x 1 1 && x 1 14).toNat = 0 := by
      have r28773 := hand2 (x 1 1) (x 1 14)
      have b28774 := hb (x 1 14)
      have b28775 := hb (x 1 1 && x 1 14)
      clear * - r28773 b28774 b28775 d28768
      omega
    have d28776 : (x 1 2).toNat = 0 := by
      have r28777 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
      have b28778 := hb (x 1 2)
      have b28779 := hb (x 1 14)
      clear * - r28777 b28778 b28779 d28768
      omega
    have d28780 : (x 1 2 && x 1 13).toNat = 0 := by
      have r28781 := hand1 (x 1 2) (x 1 13)
      have b28782 := hb (x 1 2)
      have b28783 := hb (x 1 2 && x 1 13)
      clear * - r28781 b28782 b28783 d28776
      omega
    have d28784 : (x 1 2 && x 1 11).toNat = 0 := by
      have r28785 := hand1 (x 1 2) (x 1 11)
      have b28786 := hb (x 1 2)
      have b28787 := hb (x 1 2 && x 1 11)
      clear * - r28785 b28786 b28787 d28776
      omega
    have d28788 : (x 1 2 && x 1 7).toNat = 0 := by
      have r28789 := hand1 (x 1 2) (x 1 7)
      have b28790 := hb (x 1 2)
      have b28791 := hb (x 1 2 && x 1 7)
      clear * - r28789 b28790 b28791 d28776
      omega
    have d28792 : (x 1 10).toNat = 0 := by
      have r28793 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
      have b28794 := hb (x 1 2)
      have b28795 := hb (x 1 10)
      clear * - r28793 b28794 b28795 d28776
      omega
    cases h28796 : x 0 2
    · have f28797 : (x 0 2).toNat = 0 := by rw [h28796]; rfl
      have d28798 : (x 0 10).toNat = 0 := by
        have r28799 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
        have b28800 := hb (x 0 2)
        have b28801 := hb (x 0 10)
        clear * - r28799 b28800 b28801 f28797
        omega
      have d28802 : (x 0 1 && x 0 10).toNat = 0 := by
        have r28803 := hand2 (x 0 1) (x 0 10)
        have b28804 := hb (x 0 10)
        have b28805 := hb (x 0 1 && x 0 10)
        clear * - r28803 b28804 b28805 d28798
        omega
      have d28806 : (x 0 6 && x 0 10).toNat = 0 := by
        have r28807 := hand2 (x 0 6) (x 0 10)
        have b28808 := hb (x 0 10)
        have b28809 := hb (x 0 6 && x 0 10)
        clear * - r28807 b28808 b28809 d28798
        omega
      have d28810 : (x 2 13).toNat = 1 := by
        have r28811 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b28812 := hb (x 0 2)
        have b28813 := hb (x 2 13)
        have b28814 := hb (x 1 1 && x 1 14)
        clear * - r28811 b28812 b28813 b28814 d28772 f28797
        omega
      have d28815 : (x 2 1).toNat = 1 := by
        have r28816 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
        have b28817 := hb (x 2 1)
        have b28818 := hb (x 2 13)
        clear * - r28816 b28817 b28818 d28810
        omega
      have d28819 : (x 3 14).toNat = 0 := by
        have r28820 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b28821 := hb (x 2 1)
        have b28822 := hb (x 3 14)
        clear * - r28820 b28821 b28822 d28815
        omega
      have d28823 : (x 3 1 && x 3 14).toNat = 0 := by
        have r28824 := hand2 (x 3 1) (x 3 14)
        have b28825 := hb (x 3 14)
        have b28826 := hb (x 3 1 && x 3 14)
        clear * - r28824 b28825 b28826 d28819
        omega
      have d28827 : (x 3 3 && x 3 14).toNat = 0 := by
        have r28828 := hand2 (x 3 3) (x 3 14)
        have b28829 := hb (x 3 14)
        have b28830 := hb (x 3 3 && x 3 14)
        clear * - r28828 b28829 b28830 d28819
        omega
      have d28831 : (x 3 5 && x 3 14).toNat = 0 := by
        have r28832 := hand2 (x 3 5) (x 3 14)
        have b28833 := hb (x 3 14)
        have b28834 := hb (x 3 5 && x 3 14)
        clear * - r28832 b28833 b28834 d28819
        omega
      have d28835 : (x 3 6).toNat = 0 := by
        have r28836 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
        have b28837 := hb (x 3 6)
        have b28838 := hb (x 3 14)
        clear * - r28836 b28837 b28838 d28819
        omega
      have d28839 : (x 3 2 && x 3 6).toNat = 0 := by
        have r28840 := hand2 (x 3 2) (x 3 6)
        have b28841 := hb (x 3 6)
        have b28842 := hb (x 3 2 && x 3 6)
        clear * - r28840 b28841 b28842 d28835
        omega
      have d28843 : (x 3 2).toNat = 0 := by
        have r28844 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
        have b28845 := hb (x 3 2)
        have b28846 := hb (x 3 14)
        clear * - r28844 b28845 b28846 d28819
        omega
      have d28847 : (x 3 10).toNat = 0 := by
        have r28848 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
        have b28849 := hb (x 3 2)
        have b28850 := hb (x 3 10)
        clear * - r28848 b28849 b28850 d28843
        omega
      cases h28851 : x 0 8
      · have f28852 : (x 0 8).toNat = 0 := by rw [h28851]; rfl
        have d28853 : (x 0 8 && x 0 14).toNat = 0 := by
          have r28854 := hand1 (x 0 8) (x 0 14)
          have b28855 := hb (x 0 8)
          have b28856 := hb (x 0 8 && x 0 14)
          clear * - r28854 b28855 b28856 f28852
          omega
        cases h28857 : x (-1) 2
        · have f28858 : (x (-1) 2).toNat = 0 := by rw [h28857]; rfl
          have d28859 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
            have r28860 := hand1 (x (-1) 2) (x (-1) 12)
            have b28861 := hb (x (-1) 2)
            have b28862 := hb (x (-1) 2 && x (-1) 12)
            clear * - r28860 b28861 b28862 f28858
            omega
          have d28863 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
            have r28864 := hand1 (x (-1) 2) (x (-1) 11)
            have b28865 := hb (x (-1) 2)
            have b28866 := hb (x (-1) 2 && x (-1) 11)
            clear * - r28864 b28865 b28866 f28858
            omega
          have d28867 : (x (-1) 10).toNat = 0 := by
            have r28868 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
            have b28869 := hb (x (-1) 2)
            have b28870 := hb (x (-1) 10)
            clear * - r28868 b28869 b28870 f28858
            omega
          cases h28871 : x 0 9
          · have f28872 : (x 0 9).toNat = 0 := by rw [h28871]; rfl
            have d28873 : (x 0 9 && x 0 14).toNat = 0 := by
              have r28874 := hand1 (x 0 9) (x 0 14)
              have b28875 := hb (x 0 9)
              have b28876 := hb (x 0 9 && x 0 14)
              clear * - r28874 b28875 b28876 f28872
              omega
            cases h28877 : x (-1) 3
            · have f28878 : (x (-1) 3).toNat = 0 := by rw [h28877]; rfl
              have d28879 : (x (-1) 11).toNat = 0 := by
                have r28880 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
                have b28881 := hb (x (-1) 3)
                have b28882 := hb (x (-1) 11)
                clear * - r28880 b28881 b28882 f28878
                omega
              cases h28883 : x 1 1
              · have f28884 : (x 1 1).toNat = 0 := by rw [h28883]; rfl
                have d28885 : (x 1 13).toNat = 0 := by
                  have r28886 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
                  have b28887 := hb (x 1 1)
                  have b28888 := hb (x 1 13)
                  clear * - r28886 b28887 b28888 f28884
                  omega
                have d28889 : (x 1 3 && x 1 13).toNat = 0 := by
                  have r28890 := hand2 (x 1 3) (x 1 13)
                  have b28891 := hb (x 1 13)
                  have b28892 := hb (x 1 3 && x 1 13)
                  clear * - r28890 b28891 b28892 d28885
                  omega
                have d28893 : (x 1 4 && x 1 13).toNat = 0 := by
                  have r28894 := hand2 (x 1 4) (x 1 13)
                  have b28895 := hb (x 1 13)
                  have b28896 := hb (x 1 4 && x 1 13)
                  clear * - r28894 b28895 b28896 d28885
                  omega
                have d28897 : (x 1 8 && x 1 13).toNat = 0 := by
                  have r28898 := hand2 (x 1 8) (x 1 13)
                  have b28899 := hb (x 1 13)
                  have b28900 := hb (x 1 8 && x 1 13)
                  clear * - r28898 b28899 b28900 d28885
                  omega
                have d28901 : (x 1 12 && x 1 13).toNat = 0 := by
                  have r28902 := hand2 (x 1 12) (x 1 13)
                  have b28903 := hb (x 1 13)
                  have b28904 := hb (x 1 12 && x 1 13)
                  clear * - r28902 b28903 b28904 d28885
                  omega
                have d28905 : (x 2 12).toNat = 1 := by
                  have r28906 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e28907 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                  have e28908 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                  have b28909 := hb (x (-1) 3)
                  have b28910 := hb (x 0 2)
                  have b28911 := hb (x 1 13)
                  have b28912 := hb (x 2 12)
                  clear * - r28906 e28907 e28908 b28909 b28910 b28911 b28912 d28885 f28797 f28878
                  omega
                have d28913 : (x 2 2 && x 2 12).toNat = 1 := by
                  have r28914 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b28915 := hb (x (-1) 5)
                  have b28916 := hb (x 4 10)
                  have b28917 := hb (x 3 1 && x 3 11)
                  have b28918 := hb (x 2 2 && x 2 12)
                  have b28919 := hb (x 1 3 && x 1 13)
                  have b28920 := hb (x 0 4 && x 0 14)
                  clear * - r28914 b28915 b28916 b28917 b28918 b28919 b28920 g11 g42 d28889 d27968 g0
                  omega
                have d28921 : (x 2 2).toNat = 1 := by
                  have r28922 := hand1 (x 2 2) (x 2 12)
                  have b28923 := hb (x 2 2)
                  have b28924 := hb (x 2 2 && x 2 12)
                  clear * - r28922 b28923 b28924 d28913
                  omega
                have d28925 : (x 4 12).toNat = 0 := by
                  have r28926 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e28927 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e28928 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b28929 := hb (x 1 3)
                  have b28930 := hb (x 2 2)
                  have b28931 := hb (x 3 13)
                  have b28932 := hb (x 4 12)
                  clear * - r28926 e28927 e28928 b28929 b28930 b28931 b28932 d28921
                  omega
                have d28933 : (x 3 13).toNat = 0 := by
                  have r28934 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e28935 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e28936 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b28937 := hb (x 1 3)
                  have b28938 := hb (x 2 2)
                  have b28939 := hb (x 3 13)
                  have b28940 := hb (x 4 12)
                  clear * - r28934 e28935 e28936 b28937 b28938 b28939 b28940 d28925 d28921
                  omega
                have d28941 : (x 1 3).toNat = 0 := by
                  have r28942 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e28943 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e28944 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b28945 := hb (x 1 3)
                  have b28946 := hb (x 2 2)
                  have b28947 := hb (x 3 13)
                  have b28948 := hb (x 4 12)
                  clear * - r28942 e28943 e28944 b28945 b28946 b28947 b28948 d28925 d28933 d28921
                  omega
                have d28949 : (x 1 11).toNat = 0 := by
                  have r28950 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
                  have b28951 := hb (x 1 3)
                  have b28952 := hb (x 1 11)
                  clear * - r28950 b28951 b28952 d28941
                  omega
                cases h28953 : x (-1) 4
                · have f28954 : (x (-1) 4).toNat = 0 := by rw [h28953]; rfl
                  cases h28955 : x 1 4
                  · have f28956 : (x 1 4).toNat = 0 := by rw [h28955]; rfl
                    cases h28957 : x (-1) 6
                    · have f28958 : (x (-1) 6).toNat = 0 := by rw [h28957]; rfl
                      have d28959 : (x 2 3 && x 2 12).toNat = 1 := by
                        have r28960 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b28961 := hb (x (-1) 6)
                        have b28962 := hb (x 5 9)
                        have b28963 := hb (x 4 1 && x 4 10)
                        have b28964 := hb (x 3 2 && x 3 11)
                        have b28965 := hb (x 2 3 && x 2 12)
                        have b28966 := hb (x 1 4 && x 1 13)
                        have b28967 := hb (x 0 5 && x 0 14)
                        clear * - r28960 b28961 b28962 b28963 b28964 b28965 b28966 b28967 g12 g39 g40 d28893 d27903 f28958
                        omega
                      have d28968 : (x 2 3).toNat = 1 := by
                        have r28969 := hand1 (x 2 3) (x 2 12)
                        have b28970 := hb (x 2 3)
                        have b28971 := hb (x 2 3 && x 2 12)
                        clear * - r28969 b28970 b28971 d28959
                        omega
                      have d28972 : (x 5 12).toNat = 0 := by
                        have r28973 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28974 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                        have e28975 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                        have b28976 := hb (x 2 3)
                        have b28977 := hb (x 3 2)
                        have b28978 := hb (x 4 13)
                        have b28979 := hb (x 5 12)
                        clear * - r28973 e28974 e28975 b28976 b28977 b28978 b28979 d28843 d28968
                        omega
                      have d28980 : (x 5 1 && x 5 12).toNat = 0 := by
                        have r28981 := hand2 (x 5 1) (x 5 12)
                        have b28982 := hb (x 5 12)
                        have b28983 := hb (x 5 1 && x 5 12)
                        clear * - r28981 b28982 b28983 d28972
                        omega
                      have d28984 : (x 5 4).toNat = 0 := by
                        have r28985 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                        have b28986 := hb (x 5 4)
                        have b28987 := hb (x 5 12)
                        clear * - r28985 b28986 b28987 d28972
                        omega
                      have d28988 : (x 5 4 && x 5 13).toNat = 0 := by
                        have r28989 := hand1 (x 5 4) (x 5 13)
                        have b28990 := hb (x 5 4)
                        have b28991 := hb (x 5 4 && x 5 13)
                        clear * - r28989 b28990 b28991 d28984
                        omega
                      have d28992 : (x 4 13).toNat = 0 := by
                        have r28993 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28994 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                        have e28995 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                        have b28996 := hb (x 2 3)
                        have b28997 := hb (x 3 2)
                        have b28998 := hb (x 4 13)
                        have b28999 := hb (x 5 12)
                        clear * - r28993 e28994 e28995 b28996 b28997 b28998 b28999 d28972 d28843 d28968
                        omega
                      have d29000 : (x 4 2 && x 4 13).toNat = 0 := by
                        have r29001 := hand2 (x 4 2) (x 4 13)
                        have b29002 := hb (x 4 13)
                        have b29003 := hb (x 4 2 && x 4 13)
                        clear * - r29001 b29002 b29003 d28992
                        omega
                      have d29004 : (x 6 11).toNat = 1 := by
                        have r29005 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b29006 := hb (x 2 4)
                        have b29007 := hb (x 6 11)
                        have b29008 := hb (x 5 1 && x 5 12)
                        have b29009 := hb (x 4 2 && x 4 13)
                        have b29010 := hb (x 3 3 && x 3 14)
                        clear * - r29005 b29006 b29007 b29008 b29009 b29010 d28980 d29000 d28827 g9
                        omega
                      have d29011 : (x 6 3).toNat = 1 := by
                        have r29012 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
                        have b29013 := hb (x 6 3)
                        have b29014 := hb (x 6 11)
                        clear * - r29012 b29013 b29014 d29004
                        omega
                      have d29015 : (x 9 12).toNat = 0 := by
                        have r29016 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29017 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                        have e29018 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                        have b29019 := hb (x 6 3)
                        have b29020 := hb (x 7 2)
                        have b29021 := hb (x 8 13)
                        have b29022 := hb (x 9 12)
                        clear * - r29016 e29017 e29018 b29019 b29020 b29021 b29022 d29011
                        omega
                      have d29023 : (x 9 5 && x 9 12).toNat = 0 := by
                        have r29024 := hand2 (x 9 5) (x 9 12)
                        have b29025 := hb (x 9 12)
                        have b29026 := hb (x 9 5 && x 9 12)
                        clear * - r29024 b29025 b29026 d29015
                        omega
                      have d29027 : (x 9 4).toNat = 0 := by
                        have r29028 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                        have b29029 := hb (x 9 4)
                        have b29030 := hb (x 9 12)
                        clear * - r29028 b29029 b29030 d29015
                        omega
                      have d29031 : (x 9 4 && x 9 13).toNat = 0 := by
                        have r29032 := hand1 (x 9 4) (x 9 13)
                        have b29033 := hb (x 9 4)
                        have b29034 := hb (x 9 4 && x 9 13)
                        clear * - r29032 b29033 b29034 d29027
                        omega
                      have d29035 : (x 9 4 && x 9 9).toNat = 0 := by
                        have r29036 := hand1 (x 9 4) (x 9 9)
                        have b29037 := hb (x 9 4)
                        have b29038 := hb (x 9 4 && x 9 9)
                        clear * - r29036 b29037 b29038 d29027
                        omega
                      have d29039 : (x 9 4 && x 9 5).toNat = 0 := by
                        have r29040 := hand1 (x 9 4) (x 9 5)
                        have b29041 := hb (x 9 4)
                        have b29042 := hb (x 9 4 && x 9 5)
                        clear * - r29040 b29041 b29042 d29027
                        omega
                      have d29043 : (x 8 13).toNat = 0 := by
                        have r29044 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29045 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                        have e29046 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                        have b29047 := hb (x 6 3)
                        have b29048 := hb (x 7 2)
                        have b29049 := hb (x 8 13)
                        have b29050 := hb (x 9 12)
                        clear * - r29044 e29045 e29046 b29047 b29048 b29049 b29050 d29015 d29011
                        omega
                      have d29051 : (x 8 6 && x 8 13).toNat = 0 := by
                        have r29052 := hand2 (x 8 6) (x 8 13)
                        have b29053 := hb (x 8 13)
                        have b29054 := hb (x 8 6 && x 8 13)
                        clear * - r29052 b29053 b29054 d29043
                        omega
                      have d29055 : (x 8 5).toNat = 0 := by
                        have r29056 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
                        have b29057 := hb (x 8 5)
                        have b29058 := hb (x 8 13)
                        clear * - r29056 b29057 b29058 d29043
                        omega
                      have d29059 : (x 8 5 && x 8 14).toNat = 0 := by
                        have r29060 := hand1 (x 8 5) (x 8 14)
                        have b29061 := hb (x 8 5)
                        have b29062 := hb (x 8 5 && x 8 14)
                        clear * - r29060 b29061 b29062 d29055
                        omega
                      have d29063 : (x 8 5 && x 8 10).toNat = 0 := by
                        have r29064 := hand1 (x 8 5) (x 8 10)
                        have b29065 := hb (x 8 5)
                        have b29066 := hb (x 8 5 && x 8 10)
                        clear * - r29064 b29065 b29066 d29055
                        omega
                      have d29067 : (x 8 5 && x 8 6).toNat = 0 := by
                        have r29068 := hand1 (x 8 5) (x 8 6)
                        have b29069 := hb (x 8 5)
                        have b29070 := hb (x 8 5 && x 8 6)
                        clear * - r29068 b29069 b29070 d29055
                        omega
                      have d29071 : (x 7 2).toNat = 0 := by
                        have r29072 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29073 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                        have e29074 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                        have b29075 := hb (x 6 3)
                        have b29076 := hb (x 7 2)
                        have b29077 := hb (x 8 13)
                        have b29078 := hb (x 9 12)
                        clear * - r29072 e29073 e29074 b29075 b29076 b29077 b29078 d29015 d29043 d29011
                        omega
                      have d29079 : (x 7 2 && x 7 11).toNat = 0 := by
                        have r29080 := hand1 (x 7 2) (x 7 11)
                        have b29081 := hb (x 7 2)
                        have b29082 := hb (x 7 2 && x 7 11)
                        clear * - r29080 b29081 b29082 d29071
                        omega
                      have d29083 : (x 7 2 && x 7 7).toNat = 0 := by
                        have r29084 := hand1 (x 7 2) (x 7 7)
                        have b29085 := hb (x 7 2)
                        have b29086 := hb (x 7 2 && x 7 7)
                        clear * - r29084 b29085 b29086 d29071
                        omega
                      have d29087 : (x 7 10).toNat = 0 := by
                        have r29088 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
                        have b29089 := hb (x 7 2)
                        have b29090 := hb (x 7 10)
                        clear * - r29088 b29089 b29090 d29071
                        omega
                      have d29091 : (x 4 5).toNat = 0 := by
                        have r29092 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
                        have b29093 := hb (x 4 5)
                        have b29094 := hb (x 4 13)
                        clear * - r29092 b29093 b29094 d28992
                        omega
                      have d29095 : (x 4 5 && x 4 14).toNat = 0 := by
                        have r29096 := hand1 (x 4 5) (x 4 14)
                        have b29097 := hb (x 4 5)
                        have b29098 := hb (x 4 5 && x 4 14)
                        clear * - r29096 b29097 b29098 d29091
                        omega
                      have d29099 : (x 9 8).toNat = 0 := by
                        have r29100 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29101 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                        have e29102 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                        have e29103 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                        have e29104 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                        have e29105 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                        have e29106 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                        have b29107 := hb (x 2 7)
                        have b29108 := hb (x 3 6)
                        have b29109 := hb (x 4 5)
                        have b29110 := hb (x 5 4)
                        have b29111 := hb (x 6 11)
                        have b29112 := hb (x 7 10)
                        have b29113 := hb (x 8 9)
                        have b29114 := hb (x 9 8)
                        clear * - r29100 e29101 e29102 e29103 e29104 e29105 e29106 b29107 b29108 b29109 b29110 b29111 b29112 b29113 b29114 d29087 d29004 d28984 d29091 d28835
                        omega
                      have d29115 : (x 8 9).toNat = 0 := by
                        have r29116 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29117 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                        have e29118 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                        have e29119 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                        have e29120 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                        have e29121 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                        have e29122 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                        have b29123 := hb (x 2 7)
                        have b29124 := hb (x 3 6)
                        have b29125 := hb (x 4 5)
                        have b29126 := hb (x 5 4)
                        have b29127 := hb (x 6 11)
                        have b29128 := hb (x 7 10)
                        have b29129 := hb (x 8 9)
                        have b29130 := hb (x 9 8)
                        clear * - r29116 e29117 e29118 e29119 e29120 e29121 e29122 b29123 b29124 b29125 b29126 b29127 b29128 b29129 b29130 d29099 d29087 d29004 d28984 d29091 d28835
                        omega
                      have d29131 : (x 2 7).toNat = 0 := by
                        have r29132 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29133 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                        have e29134 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                        have e29135 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                        have e29136 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                        have e29137 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                        have e29138 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                        have b29139 := hb (x 2 7)
                        have b29140 := hb (x 3 6)
                        have b29141 := hb (x 4 5)
                        have b29142 := hb (x 5 4)
                        have b29143 := hb (x 6 11)
                        have b29144 := hb (x 7 10)
                        have b29145 := hb (x 8 9)
                        have b29146 := hb (x 9 8)
                        clear * - r29132 e29133 e29134 e29135 e29136 e29137 e29138 b29139 b29140 b29141 b29142 b29143 b29144 b29145 b29146 d29099 d29115 d29087 d29004 d28984 d29091 d28835
                        omega
                      have d29147 : (x 2 7 && x 2 12).toNat = 0 := by
                        have r29148 := hand1 (x 2 7) (x 2 12)
                        have b29149 := hb (x 2 7)
                        have b29150 := hb (x 2 7 && x 2 12)
                        clear * - r29148 b29149 b29150 d29131
                        omega
                      have r29151 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r29152 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r29153 : (x 17 1).toNat + (x 16 2).toNat + (x 15 3).toNat + (x 14 4).toNat + (x 13 5).toNat + (x 12 6).toNat + (x 11 7).toNat + (x 10 8).toNat + (x 9 9).toNat + (x 8 10).toNat + (x 7 11).toNat + (x 6 12).toNat + (x 5 13).toNat + (x 4 14).toNat = 3 := by have q := hcount 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r29154 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e29155 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                      have e29156 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                      have e29157 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                      have e29158 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                      have e29159 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                      have e29160 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                      have r29161 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e29162 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
                      have e29163 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
                      have e29164 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
                      have e29165 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
                      have e29166 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
                      have e29167 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
                      have r29168 : 1 ≤ (x 13 1).toNat + (x 12 1 && x 12 2).toNat + (x 11 2 && x 11 3).toNat + (x 10 3 && x 10 4).toNat + (x 9 4 && x 9 5).toNat + (x 8 5 && x 8 6).toNat + (x 7 6 && x 7 7).toNat + (x 6 7 && x 6 8).toNat + (x 5 8 && x 5 9).toNat + (x 4 9 && x 4 10).toNat + (x 3 10 && x 3 11).toNat + (x 2 11 && x 2 12).toNat + (x 1 12 && x 1 13).toNat + (x 0 13 && x 0 14).toNat + (x (-1) 14).toNat := by have q := hcov1 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r29169 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r29170 : 1 ≤ (x 13 5).toNat + (x 12 1 && x 12 6).toNat + (x 11 2 && x 11 7).toNat + (x 10 3 && x 10 8).toNat + (x 9 4 && x 9 9).toNat + (x 8 5 && x 8 10).toNat + (x 7 6 && x 7 11).toNat + (x 6 7 && x 6 12).toNat + (x 5 8 && x 5 13).toNat + (x 4 9 && x 4 14).toNat + (x 3 10).toNat := by have q := hcov5 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r29171 : 1 ≤ (x 14 7).toNat + (x 13 1 && x 13 8).toNat + (x 12 2 && x 12 9).toNat + (x 11 3 && x 11 10).toNat + (x 10 4 && x 10 11).toNat + (x 9 5 && x 9 12).toNat + (x 8 6 && x 8 13).toNat + (x 7 7 && x 7 14).toNat + (x 6 8).toNat := by have q := hcov7 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r29172 : 1 ≤ (x 9 9).toNat + (x 8 1 && x 8 10).toNat + (x 7 2 && x 7 11).toNat + (x 6 3 && x 6 12).toNat + (x 5 4 && x 5 13).toNat + (x 4 5 && x 4 14).toNat + (x 3 6).toNat := by have q := hcov9 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r29173 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r29174 : 1 ≤ (x 18 11).toNat + (x 17 1 && x 17 12).toNat + (x 16 2 && x 16 13).toNat + (x 15 3 && x 15 14).toNat + (x 14 4).toNat := by have q := hcov11 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r29175 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r29176 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r29177 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                      have r29178 := hand2 (x 12 1) (x 12 2)
                      have r29179 := hand2 (x 11 2) (x 11 3)
                      have r29180 := hand2 (x 10 3) (x 10 4)
                      have r29181 := hand2 (x 7 6) (x 7 7)
                      have r29182 := hand1 (x 2 11) (x 2 12)
                      have r29183 := hand2 (x 8 1) (x 8 6)
                      have r29184 := hand2 (x 12 1) (x 12 6)
                      have r29185 := hand2 (x 11 2) (x 11 7)
                      have r29186 := hand2 (x 10 3) (x 10 8)
                      have r29187 := hand2 (x 7 6) (x 7 11)
                      have r29188 := hand1 (x 6 7) (x 6 12)
                      have r29189 := hand1 (x 5 8) (x 5 13)
                      have r29190 := hand1 (x 4 9) (x 4 14)
                      have r29191 := hand1 (x 13 1) (x 13 8)
                      have r29192 := hand1 (x 12 2) (x 12 9)
                      have r29193 := hand1 (x 11 3) (x 11 10)
                      have r29194 := hand1 (x 10 4) (x 10 11)
                      have r29195 := hand1 (x 7 7) (x 7 14)
                      have r29196 := hand2 (x 8 1) (x 8 10)
                      have r29197 := hand2 (x 6 3) (x 6 12)
                      have r29198 := hand2 (x 12 1) (x 12 10)
                      have r29199 := hand2 (x 11 2) (x 11 11)
                      have r29200 := hand1 (x 10 3) (x 10 12)
                      have r29201 := hand1 (x 17 1) (x 17 12)
                      have r29202 := hand1 (x 16 2) (x 16 13)
                      have r29203 := hand1 (x 15 3) (x 15 14)
                      have r29204 := hand2 (x 4 1) (x 4 14)
                      have r29205 := hand1 (x 12 1) (x 12 14)
                      linarith only [r29151, r29152, r29153, r29154, e29155, e29156, e29157, e29158, e29159, e29160, r29161, e29162, e29163, e29164, e29165, e29166, e29167, r29168, r29169, r29170, r29171, r29172, r29173, r29174, r29175, r29176, r29177, r29178, r29179, r29180, r29181, r29182, r29183, r29184, r29185, r29186, r29187, r29188, r29189, r29190, r29191, r29192, r29193, r29194, r29195, r29196, r29197, r29198, r29199, r29200, r29201, r29202, r29203, r29204, r29205, d28867, g6, g7, d28885, d28905, d28843, d28835, d28847, g10, g11, g12, g13, d29055, d29027, d29039, d29067, g14, g15, g16, g17, d28901, d27895, d29083, g27, g28, g29, g30, d29147, d28897, d28873, d29035, d29063, d29023, d29051, d29079, d28988, d29095, d29031, d29059]
                    · have f29317 : (x (-1) 6).toNat = 1 := by rw [h28957]; rfl
                      have d29318 : (x (-1) 14).toNat = 1 := by
                        have r29319 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
                        have b29320 := hb (x (-1) 6)
                        have b29321 := hb (x (-1) 14)
                        clear * - r29319 b29320 b29321 f29317
                        omega
                      have d29322 : (x (-2) 1).toNat = 0 := by
                        have r29323 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b29324 := hb (x (-2) 1)
                        have b29325 := hb (x (-1) 14)
                        clear * - r29323 b29324 b29325 d29318
                        omega
                      have d29326 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                        have r29327 := hand1 (x (-2) 1) (x (-2) 14)
                        have b29328 := hb (x (-2) 1)
                        have b29329 := hb (x (-2) 1 && x (-2) 14)
                        clear * - r29327 b29328 b29329 d29322
                        omega
                      have d29330 : (x (-2) 13).toNat = 0 := by
                        have r29331 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                        have b29332 := hb (x (-2) 1)
                        have b29333 := hb (x (-2) 13)
                        clear * - r29331 b29332 b29333 d29322
                        omega
                      have d29334 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
                        have r29335 := hand2 (x (-2) 2) (x (-2) 13)
                        have b29336 := hb (x (-2) 13)
                        have b29337 := hb (x (-2) 2 && x (-2) 13)
                        clear * - r29335 b29336 b29337 d29330
                        omega
                      have d29338 : (x (-3) 2).toNat = 1 := by
                        have r29339 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b29340 := hb (x (-3) 2)
                        have b29341 := hb (x (-1) 13)
                        have b29342 := hb (x (-2) 1 && x (-2) 14)
                        clear * - r29339 b29340 b29341 b29342 g2 d29326
                        omega
                      have d29343 : (x (-3) 14).toNat = 1 := by
                        have r29344 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                        have b29345 := hb (x (-3) 2)
                        have b29346 := hb (x (-3) 14)
                        clear * - r29344 b29345 b29346 d29338
                        omega
                      have d29347 : (x (-4) 1).toNat = 0 := by
                        have r29348 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b29349 := hb (x (-4) 1)
                        have b29350 := hb (x (-3) 14)
                        clear * - r29348 b29349 b29350 d29343
                        omega
                      have d29351 : (x (-4) 13).toNat = 0 := by
                        have r29352 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
                        have b29353 := hb (x (-4) 1)
                        have b29354 := hb (x (-4) 13)
                        clear * - r29352 b29353 b29354 d29347
                        omega
                      have d29355 : (x (-4) 2).toNat = 1 := by
                        have r29356 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b29357 := hb (x (-4) 2)
                        have b29358 := hb (x (-2) 13)
                        have b29359 := hb (x (-3) 1 && x (-3) 14)
                        clear * - r29356 b29357 b29358 b29359 d29330 d27924
                        omega
                      have d29360 : (x (-4) 14).toNat = 1 := by
                        have r29361 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                        have b29362 := hb (x (-4) 2)
                        have b29363 := hb (x (-4) 14)
                        clear * - r29361 b29362 b29363 d29355
                        omega
                      have d29364 : (x (-5) 1).toNat = 0 := by
                        have r29365 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b29366 := hb (x (-5) 1)
                        have b29367 := hb (x (-4) 14)
                        clear * - r29365 b29366 b29367 d29360
                        omega
                      have d29368 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
                        have r29369 := hand1 (x (-5) 1) (x (-5) 14)
                        have b29370 := hb (x (-5) 1)
                        have b29371 := hb (x (-5) 1 && x (-5) 14)
                        clear * - r29369 b29370 b29371 d29364
                        omega
                      have d29372 : (x (-5) 13).toNat = 0 := by
                        have r29373 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
                        have b29374 := hb (x (-5) 1)
                        have b29375 := hb (x (-5) 13)
                        clear * - r29373 b29374 b29375 d29364
                        omega
                      have d29376 : (x (-6) 2).toNat = 1 := by
                        have r29377 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b29378 := hb (x (-6) 2)
                        have b29379 := hb (x (-4) 13)
                        have b29380 := hb (x (-5) 1 && x (-5) 14)
                        clear * - r29377 b29378 b29379 b29380 d29351 d29368
                        omega
                      have d29381 : (x (-4) 12).toNat = 0 := by
                        have r29382 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29383 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                        have e29384 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                        have b29385 := hb (x (-7) 3)
                        have b29386 := hb (x (-6) 2)
                        have b29387 := hb (x (-5) 13)
                        have b29388 := hb (x (-4) 12)
                        clear * - r29382 e29383 e29384 b29385 b29386 b29387 b29388 d29372 d29376
                        omega
                      have d29389 : (x (-4) 4).toNat = 0 := by
                        have r29390 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
                        have b29391 := hb (x (-4) 4)
                        have b29392 := hb (x (-4) 12)
                        clear * - r29390 b29391 b29392 d29381
                        omega
                      have r29393 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b29394 := hb (x (-4) 4)
                      have b29395 := hb (x 0 11)
                      have b29396 := hb (x (-1) 1 && x (-1) 12)
                      have b29397 := hb (x (-2) 2 && x (-2) 13)
                      have b29398 := hb (x (-3) 3 && x (-3) 14)
                      linarith only [r29393, b29394, b29395, b29396, b29397, b29398, g5, g44, d29334, d27980, d29389]
                  · have f29399 : (x 1 4).toNat = 1 := by rw [h28955]; rfl
                    have d29400 : (x 1 12).toNat = 1 := by
                      have r29401 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
                      have b29402 := hb (x 1 4)
                      have b29403 := hb (x 1 12)
                      clear * - r29401 b29402 b29403 f29399
                      omega
                    have d29404 : (x (-2) 3).toNat = 0 := by
                      have r29405 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e29406 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                      have e29407 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                      have b29408 := hb (x (-2) 3)
                      have b29409 := hb (x (-1) 2)
                      have b29410 := hb (x 0 13)
                      have b29411 := hb (x 1 12)
                      clear * - r29405 e29406 e29407 b29408 b29409 b29410 b29411 d29400 g6 f28858
                      omega
                    have d29412 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
                      have r29413 := hand1 (x (-2) 3) (x (-2) 14)
                      have b29414 := hb (x (-2) 3)
                      have b29415 := hb (x (-2) 3 && x (-2) 14)
                      clear * - r29413 b29414 b29415 d29404
                      omega
                    have d29416 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
                      have r29417 := hand1 (x (-2) 3) (x (-2) 13)
                      have b29418 := hb (x (-2) 3)
                      have b29419 := hb (x (-2) 3 && x (-2) 13)
                      clear * - r29417 b29418 b29419 d29404
                      omega
                    have d29420 : (x (-3) 4).toNat = 1 := by
                      have r29421 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b29422 := hb (x (-3) 4)
                      have b29423 := hb (x 1 11)
                      have b29424 := hb (x 0 1 && x 0 12)
                      have b29425 := hb (x (-1) 2 && x (-1) 13)
                      have b29426 := hb (x (-2) 3 && x (-2) 14)
                      clear * - r29421 b29422 b29423 b29424 b29425 b29426 d28949 d27960 g45 d29412
                      omega
                    have d29427 : (x (-3) 12).toNat = 1 := by
                      have r29428 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
                      have b29429 := hb (x (-3) 4)
                      have b29430 := hb (x (-3) 12)
                      clear * - r29428 b29429 b29430 d29420
                      omega
                    have d29431 : (x (-4) 13).toNat = 0 := by
                      have r29432 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e29433 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                      have e29434 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                      have b29435 := hb (x (-6) 3)
                      have b29436 := hb (x (-5) 2)
                      have b29437 := hb (x (-4) 13)
                      have b29438 := hb (x (-3) 12)
                      clear * - r29432 e29433 e29434 b29435 b29436 b29437 b29438 d29427
                      omega
                    have d29439 : (x (-4) 5).toNat = 0 := by
                      have r29440 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
                      have b29441 := hb (x (-4) 5)
                      have b29442 := hb (x (-4) 13)
                      clear * - r29440 b29441 b29442 d29431
                      omega
                    have d29443 : (x (-5) 2).toNat = 0 := by
                      have r29444 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e29445 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                      have e29446 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                      have b29447 := hb (x (-6) 3)
                      have b29448 := hb (x (-5) 2)
                      have b29449 := hb (x (-4) 13)
                      have b29450 := hb (x (-3) 12)
                      clear * - r29444 e29445 e29446 b29447 b29448 b29449 b29450 d29427 d29431
                      omega
                    have d29451 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
                      have r29452 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b29453 := hb (x (-5) 2)
                      have b29454 := hb (x (-3) 13)
                      have b29455 := hb (x (-4) 1 && x (-4) 14)
                      clear * - r29452 b29453 b29454 b29455 d27932 d29443
                      omega
                    have d29456 : (x (-4) 1).toNat = 1 := by
                      have r29457 := hand1 (x (-4) 1) (x (-4) 14)
                      have b29458 := hb (x (-4) 1)
                      have b29459 := hb (x (-4) 1 && x (-4) 14)
                      clear * - r29457 b29458 b29459 d29451
                      omega
                    have d29460 : (x (-3) 14).toNat = 0 := by
                      have r29461 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b29462 := hb (x (-4) 1)
                      have b29463 := hb (x (-3) 14)
                      clear * - r29461 b29462 b29463 d29456
                      omega
                    have d29464 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
                      have r29465 := hand2 (x (-3) 4) (x (-3) 14)
                      have b29466 := hb (x (-3) 14)
                      have b29467 := hb (x (-3) 4 && x (-3) 14)
                      clear * - r29465 b29466 b29467 d29460
                      omega
                    have r29468 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29469 := hb (x (-4) 5)
                    have b29470 := hb (x 1 10)
                    have b29471 := hb (x 0 1 && x 0 11)
                    have b29472 := hb (x (-1) 2 && x (-1) 12)
                    have b29473 := hb (x (-2) 3 && x (-2) 13)
                    have b29474 := hb (x (-3) 4 && x (-3) 14)
                    linarith only [r29468, b29469, b29470, b29471, b29472, b29473, b29474, d28792, g41, d28859, d29416, d29464, d29439]
                · have f29475 : (x (-1) 4).toNat = 1 := by rw [h28953]; rfl
                  have d29476 : (x (-1) 12).toNat = 1 := by
                    have r29477 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                    have b29478 := hb (x (-1) 4)
                    have b29479 := hb (x (-1) 12)
                    clear * - r29477 b29478 b29479 f29475
                    omega
                  have d29480 : (x (-2) 13).toNat = 0 := by
                    have r29481 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29482 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                    have e29483 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                    have b29484 := hb (x (-4) 3)
                    have b29485 := hb (x (-3) 2)
                    have b29486 := hb (x (-2) 13)
                    have b29487 := hb (x (-1) 12)
                    clear * - r29481 e29482 e29483 b29484 b29485 b29486 b29487 d29476
                    omega
                  have d29488 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
                    have r29489 := hand2 (x (-2) 2) (x (-2) 13)
                    have b29490 := hb (x (-2) 13)
                    have b29491 := hb (x (-2) 2 && x (-2) 13)
                    clear * - r29489 b29490 b29491 d29480
                    omega
                  have d29492 : (x (-4) 2).toNat = 1 := by
                    have r29493 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29494 := hb (x (-4) 2)
                    have b29495 := hb (x (-2) 13)
                    have b29496 := hb (x (-3) 1 && x (-3) 14)
                    clear * - r29493 b29494 b29495 b29496 d29480 d27924
                    omega
                  have d29497 : (x (-4) 14).toNat = 1 := by
                    have r29498 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                    have b29499 := hb (x (-4) 2)
                    have b29500 := hb (x (-4) 14)
                    clear * - r29498 b29499 b29500 d29492
                    omega
                  have d29501 : (x (-5) 1).toNat = 0 := by
                    have r29502 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29503 := hb (x (-5) 1)
                    have b29504 := hb (x (-4) 14)
                    clear * - r29502 b29503 b29504 d29497
                    omega
                  have d29505 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
                    have r29506 := hand1 (x (-5) 1) (x (-5) 14)
                    have b29507 := hb (x (-5) 1)
                    have b29508 := hb (x (-5) 1 && x (-5) 14)
                    clear * - r29506 b29507 b29508 d29501
                    omega
                  have d29509 : (x (-5) 13).toNat = 0 := by
                    have r29510 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
                    have b29511 := hb (x (-5) 1)
                    have b29512 := hb (x (-5) 13)
                    clear * - r29510 b29511 b29512 d29501
                    omega
                  have d29513 : (x (-3) 2).toNat = 0 := by
                    have r29514 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29515 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                    have e29516 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                    have b29517 := hb (x (-4) 3)
                    have b29518 := hb (x (-3) 2)
                    have b29519 := hb (x (-2) 13)
                    have b29520 := hb (x (-1) 12)
                    clear * - r29514 e29515 e29516 b29517 b29518 b29519 b29520 d29476 d29480
                    omega
                  have d29521 : (x (-4) 3).toNat = 0 := by
                    have r29522 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29523 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                    have e29524 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                    have b29525 := hb (x (-4) 3)
                    have b29526 := hb (x (-3) 2)
                    have b29527 := hb (x (-2) 13)
                    have b29528 := hb (x (-1) 12)
                    clear * - r29522 e29523 e29524 b29525 b29526 b29527 b29528 d29476 d29480 d29513
                    omega
                  have d29529 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                    have r29530 := hand1 (x (-4) 3) (x (-4) 14)
                    have b29531 := hb (x (-4) 3)
                    have b29532 := hb (x (-4) 3 && x (-4) 14)
                    clear * - r29530 b29531 b29532 d29521
                    omega
                  have d29533 : (x (-2) 12).toNat = 0 := by
                    have r29534 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29535 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                    have e29536 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                    have b29537 := hb (x (-5) 3)
                    have b29538 := hb (x (-4) 2)
                    have b29539 := hb (x (-3) 13)
                    have b29540 := hb (x (-2) 12)
                    clear * - r29534 e29535 e29536 b29537 b29538 b29539 b29540 d27932 d29492
                    omega
                  have d29541 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
                    have r29542 := hand2 (x (-2) 1) (x (-2) 12)
                    have b29543 := hb (x (-2) 12)
                    have b29544 := hb (x (-2) 1 && x (-2) 12)
                    clear * - r29542 b29543 b29544 d29533
                    omega
                  have d29545 : (x (-5) 3).toNat = 0 := by
                    have r29546 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29547 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                    have e29548 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                    have b29549 := hb (x (-5) 3)
                    have b29550 := hb (x (-4) 2)
                    have b29551 := hb (x (-3) 13)
                    have b29552 := hb (x (-2) 12)
                    clear * - r29546 e29547 e29548 b29549 b29550 b29551 b29552 d29533 d27932 d29492
                    omega
                  have d29553 : (x (-5) 11).toNat = 0 := by
                    have r29554 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
                    have b29555 := hb (x (-5) 3)
                    have b29556 := hb (x (-5) 11)
                    clear * - r29554 b29555 b29556 d29545
                    omega
                  have d29557 : (x (-4) 4).toNat = 1 := by
                    have r29558 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29559 := hb (x (-4) 4)
                    have b29560 := hb (x 0 11)
                    have b29561 := hb (x (-1) 1 && x (-1) 12)
                    have b29562 := hb (x (-2) 2 && x (-2) 13)
                    have b29563 := hb (x (-3) 3 && x (-3) 14)
                    clear * - r29558 b29559 b29560 b29561 b29562 b29563 g5 g44 d29488 d27980
                    omega
                  have d29564 : (x (-4) 12).toNat = 1 := by
                    have r29565 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
                    have b29566 := hb (x (-4) 4)
                    have b29567 := hb (x (-4) 12)
                    clear * - r29565 b29566 b29567 d29557
                    omega
                  have d29568 : (x (-6) 2).toNat = 0 := by
                    have r29569 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29570 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                    have e29571 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                    have b29572 := hb (x (-7) 3)
                    have b29573 := hb (x (-6) 2)
                    have b29574 := hb (x (-5) 13)
                    have b29575 := hb (x (-4) 12)
                    clear * - r29569 e29570 e29571 b29572 b29573 b29574 b29575 d29564 d29509
                    omega
                  have d29576 : (x (-4) 13).toNat = 1 := by
                    have r29577 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29578 := hb (x (-6) 2)
                    have b29579 := hb (x (-4) 13)
                    have b29580 := hb (x (-5) 1 && x (-5) 14)
                    clear * - r29577 b29578 b29579 b29580 d29505 d29568
                    omega
                  have d29581 : (x (-3) 12).toNat = 0 := by
                    have r29582 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29583 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                    have e29584 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                    have b29585 := hb (x (-6) 3)
                    have b29586 := hb (x (-5) 2)
                    have b29587 := hb (x (-4) 13)
                    have b29588 := hb (x (-3) 12)
                    clear * - r29582 e29583 e29584 b29585 b29586 b29587 b29588 d29576
                    omega
                  have d29589 : (x (-5) 2).toNat = 0 := by
                    have r29590 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29591 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                    have e29592 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                    have b29593 := hb (x (-6) 3)
                    have b29594 := hb (x (-5) 2)
                    have b29595 := hb (x (-4) 13)
                    have b29596 := hb (x (-3) 12)
                    clear * - r29590 e29591 e29592 b29593 b29594 b29595 b29596 d29581 d29576
                    omega
                  have d29597 : (x (-5) 10).toNat = 0 := by
                    have r29598 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
                    have b29599 := hb (x (-5) 2)
                    have b29600 := hb (x (-5) 10)
                    clear * - r29598 b29599 b29600 d29589
                    omega
                  have d29601 : (x (-6) 3).toNat = 0 := by
                    have r29602 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29603 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                    have e29604 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                    have b29605 := hb (x (-6) 3)
                    have b29606 := hb (x (-5) 2)
                    have b29607 := hb (x (-4) 13)
                    have b29608 := hb (x (-3) 12)
                    clear * - r29602 e29603 e29604 b29605 b29606 b29607 b29608 d29581 d29576 d29589
                    omega
                  have d29609 : (x (-6) 11).toNat = 0 := by
                    have r29610 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
                    have b29611 := hb (x (-6) 3)
                    have b29612 := hb (x (-6) 11)
                    clear * - r29610 b29611 b29612 d29601
                    omega
                  have d29613 : (x (-6) 1 && x (-6) 11).toNat = 0 := by
                    have r29614 := hand2 (x (-6) 1) (x (-6) 11)
                    have b29615 := hb (x (-6) 11)
                    have b29616 := hb (x (-6) 1 && x (-6) 11)
                    clear * - r29614 b29615 b29616 d29609
                    omega
                  have d29617 : (x (-5) 4).toNat = 1 := by
                    have r29618 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29619 := hb (x (-5) 4)
                    have b29620 := hb (x (-1) 11)
                    have b29621 := hb (x (-2) 1 && x (-2) 12)
                    have b29622 := hb (x (-3) 2 && x (-3) 13)
                    have b29623 := hb (x (-4) 3 && x (-4) 14)
                    clear * - r29618 b29619 b29620 b29621 b29622 b29623 d28879 d29541 d27936 d29529
                    omega
                  have d29624 : (x (-5) 12).toNat = 1 := by
                    have r29625 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                    have b29626 := hb (x (-5) 4)
                    have b29627 := hb (x (-5) 12)
                    clear * - r29625 b29626 b29627 d29617
                    omega
                  have d29628 : (x (-6) 13).toNat = 0 := by
                    have r29629 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29630 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                    have e29631 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                    have b29632 := hb (x (-8) 3)
                    have b29633 := hb (x (-7) 2)
                    have b29634 := hb (x (-6) 13)
                    have b29635 := hb (x (-5) 12)
                    clear * - r29629 e29630 e29631 b29632 b29633 b29634 b29635 d29624
                    omega
                  have d29636 : (x (-7) 2).toNat = 0 := by
                    have r29637 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29638 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                    have e29639 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                    have b29640 := hb (x (-8) 3)
                    have b29641 := hb (x (-7) 2)
                    have b29642 := hb (x (-6) 13)
                    have b29643 := hb (x (-5) 12)
                    clear * - r29637 e29638 e29639 b29640 b29641 b29642 b29643 d29624 d29628
                    omega
                  have d29644 : (x (-7) 2 && x (-7) 13).toNat = 0 := by
                    have r29645 := hand1 (x (-7) 2) (x (-7) 13)
                    have b29646 := hb (x (-7) 2)
                    have b29647 := hb (x (-7) 2 && x (-7) 13)
                    clear * - r29645 b29646 b29647 d29636
                    omega
                  have d29648 : (x (-7) 2 && x (-7) 12).toNat = 0 := by
                    have r29649 := hand1 (x (-7) 2) (x (-7) 12)
                    have b29650 := hb (x (-7) 2)
                    have b29651 := hb (x (-7) 2 && x (-7) 12)
                    clear * - r29649 b29650 b29651 d29636
                    omega
                  have d29652 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
                    have r29653 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29654 := hb (x (-7) 2)
                    have b29655 := hb (x (-5) 13)
                    have b29656 := hb (x (-6) 1 && x (-6) 14)
                    clear * - r29653 b29654 b29655 b29656 d29509 d29636
                    omega
                  have d29657 : (x (-6) 14).toNat = 1 := by
                    have r29658 := hand2 (x (-6) 1) (x (-6) 14)
                    have b29659 := hb (x (-6) 14)
                    have b29660 := hb (x (-6) 1 && x (-6) 14)
                    clear * - r29658 b29659 b29660 d29652
                    omega
                  have d29661 : (x (-7) 1).toNat = 0 := by
                    have r29662 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29663 := hb (x (-7) 1)
                    have b29664 := hb (x (-6) 14)
                    clear * - r29662 b29663 b29664 d29657
                    omega
                  have d29665 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
                    have r29666 := hand1 (x (-7) 1) (x (-7) 14)
                    have b29667 := hb (x (-7) 1)
                    have b29668 := hb (x (-7) 1 && x (-7) 14)
                    clear * - r29666 b29667 b29668 d29661
                    omega
                  have d29669 : (x (-8) 2).toNat = 1 := by
                    have r29670 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29671 := hb (x (-8) 2)
                    have b29672 := hb (x (-6) 13)
                    have b29673 := hb (x (-7) 1 && x (-7) 14)
                    clear * - r29670 b29671 b29672 b29673 d29628 d29665
                    omega
                  have d29674 : (x (-8) 14).toNat = 1 := by
                    have r29675 : (x (-8) 2).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp2 (-8))
                    have b29676 := hb (x (-8) 2)
                    have b29677 := hb (x (-8) 14)
                    clear * - r29675 b29676 b29677 d29669
                    omega
                  have d29678 : (x (-9) 1).toNat = 0 := by
                    have r29679 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29680 := hb (x (-9) 1)
                    have b29681 := hb (x (-8) 14)
                    clear * - r29679 b29680 b29681 d29674
                    omega
                  have d29682 : (x (-9) 13).toNat = 0 := by
                    have r29683 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
                    have b29684 := hb (x (-9) 1)
                    have b29685 := hb (x (-9) 13)
                    clear * - r29683 b29684 b29685 d29678
                    omega
                  have d29686 : (x (-6) 12).toNat = 0 := by
                    have r29687 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29688 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                    have e29689 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                    have b29690 := hb (x (-9) 3)
                    have b29691 := hb (x (-8) 2)
                    have b29692 := hb (x (-7) 13)
                    have b29693 := hb (x (-6) 12)
                    clear * - r29687 e29688 e29689 b29690 b29691 b29692 b29693 d29669
                    omega
                  have d29694 : (x (-6) 1 && x (-6) 12).toNat = 0 := by
                    have r29695 := hand2 (x (-6) 1) (x (-6) 12)
                    have b29696 := hb (x (-6) 12)
                    have b29697 := hb (x (-6) 1 && x (-6) 12)
                    clear * - r29695 b29696 b29697 d29686
                    omega
                  have d29698 : (x (-8) 3).toNat = 0 := by
                    have r29699 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29700 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                    have e29701 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                    have b29702 := hb (x (-8) 3)
                    have b29703 := hb (x (-7) 2)
                    have b29704 := hb (x (-6) 13)
                    have b29705 := hb (x (-5) 12)
                    clear * - r29699 e29700 e29701 b29702 b29703 b29704 b29705 d29624 d29628 d29636
                    omega
                  have d29706 : (x (-8) 3 && x (-8) 14).toNat = 0 := by
                    have r29707 := hand1 (x (-8) 3) (x (-8) 14)
                    have b29708 := hb (x (-8) 3)
                    have b29709 := hb (x (-8) 3 && x (-8) 14)
                    clear * - r29707 b29708 b29709 d29698
                    omega
                  have d29710 : (x (-8) 3 && x (-8) 13).toNat = 0 := by
                    have r29711 := hand1 (x (-8) 3) (x (-8) 13)
                    have b29712 := hb (x (-8) 3)
                    have b29713 := hb (x (-8) 3 && x (-8) 13)
                    clear * - r29711 b29712 b29713 d29698
                    omega
                  have d29714 : (x (-9) 4).toNat = 1 := by
                    have r29715 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29716 := hb (x (-9) 4)
                    have b29717 := hb (x (-5) 11)
                    have b29718 := hb (x (-6) 1 && x (-6) 12)
                    have b29719 := hb (x (-7) 2 && x (-7) 13)
                    have b29720 := hb (x (-8) 3 && x (-8) 14)
                    clear * - r29715 b29716 b29717 b29718 b29719 b29720 d29553 d29694 d29644 d29706
                    omega
                  have d29721 : (x (-9) 12).toNat = 1 := by
                    have r29722 : (x (-9) 4).toNat ≤ (x (-9) 12).toNat := himp _ _ (hp4 (-9))
                    have b29723 := hb (x (-9) 4)
                    have b29724 := hb (x (-9) 12)
                    clear * - r29722 b29723 b29724 d29714
                    omega
                  have d29725 : (x (-10) 13).toNat = 0 := by
                    have r29726 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29727 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
                    have e29728 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
                    have b29729 := hb (x (-12) 3)
                    have b29730 := hb (x (-11) 2)
                    have b29731 := hb (x (-10) 13)
                    have b29732 := hb (x (-9) 12)
                    clear * - r29726 e29727 e29728 b29729 b29730 b29731 b29732 d29721
                    omega
                  have d29733 : (x (-10) 5).toNat = 0 := by
                    have r29734 : (x (-10) 5).toNat ≤ (x (-10) 13).toNat := himp _ _ (hp5 (-10))
                    have b29735 := hb (x (-10) 5)
                    have b29736 := hb (x (-10) 13)
                    clear * - r29734 b29735 b29736 d29725
                    omega
                  have d29737 : (x (-11) 2).toNat = 0 := by
                    have r29738 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29739 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
                    have e29740 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
                    have b29741 := hb (x (-12) 3)
                    have b29742 := hb (x (-11) 2)
                    have b29743 := hb (x (-10) 13)
                    have b29744 := hb (x (-9) 12)
                    clear * - r29738 e29739 e29740 b29741 b29742 b29743 b29744 d29721 d29725
                    omega
                  have d29745 : (x (-10) 1 && x (-10) 14).toNat = 1 := by
                    have r29746 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29747 := hb (x (-11) 2)
                    have b29748 := hb (x (-9) 13)
                    have b29749 := hb (x (-10) 1 && x (-10) 14)
                    clear * - r29746 b29747 b29748 b29749 d29682 d29737
                    omega
                  have d29750 : (x (-10) 1).toNat = 1 := by
                    have r29751 := hand1 (x (-10) 1) (x (-10) 14)
                    have b29752 := hb (x (-10) 1)
                    have b29753 := hb (x (-10) 1 && x (-10) 14)
                    clear * - r29751 b29752 b29753 d29745
                    omega
                  have d29754 : (x (-9) 14).toNat = 0 := by
                    have r29755 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29756 := hb (x (-10) 1)
                    have b29757 := hb (x (-9) 14)
                    clear * - r29755 b29756 b29757 d29750
                    omega
                  have d29758 : (x (-9) 4 && x (-9) 14).toNat = 0 := by
                    have r29759 := hand2 (x (-9) 4) (x (-9) 14)
                    have b29760 := hb (x (-9) 14)
                    have b29761 := hb (x (-9) 4 && x (-9) 14)
                    clear * - r29759 b29760 b29761 d29754
                    omega
                  have r29762 : 1 ≤ (x (-5) 10).toNat + (x (-6) 1 && x (-6) 11).toNat + (x (-7) 2 && x (-7) 12).toNat + (x (-8) 3 && x (-8) 13).toNat + (x (-9) 4 && x (-9) 14).toNat + (x (-10) 5).toNat := by have q := hcov10 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29763 := hb (x (-10) 5)
                  have b29764 := hb (x (-5) 10)
                  have b29765 := hb (x (-6) 1 && x (-6) 11)
                  have b29766 := hb (x (-7) 2 && x (-7) 12)
                  have b29767 := hb (x (-8) 3 && x (-8) 13)
                  have b29768 := hb (x (-9) 4 && x (-9) 14)
                  linarith only [r29762, b29763, b29764, b29765, b29766, b29767, b29768, d29597, d29613, d29648, d29710, d29758, d29733]
              · have f29769 : (x 1 1).toNat = 1 := by rw [h28883]; rfl
                have d29770 : (x 2 14).toNat = 0 := by
                  have r29771 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29772 := hb (x 1 1)
                  have b29773 := hb (x 2 14)
                  clear * - r29771 b29772 b29773 f29769
                  omega
                have d29774 : (x 2 1 && x 2 14).toNat = 0 := by
                  have r29775 := hand2 (x 2 1) (x 2 14)
                  have b29776 := hb (x 2 14)
                  have b29777 := hb (x 2 1 && x 2 14)
                  clear * - r29775 b29776 b29777 d29770
                  omega
                have d29778 : (x 2 2).toNat = 0 := by
                  have r29779 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
                  have b29780 := hb (x 2 2)
                  have b29781 := hb (x 2 14)
                  clear * - r29779 b29780 b29781 d29770
                  omega
                have d29782 : (x 4 13).toNat = 1 := by
                  have r29783 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29784 := hb (x 2 2)
                  have b29785 := hb (x 4 13)
                  have b29786 := hb (x 3 1 && x 3 14)
                  clear * - r29783 b29784 b29785 b29786 d28823 d29778
                  omega
                have d29787 : (x 4 1).toNat = 1 := by
                  have r29788 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                  have b29789 := hb (x 4 1)
                  have b29790 := hb (x 4 13)
                  clear * - r29788 b29789 b29790 d29782
                  omega
                have d29791 : (x 5 14).toNat = 0 := by
                  have r29792 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29793 := hb (x 4 1)
                  have b29794 := hb (x 5 14)
                  clear * - r29792 b29793 b29794 d29787
                  omega
                have d29795 : (x 5 1 && x 5 14).toNat = 0 := by
                  have r29796 := hand2 (x 5 1) (x 5 14)
                  have b29797 := hb (x 5 14)
                  have b29798 := hb (x 5 1 && x 5 14)
                  clear * - r29796 b29797 b29798 d29791
                  omega
                have d29799 : (x 5 2).toNat = 0 := by
                  have r29800 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                  have b29801 := hb (x 5 2)
                  have b29802 := hb (x 5 14)
                  clear * - r29800 b29801 b29802 d29791
                  omega
                have d29803 : (x 3 13).toNat = 1 := by
                  have r29804 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29805 := hb (x 1 2)
                  have b29806 := hb (x 3 13)
                  have b29807 := hb (x 2 1 && x 2 14)
                  clear * - r29804 b29805 b29806 b29807 d29774 d28776
                  omega
                have d29808 : (x 3 1).toNat = 1 := by
                  have r29809 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
                  have b29810 := hb (x 3 1)
                  have b29811 := hb (x 3 13)
                  clear * - r29809 b29810 b29811 d29803
                  omega
                have d29812 : (x 4 14).toNat = 0 := by
                  have r29813 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29814 := hb (x 3 1)
                  have b29815 := hb (x 4 14)
                  clear * - r29813 b29814 b29815 d29808
                  omega
                have d29816 : (x 4 1 && x 4 14).toNat = 0 := by
                  have r29817 := hand2 (x 4 1) (x 4 14)
                  have b29818 := hb (x 4 14)
                  have b29819 := hb (x 4 1 && x 4 14)
                  clear * - r29817 b29818 b29819 d29812
                  omega
                have d29820 : (x 5 13).toNat = 1 := by
                  have r29821 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29822 := hb (x 3 2)
                  have b29823 := hb (x 5 13)
                  have b29824 := hb (x 4 1 && x 4 14)
                  clear * - r29821 b29822 b29823 b29824 d29816 d28843
                  omega
                have d29825 : (x 5 1).toNat = 1 := by
                  have r29826 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
                  have b29827 := hb (x 5 1)
                  have b29828 := hb (x 5 13)
                  clear * - r29826 b29827 b29828 d29820
                  omega
                have d29829 : (x 6 14).toNat = 0 := by
                  have r29830 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29831 := hb (x 5 1)
                  have b29832 := hb (x 6 14)
                  clear * - r29830 b29831 b29832 d29825
                  omega
                have d29833 : (x 6 1 && x 6 14).toNat = 0 := by
                  have r29834 := hand2 (x 6 1) (x 6 14)
                  have b29835 := hb (x 6 14)
                  have b29836 := hb (x 6 1 && x 6 14)
                  clear * - r29834 b29835 b29836 d29829
                  omega
                have d29837 : (x 7 13).toNat = 1 := by
                  have r29838 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29839 := hb (x 5 2)
                  have b29840 := hb (x 7 13)
                  have b29841 := hb (x 6 1 && x 6 14)
                  clear * - r29838 b29839 b29840 b29841 d29833 d29799
                  omega
                have d29842 : (x 7 1).toNat = 1 := by
                  have r29843 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
                  have b29844 := hb (x 7 1)
                  have b29845 := hb (x 7 13)
                  clear * - r29843 b29844 b29845 d29837
                  omega
                have d29846 : (x 8 14).toNat = 0 := by
                  have r29847 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29848 := hb (x 7 1)
                  have b29849 := hb (x 8 14)
                  clear * - r29847 b29848 b29849 d29842
                  omega
                have d29850 : (x 8 1 && x 8 14).toNat = 0 := by
                  have r29851 := hand2 (x 8 1) (x 8 14)
                  have b29852 := hb (x 8 14)
                  have b29853 := hb (x 8 1 && x 8 14)
                  clear * - r29851 b29852 b29853 d29846
                  omega
                have d29854 : (x 8 2).toNat = 0 := by
                  have r29855 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
                  have b29856 := hb (x 8 2)
                  have b29857 := hb (x 8 14)
                  clear * - r29855 b29856 b29857 d29846
                  omega
                have d29858 : (x 6 2).toNat = 0 := by
                  have r29859 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
                  have b29860 := hb (x 6 2)
                  have b29861 := hb (x 6 14)
                  clear * - r29859 b29860 b29861 d29829
                  omega
                have d29862 : (x 4 2).toNat = 0 := by
                  have r29863 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                  have b29864 := hb (x 4 2)
                  have b29865 := hb (x 4 14)
                  clear * - r29863 b29864 b29865 d29812
                  omega
                have d29866 : (x 6 13).toNat = 1 := by
                  have r29867 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29868 := hb (x 4 2)
                  have b29869 := hb (x 6 13)
                  have b29870 := hb (x 5 1 && x 5 14)
                  clear * - r29867 b29868 b29869 b29870 d29795 d29862
                  omega
                have d29871 : (x 6 1).toNat = 1 := by
                  have r29872 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
                  have b29873 := hb (x 6 1)
                  have b29874 := hb (x 6 13)
                  clear * - r29872 b29873 b29874 d29866
                  omega
                have d29875 : (x 7 14).toNat = 0 := by
                  have r29876 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29877 := hb (x 6 1)
                  have b29878 := hb (x 7 14)
                  clear * - r29876 b29877 b29878 d29871
                  omega
                have d29879 : (x 7 1 && x 7 14).toNat = 0 := by
                  have r29880 := hand2 (x 7 1) (x 7 14)
                  have b29881 := hb (x 7 14)
                  have b29882 := hb (x 7 1 && x 7 14)
                  clear * - r29880 b29881 b29882 d29875
                  omega
                have d29883 : (x 8 13).toNat = 1 := by
                  have r29884 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29885 := hb (x 6 2)
                  have b29886 := hb (x 8 13)
                  have b29887 := hb (x 7 1 && x 7 14)
                  clear * - r29884 b29885 b29886 b29887 d29879 d29858
                  omega
                have d29888 : (x 8 1).toNat = 1 := by
                  have r29889 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
                  have b29890 := hb (x 8 1)
                  have b29891 := hb (x 8 13)
                  clear * - r29889 b29890 b29891 d29883
                  omega
                have d29892 : (x 9 14).toNat = 0 := by
                  have r29893 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29894 := hb (x 8 1)
                  have b29895 := hb (x 9 14)
                  clear * - r29893 b29894 b29895 d29888
                  omega
                have d29896 : (x 9 1 && x 9 14).toNat = 0 := by
                  have r29897 := hand2 (x 9 1) (x 9 14)
                  have b29898 := hb (x 9 14)
                  have b29899 := hb (x 9 1 && x 9 14)
                  clear * - r29897 b29898 b29899 d29892
                  omega
                have d29900 : (x 10 13).toNat = 1 := by
                  have r29901 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29902 := hb (x 8 2)
                  have b29903 := hb (x 10 13)
                  have b29904 := hb (x 9 1 && x 9 14)
                  clear * - r29901 b29902 b29903 b29904 d29896 d29854
                  omega
                have d29905 : (x 10 1).toNat = 1 := by
                  have r29906 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
                  have b29907 := hb (x 10 1)
                  have b29908 := hb (x 10 13)
                  clear * - r29906 b29907 b29908 d29900
                  omega
                have d29909 : (x 11 14).toNat = 0 := by
                  have r29910 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29911 := hb (x 10 1)
                  have b29912 := hb (x 11 14)
                  clear * - r29910 b29911 b29912 d29905
                  omega
                have d29913 : (x 11 1 && x 11 14).toNat = 0 := by
                  have r29914 := hand2 (x 11 1) (x 11 14)
                  have b29915 := hb (x 11 14)
                  have b29916 := hb (x 11 1 && x 11 14)
                  clear * - r29914 b29915 b29916 d29909
                  omega
                have d29917 : (x 11 2).toNat = 0 := by
                  have r29918 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
                  have b29919 := hb (x 11 2)
                  have b29920 := hb (x 11 14)
                  clear * - r29918 b29919 b29920 d29909
                  omega
                have d29921 : (x 9 2).toNat = 0 := by
                  have r29922 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
                  have b29923 := hb (x 9 2)
                  have b29924 := hb (x 9 14)
                  clear * - r29922 b29923 b29924 d29892
                  omega
                have d29925 : (x 7 2).toNat = 0 := by
                  have r29926 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
                  have b29927 := hb (x 7 2)
                  have b29928 := hb (x 7 14)
                  clear * - r29926 b29927 b29928 d29875
                  omega
                have d29929 : (x 9 13).toNat = 1 := by
                  have r29930 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29931 := hb (x 7 2)
                  have b29932 := hb (x 9 13)
                  have b29933 := hb (x 8 1 && x 8 14)
                  clear * - r29930 b29931 b29932 b29933 d29850 d29925
                  omega
                have d29934 : (x 9 1).toNat = 1 := by
                  have r29935 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
                  have b29936 := hb (x 9 1)
                  have b29937 := hb (x 9 13)
                  clear * - r29935 b29936 b29937 d29929
                  omega
                have d29938 : (x 10 14).toNat = 0 := by
                  have r29939 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29940 := hb (x 9 1)
                  have b29941 := hb (x 10 14)
                  clear * - r29939 b29940 b29941 d29934
                  omega
                have d29942 : (x 10 1 && x 10 14).toNat = 0 := by
                  have r29943 := hand2 (x 10 1) (x 10 14)
                  have b29944 := hb (x 10 14)
                  have b29945 := hb (x 10 1 && x 10 14)
                  clear * - r29943 b29944 b29945 d29938
                  omega
                have d29946 : (x 11 13).toNat = 1 := by
                  have r29947 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29948 := hb (x 9 2)
                  have b29949 := hb (x 11 13)
                  have b29950 := hb (x 10 1 && x 10 14)
                  clear * - r29947 b29948 b29949 b29950 d29942 d29921
                  omega
                have d29951 : (x 11 1).toNat = 1 := by
                  have r29952 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
                  have b29953 := hb (x 11 1)
                  have b29954 := hb (x 11 13)
                  clear * - r29952 b29953 b29954 d29946
                  omega
                have d29955 : (x 12 14).toNat = 0 := by
                  have r29956 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29957 := hb (x 11 1)
                  have b29958 := hb (x 12 14)
                  clear * - r29956 b29957 b29958 d29951
                  omega
                have d29959 : (x 12 1 && x 12 14).toNat = 0 := by
                  have r29960 := hand2 (x 12 1) (x 12 14)
                  have b29961 := hb (x 12 14)
                  have b29962 := hb (x 12 1 && x 12 14)
                  clear * - r29960 b29961 b29962 d29955
                  omega
                have d29963 : (x 13 13).toNat = 1 := by
                  have r29964 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29965 := hb (x 11 2)
                  have b29966 := hb (x 13 13)
                  have b29967 := hb (x 12 1 && x 12 14)
                  clear * - r29964 b29965 b29966 b29967 d29959 d29917
                  omega
                have d29968 : (x 13 1).toNat = 1 := by
                  have r29969 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                  have b29970 := hb (x 13 1)
                  have b29971 := hb (x 13 13)
                  clear * - r29969 b29970 b29971 d29963
                  omega
                have d29972 : (x 14 14).toNat = 0 := by
                  have r29973 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29974 := hb (x 13 1)
                  have b29975 := hb (x 14 14)
                  clear * - r29973 b29974 b29975 d29968
                  omega
                have d29976 : (x 14 1 && x 14 14).toNat = 0 := by
                  have r29977 := hand2 (x 14 1) (x 14 14)
                  have b29978 := hb (x 14 14)
                  have b29979 := hb (x 14 1 && x 14 14)
                  clear * - r29977 b29978 b29979 d29972
                  omega
                have d29980 : (x 14 3 && x 14 14).toNat = 0 := by
                  have r29981 := hand2 (x 14 3) (x 14 14)
                  have b29982 := hb (x 14 14)
                  have b29983 := hb (x 14 3 && x 14 14)
                  clear * - r29981 b29982 b29983 d29972
                  omega
                have d29984 : (x 14 2).toNat = 0 := by
                  have r29985 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
                  have b29986 := hb (x 14 2)
                  have b29987 := hb (x 14 14)
                  clear * - r29985 b29986 b29987 d29972
                  omega
                have d29988 : (x 12 2).toNat = 0 := by
                  have r29989 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
                  have b29990 := hb (x 12 2)
                  have b29991 := hb (x 12 14)
                  clear * - r29989 b29990 b29991 d29955
                  omega
                have d29992 : (x 10 2).toNat = 0 := by
                  have r29993 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
                  have b29994 := hb (x 10 2)
                  have b29995 := hb (x 10 14)
                  clear * - r29993 b29994 b29995 d29938
                  omega
                have d29996 : (x 12 13).toNat = 1 := by
                  have r29997 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29998 := hb (x 10 2)
                  have b29999 := hb (x 12 13)
                  have b30000 := hb (x 11 1 && x 11 14)
                  clear * - r29997 b29998 b29999 b30000 d29913 d29992
                  omega
                have d30001 : (x 12 1).toNat = 1 := by
                  have r30002 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
                  have b30003 := hb (x 12 1)
                  have b30004 := hb (x 12 13)
                  clear * - r30002 b30003 b30004 d29996
                  omega
                have d30005 : (x 13 14).toNat = 0 := by
                  have r30006 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30007 := hb (x 12 1)
                  have b30008 := hb (x 13 14)
                  clear * - r30006 b30007 b30008 d30001
                  omega
                have d30009 : (x 13 1 && x 13 14).toNat = 0 := by
                  have r30010 := hand2 (x 13 1) (x 13 14)
                  have b30011 := hb (x 13 14)
                  have b30012 := hb (x 13 1 && x 13 14)
                  clear * - r30010 b30011 b30012 d30005
                  omega
                have d30013 : (x 14 13).toNat = 1 := by
                  have r30014 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30015 := hb (x 12 2)
                  have b30016 := hb (x 14 13)
                  have b30017 := hb (x 13 1 && x 13 14)
                  clear * - r30014 b30015 b30016 b30017 d30009 d29988
                  omega
                have d30018 : (x 14 1).toNat = 1 := by
                  have r30019 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
                  have b30020 := hb (x 14 1)
                  have b30021 := hb (x 14 13)
                  clear * - r30019 b30020 b30021 d30013
                  omega
                have d30022 : (x 15 14).toNat = 0 := by
                  have r30023 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30024 := hb (x 14 1)
                  have b30025 := hb (x 15 14)
                  clear * - r30023 b30024 b30025 d30018
                  omega
                have d30026 : (x 15 1 && x 15 14).toNat = 0 := by
                  have r30027 := hand2 (x 15 1) (x 15 14)
                  have b30028 := hb (x 15 14)
                  have b30029 := hb (x 15 1 && x 15 14)
                  clear * - r30027 b30028 b30029 d30022
                  omega
                have d30030 : (x 16 13).toNat = 1 := by
                  have r30031 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30032 := hb (x 14 2)
                  have b30033 := hb (x 16 13)
                  have b30034 := hb (x 15 1 && x 15 14)
                  clear * - r30031 b30032 b30033 b30034 d30026 d29984
                  omega
                have d30035 : (x 16 1).toNat = 1 := by
                  have r30036 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
                  have b30037 := hb (x 16 1)
                  have b30038 := hb (x 16 13)
                  clear * - r30036 b30037 b30038 d30030
                  omega
                have d30039 : (x 17 14).toNat = 0 := by
                  have r30040 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30041 := hb (x 16 1)
                  have b30042 := hb (x 17 14)
                  clear * - r30040 b30041 b30042 d30035
                  omega
                have d30043 : (x 17 2).toNat = 0 := by
                  have r30044 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
                  have b30045 := hb (x 17 2)
                  have b30046 := hb (x 17 14)
                  clear * - r30044 b30045 b30046 d30039
                  omega
                have d30047 : (x 15 2).toNat = 0 := by
                  have r30048 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
                  have b30049 := hb (x 15 2)
                  have b30050 := hb (x 15 14)
                  clear * - r30048 b30049 b30050 d30022
                  omega
                have d30051 : (x 15 2 && x 15 13).toNat = 0 := by
                  have r30052 := hand1 (x 15 2) (x 15 13)
                  have b30053 := hb (x 15 2)
                  have b30054 := hb (x 15 2 && x 15 13)
                  clear * - r30052 b30053 b30054 d30047
                  omega
                have d30055 : (x 13 2).toNat = 0 := by
                  have r30056 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
                  have b30057 := hb (x 13 2)
                  have b30058 := hb (x 13 14)
                  clear * - r30056 b30057 b30058 d30005
                  omega
                have d30059 : (x 15 13).toNat = 1 := by
                  have r30060 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30061 := hb (x 13 2)
                  have b30062 := hb (x 15 13)
                  have b30063 := hb (x 14 1 && x 14 14)
                  clear * - r30060 b30061 b30062 b30063 d29976 d30055
                  omega
                have d30064 : (x 15 1).toNat = 1 := by
                  have r30065 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
                  have b30066 := hb (x 15 1)
                  have b30067 := hb (x 15 13)
                  clear * - r30065 b30066 b30067 d30059
                  omega
                have d30068 : (x 16 14).toNat = 0 := by
                  have r30069 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30070 := hb (x 15 1)
                  have b30071 := hb (x 16 14)
                  clear * - r30069 b30070 b30071 d30064
                  omega
                have d30072 : (x 16 1 && x 16 14).toNat = 0 := by
                  have r30073 := hand2 (x 16 1) (x 16 14)
                  have b30074 := hb (x 16 14)
                  have b30075 := hb (x 16 1 && x 16 14)
                  clear * - r30073 b30074 b30075 d30068
                  omega
                have d30076 : (x 17 13).toNat = 1 := by
                  have r30077 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30078 := hb (x 15 2)
                  have b30079 := hb (x 17 13)
                  have b30080 := hb (x 16 1 && x 16 14)
                  clear * - r30077 b30078 b30079 b30080 d30072 d30047
                  omega
                have d30081 : (x 17 1).toNat = 1 := by
                  have r30082 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
                  have b30083 := hb (x 17 1)
                  have b30084 := hb (x 17 13)
                  clear * - r30082 b30083 b30084 d30076
                  omega
                have d30085 : (x 18 14).toNat = 0 := by
                  have r30086 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30087 := hb (x 17 1)
                  have b30088 := hb (x 18 14)
                  clear * - r30086 b30087 b30088 d30081
                  omega
                have d30089 : (x 18 1 && x 18 14).toNat = 0 := by
                  have r30090 := hand2 (x 18 1) (x 18 14)
                  have b30091 := hb (x 18 14)
                  have b30092 := hb (x 18 1 && x 18 14)
                  clear * - r30090 b30091 b30092 d30085
                  omega
                have d30093 : (x 19 13).toNat = 1 := by
                  have r30094 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30095 := hb (x 17 2)
                  have b30096 := hb (x 19 13)
                  have b30097 := hb (x 18 1 && x 18 14)
                  clear * - r30094 b30095 b30096 b30097 d30089 d30043
                  omega
                have d30098 : (x 18 2).toNat = 0 := by
                  have r30099 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
                  have b30100 := hb (x 18 2)
                  have b30101 := hb (x 18 14)
                  clear * - r30099 b30100 b30101 d30085
                  omega
                have d30102 : (x 20 12).toNat = 0 := by
                  have r30103 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30104 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                  have e30105 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                  have b30106 := hb (x 17 3)
                  have b30107 := hb (x 18 2)
                  have b30108 := hb (x 19 13)
                  have b30109 := hb (x 20 12)
                  clear * - r30103 e30104 e30105 b30106 b30107 b30108 b30109 d30093 d30098
                  omega
                have d30110 : (x 17 3).toNat = 0 := by
                  have r30111 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30112 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                  have e30113 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                  have b30114 := hb (x 17 3)
                  have b30115 := hb (x 18 2)
                  have b30116 := hb (x 19 13)
                  have b30117 := hb (x 20 12)
                  clear * - r30111 e30112 e30113 b30114 b30115 b30116 b30117 d30102 d30093 d30098
                  omega
                have d30118 : (x 17 11).toNat = 0 := by
                  have r30119 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
                  have b30120 := hb (x 17 3)
                  have b30121 := hb (x 17 11)
                  clear * - r30119 b30120 b30121 d30110
                  omega
                have d30122 : (x 16 12).toNat = 0 := by
                  have r30123 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30124 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                  have e30125 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                  have b30126 := hb (x 13 3)
                  have b30127 := hb (x 14 2)
                  have b30128 := hb (x 15 13)
                  have b30129 := hb (x 16 12)
                  clear * - r30123 e30124 e30125 b30126 b30127 b30128 b30129 d30059 d29984
                  omega
                have d30130 : (x 16 1 && x 16 12).toNat = 0 := by
                  have r30131 := hand2 (x 16 1) (x 16 12)
                  have b30132 := hb (x 16 12)
                  have b30133 := hb (x 16 1 && x 16 12)
                  clear * - r30131 b30132 b30133 d30122
                  omega
                have d30134 : (x 13 12).toNat = 0 := by
                  have r30135 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30136 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                  have e30137 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                  have b30138 := hb (x 10 3)
                  have b30139 := hb (x 11 2)
                  have b30140 := hb (x 12 13)
                  have b30141 := hb (x 13 12)
                  clear * - r30135 e30136 e30137 b30138 b30139 b30140 b30141 d29996 d29917
                  omega
                have d30142 : (x 13 4).toNat = 0 := by
                  have r30143 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
                  have b30144 := hb (x 13 4)
                  have b30145 := hb (x 13 12)
                  clear * - r30143 b30144 b30145 d30134
                  omega
                have r30146 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b30147 := hb (x 13 4)
                have b30148 := hb (x 17 11)
                have b30149 := hb (x 16 1 && x 16 12)
                have b30150 := hb (x 15 2 && x 15 13)
                have b30151 := hb (x 14 3 && x 14 14)
                linarith only [r30146, b30147, b30148, b30149, b30150, b30151, d30118, d30130, d30051, d29980, d30142]
            · have f30152 : (x (-1) 3).toNat = 1 := by rw [h28877]; rfl
              have d30153 : (x 2 12).toNat = 0 := by
                have r30154 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e30155 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                have e30156 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                have b30157 := hb (x (-1) 3)
                have b30158 := hb (x 0 2)
                have b30159 := hb (x 1 13)
                have b30160 := hb (x 2 12)
                clear * - r30154 e30155 e30156 b30157 b30158 b30159 b30160 f28797 f30152
                omega
              have d30161 : (x 2 2 && x 2 12).toNat = 0 := by
                have r30162 := hand2 (x 2 2) (x 2 12)
                have b30163 := hb (x 2 12)
                have b30164 := hb (x 2 2 && x 2 12)
                clear * - r30162 b30163 b30164 d30153
                omega
              have d30165 : (x 1 13).toNat = 0 := by
                have r30166 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e30167 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                have e30168 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                have b30169 := hb (x (-1) 3)
                have b30170 := hb (x 0 2)
                have b30171 := hb (x 1 13)
                have b30172 := hb (x 2 12)
                clear * - r30166 e30167 e30168 b30169 b30170 b30171 b30172 d30153 f28797 f30152
                omega
              have d30173 : (x 1 3 && x 1 13).toNat = 0 := by
                have r30174 := hand2 (x 1 3) (x 1 13)
                have b30175 := hb (x 1 13)
                have b30176 := hb (x 1 3 && x 1 13)
                clear * - r30174 b30175 b30176 d30165
                omega
              have r30177 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b30178 := hb (x (-1) 5)
              have b30179 := hb (x 4 10)
              have b30180 := hb (x 3 1 && x 3 11)
              have b30181 := hb (x 2 2 && x 2 12)
              have b30182 := hb (x 1 3 && x 1 13)
              have b30183 := hb (x 0 4 && x 0 14)
              linarith only [r30177, b30178, b30179, b30180, b30181, b30182, b30183, g11, g42, d30161, d30173, d27968, g0]
          · have f30184 : (x 0 9).toNat = 1 := by rw [h28871]; rfl
            have d30185 : (x 1 8).toNat = 0 := by
              have r30186 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30187 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e30188 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e30189 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e30190 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e30191 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e30192 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b30193 := hb (x (-6) 7)
              have b30194 := hb (x (-5) 6)
              have b30195 := hb (x (-4) 5)
              have b30196 := hb (x (-3) 4)
              have b30197 := hb (x (-2) 11)
              have b30198 := hb (x (-1) 10)
              have b30199 := hb (x 0 9)
              have b30200 := hb (x 1 8)
              clear * - r30186 e30187 e30188 e30189 e30190 e30191 e30192 b30193 b30194 b30195 b30196 b30197 b30198 b30199 b30200 f30184 d28867
              omega
            have d30201 : (x (-2) 11).toNat = 0 := by
              have r30202 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30203 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e30204 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e30205 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e30206 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e30207 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e30208 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b30209 := hb (x (-6) 7)
              have b30210 := hb (x (-5) 6)
              have b30211 := hb (x (-4) 5)
              have b30212 := hb (x (-3) 4)
              have b30213 := hb (x (-2) 11)
              have b30214 := hb (x (-1) 10)
              have b30215 := hb (x 0 9)
              have b30216 := hb (x 1 8)
              clear * - r30202 e30203 e30204 e30205 e30206 e30207 e30208 b30209 b30210 b30211 b30212 b30213 b30214 b30215 b30216 d30185 f30184 d28867
              omega
            have d30217 : (x (-3) 4).toNat = 0 := by
              have r30218 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30219 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e30220 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e30221 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e30222 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e30223 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e30224 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b30225 := hb (x (-6) 7)
              have b30226 := hb (x (-5) 6)
              have b30227 := hb (x (-4) 5)
              have b30228 := hb (x (-3) 4)
              have b30229 := hb (x (-2) 11)
              have b30230 := hb (x (-1) 10)
              have b30231 := hb (x 0 9)
              have b30232 := hb (x 1 8)
              clear * - r30218 e30219 e30220 e30221 e30222 e30223 e30224 b30225 b30226 b30227 b30228 b30229 b30230 b30231 b30232 d30185 f30184 d28867 d30201
              omega
            have d30233 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
              have r30234 := hand1 (x (-3) 4) (x (-3) 14)
              have b30235 := hb (x (-3) 4)
              have b30236 := hb (x (-3) 4 && x (-3) 14)
              clear * - r30234 b30235 b30236 d30217
              omega
            have d30237 : (x (-4) 5).toNat = 0 := by
              have r30238 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30239 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e30240 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e30241 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e30242 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e30243 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e30244 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b30245 := hb (x (-6) 7)
              have b30246 := hb (x (-5) 6)
              have b30247 := hb (x (-4) 5)
              have b30248 := hb (x (-3) 4)
              have b30249 := hb (x (-2) 11)
              have b30250 := hb (x (-1) 10)
              have b30251 := hb (x 0 9)
              have b30252 := hb (x 1 8)
              clear * - r30238 e30239 e30240 e30241 e30242 e30243 e30244 b30245 b30246 b30247 b30248 b30249 b30250 b30251 b30252 d30185 f30184 d28867 d30201 d30217
              omega
            have d30253 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
              have r30254 := hand1 (x (-4) 5) (x (-4) 14)
              have b30255 := hb (x (-4) 5)
              have b30256 := hb (x (-4) 5 && x (-4) 14)
              clear * - r30254 b30255 b30256 d30237
              omega
            have d30257 : (x (-2) 3 && x (-2) 13).toNat = 1 := by
              have r30258 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b30259 := hb (x (-4) 5)
              have b30260 := hb (x 1 10)
              have b30261 := hb (x 0 1 && x 0 11)
              have b30262 := hb (x (-1) 2 && x (-1) 12)
              have b30263 := hb (x (-2) 3 && x (-2) 13)
              have b30264 := hb (x (-3) 4 && x (-3) 14)
              clear * - r30258 b30259 b30260 b30261 b30262 b30263 b30264 d28792 g41 d28859 d30233 d30237
              omega
            have d30265 : (x (-2) 13).toNat = 1 := by
              have r30266 := hand2 (x (-2) 3) (x (-2) 13)
              have b30267 := hb (x (-2) 13)
              have b30268 := hb (x (-2) 3 && x (-2) 13)
              clear * - r30266 b30267 b30268 d30257
              omega
            have d30269 : (x (-2) 1).toNat = 1 := by
              have r30270 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
              have b30271 := hb (x (-2) 1)
              have b30272 := hb (x (-2) 13)
              clear * - r30270 b30271 b30272 d30265
              omega
            have d30273 : (x (-1) 14).toNat = 0 := by
              have r30274 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b30275 := hb (x (-2) 1)
              have b30276 := hb (x (-1) 14)
              clear * - r30274 b30275 b30276 d30269
              omega
            have d30277 : (x (-1) 6).toNat = 0 := by
              have r30278 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
              have b30279 := hb (x (-1) 6)
              have b30280 := hb (x (-1) 14)
              clear * - r30278 b30279 b30280 d30273
              omega
            have d30281 : (x (-1) 12).toNat = 0 := by
              have r30282 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30283 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e30284 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b30285 := hb (x (-4) 3)
              have b30286 := hb (x (-3) 2)
              have b30287 := hb (x (-2) 13)
              have b30288 := hb (x (-1) 12)
              clear * - r30282 e30283 e30284 b30285 b30286 b30287 b30288 d30265
              omega
            have d30289 : (x (-1) 4).toNat = 0 := by
              have r30290 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
              have b30291 := hb (x (-1) 4)
              have b30292 := hb (x (-1) 12)
              clear * - r30290 b30291 b30292 d30281
              omega
            have d30293 : (x 2 1 && x 2 12).toNat = 1 := by
              have r30294 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b30295 := hb (x (-1) 4)
              have b30296 := hb (x 3 11)
              have b30297 := hb (x 2 1 && x 2 12)
              have b30298 := hb (x 1 2 && x 1 13)
              have b30299 := hb (x 0 3 && x 0 14)
              clear * - r30294 b30295 b30296 b30297 b30298 b30299 g10 d28780 g46 d30289
              omega
            have d30300 : (x 2 12).toNat = 1 := by
              have r30301 := hand2 (x 2 1) (x 2 12)
              have b30302 := hb (x 2 12)
              have b30303 := hb (x 2 1 && x 2 12)
              clear * - r30301 b30302 b30303 d30293
              omega
            have d30304 : (x 1 13).toNat = 0 := by
              have r30305 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30306 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
              have e30307 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
              have b30308 := hb (x (-1) 3)
              have b30309 := hb (x 0 2)
              have b30310 := hb (x 1 13)
              have b30311 := hb (x 2 12)
              clear * - r30305 e30306 e30307 b30308 b30309 b30310 b30311 d30300 f28797
              omega
            have d30312 : (x 1 3 && x 1 13).toNat = 0 := by
              have r30313 := hand2 (x 1 3) (x 1 13)
              have b30314 := hb (x 1 13)
              have b30315 := hb (x 1 3 && x 1 13)
              clear * - r30313 b30314 b30315 d30304
              omega
            have d30316 : (x 2 2 && x 2 12).toNat = 1 := by
              have r30317 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b30318 := hb (x (-1) 5)
              have b30319 := hb (x 4 10)
              have b30320 := hb (x 3 1 && x 3 11)
              have b30321 := hb (x 2 2 && x 2 12)
              have b30322 := hb (x 1 3 && x 1 13)
              have b30323 := hb (x 0 4 && x 0 14)
              clear * - r30317 b30318 b30319 b30320 b30321 b30322 b30323 g11 g42 d30312 d27968 g0
              omega
            have d30324 : (x 2 2).toNat = 1 := by
              have r30325 := hand1 (x 2 2) (x 2 12)
              have b30326 := hb (x 2 2)
              have b30327 := hb (x 2 2 && x 2 12)
              clear * - r30325 b30326 b30327 d30316
              omega
            have d30328 : (x 2 14).toNat = 1 := by
              have r30329 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
              have b30330 := hb (x 2 2)
              have b30331 := hb (x 2 14)
              clear * - r30329 b30330 b30331 d30324
              omega
            have d30332 : (x 1 1).toNat = 0 := by
              have r30333 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b30334 := hb (x 1 1)
              have b30335 := hb (x 2 14)
              clear * - r30333 b30334 b30335 d30328
              omega
            have d30336 : (x 1 9).toNat = 0 := by
              have r30337 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
              have b30338 := hb (x 1 1)
              have b30339 := hb (x 1 9)
              clear * - r30337 b30338 b30339 d30332
              omega
            have d30340 : (x 1 9 && x 1 13).toNat = 0 := by
              have r30341 := hand1 (x 1 9) (x 1 13)
              have b30342 := hb (x 1 9)
              have b30343 := hb (x 1 9 && x 1 13)
              clear * - r30341 b30342 b30343 d30336
              omega
            have d30344 : (x 4 12).toNat = 0 := by
              have r30345 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30346 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e30347 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b30348 := hb (x 1 3)
              have b30349 := hb (x 2 2)
              have b30350 := hb (x 3 13)
              have b30351 := hb (x 4 12)
              clear * - r30345 e30346 e30347 b30348 b30349 b30350 b30351 d30324
              omega
            have d30352 : (x 4 2 && x 4 12).toNat = 0 := by
              have r30353 := hand2 (x 4 2) (x 4 12)
              have b30354 := hb (x 4 12)
              have b30355 := hb (x 4 2 && x 4 12)
              clear * - r30353 b30354 b30355 d30344
              omega
            have d30356 : (x 4 4).toNat = 0 := by
              have r30357 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
              have b30358 := hb (x 4 4)
              have b30359 := hb (x 4 12)
              clear * - r30357 b30358 b30359 d30344
              omega
            have d30360 : (x 3 13).toNat = 0 := by
              have r30361 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30362 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e30363 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b30364 := hb (x 1 3)
              have b30365 := hb (x 2 2)
              have b30366 := hb (x 3 13)
              have b30367 := hb (x 4 12)
              clear * - r30361 e30362 e30363 b30364 b30365 b30366 b30367 d30344 d30324
              omega
            have d30368 : (x 3 3 && x 3 13).toNat = 0 := by
              have r30369 := hand2 (x 3 3) (x 3 13)
              have b30370 := hb (x 3 13)
              have b30371 := hb (x 3 3 && x 3 13)
              clear * - r30369 b30370 b30371 d30360
              omega
            have d30372 : (x 3 5).toNat = 0 := by
              have r30373 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
              have b30374 := hb (x 3 5)
              have b30375 := hb (x 3 13)
              clear * - r30373 b30374 b30375 d30360
              omega
            have d30376 : (x 1 3).toNat = 0 := by
              have r30377 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30378 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e30379 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b30380 := hb (x 1 3)
              have b30381 := hb (x 2 2)
              have b30382 := hb (x 3 13)
              have b30383 := hb (x 4 12)
              clear * - r30377 e30378 e30379 b30380 b30381 b30382 b30383 d30344 d30360 d30324
              omega
            have d30384 : (x 1 11).toNat = 0 := by
              have r30385 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
              have b30386 := hb (x 1 3)
              have b30387 := hb (x 1 11)
              clear * - r30385 b30386 b30387 d30376
              omega
            have d30388 : (x (-2) 3 && x (-2) 14).toNat = 1 := by
              have r30389 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b30390 := hb (x (-3) 4)
              have b30391 := hb (x 1 11)
              have b30392 := hb (x 0 1 && x 0 12)
              have b30393 := hb (x (-1) 2 && x (-1) 13)
              have b30394 := hb (x (-2) 3 && x (-2) 14)
              clear * - r30389 b30390 b30391 b30392 b30393 b30394 d30384 d27960 g45 d30217
              omega
            have d30395 : (x (-2) 3).toNat = 1 := by
              have r30396 := hand1 (x (-2) 3) (x (-2) 14)
              have b30397 := hb (x (-2) 3)
              have b30398 := hb (x (-2) 3 && x (-2) 14)
              clear * - r30396 b30397 b30398 d30388
              omega
            have d30399 : (x 1 12).toNat = 0 := by
              have r30400 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30401 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
              have e30402 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
              have b30403 := hb (x (-2) 3)
              have b30404 := hb (x (-1) 2)
              have b30405 := hb (x 0 13)
              have b30406 := hb (x 1 12)
              clear * - r30400 e30401 e30402 b30403 b30404 b30405 b30406 g6 f28858 d30395
              omega
            have d30407 : (x 1 4).toNat = 0 := by
              have r30408 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
              have b30409 := hb (x 1 4)
              have b30410 := hb (x 1 12)
              clear * - r30408 b30409 b30410 d30399
              omega
            have d30411 : (x 1 4 && x 1 13).toNat = 0 := by
              have r30412 := hand1 (x 1 4) (x 1 13)
              have b30413 := hb (x 1 4)
              have b30414 := hb (x 1 4 && x 1 13)
              clear * - r30412 b30413 b30414 d30407
              omega
            have d30415 : (x 2 3 && x 2 12).toNat = 1 := by
              have r30416 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b30417 := hb (x (-1) 6)
              have b30418 := hb (x 5 9)
              have b30419 := hb (x 4 1 && x 4 10)
              have b30420 := hb (x 3 2 && x 3 11)
              have b30421 := hb (x 2 3 && x 2 12)
              have b30422 := hb (x 1 4 && x 1 13)
              have b30423 := hb (x 0 5 && x 0 14)
              clear * - r30416 b30417 b30418 b30419 b30420 b30421 b30422 b30423 g12 g39 g40 d30411 d27903 d30277
              omega
            have d30424 : (x 2 3).toNat = 1 := by
              have r30425 := hand1 (x 2 3) (x 2 12)
              have b30426 := hb (x 2 3)
              have b30427 := hb (x 2 3 && x 2 12)
              clear * - r30425 b30426 b30427 d30415
              omega
            have d30428 : (x 5 12).toNat = 0 := by
              have r30429 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30430 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e30431 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b30432 := hb (x 2 3)
              have b30433 := hb (x 3 2)
              have b30434 := hb (x 4 13)
              have b30435 := hb (x 5 12)
              clear * - r30429 e30430 e30431 b30432 b30433 b30434 b30435 d28843 d30424
              omega
            have d30436 : (x 5 1 && x 5 12).toNat = 0 := by
              have r30437 := hand2 (x 5 1) (x 5 12)
              have b30438 := hb (x 5 12)
              have b30439 := hb (x 5 1 && x 5 12)
              clear * - r30437 b30438 b30439 d30428
              omega
            have d30440 : (x 5 4).toNat = 0 := by
              have r30441 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
              have b30442 := hb (x 5 4)
              have b30443 := hb (x 5 12)
              clear * - r30441 b30442 b30443 d30428
              omega
            have d30444 : (x 4 13).toNat = 0 := by
              have r30445 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30446 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e30447 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b30448 := hb (x 2 3)
              have b30449 := hb (x 3 2)
              have b30450 := hb (x 4 13)
              have b30451 := hb (x 5 12)
              clear * - r30445 e30446 e30447 b30448 b30449 b30450 b30451 d30428 d28843 d30424
              omega
            have d30452 : (x 4 2 && x 4 13).toNat = 0 := by
              have r30453 := hand2 (x 4 2) (x 4 13)
              have b30454 := hb (x 4 13)
              have b30455 := hb (x 4 2 && x 4 13)
              clear * - r30453 b30454 b30455 d30444
              omega
            have d30456 : (x 6 11).toNat = 1 := by
              have r30457 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b30458 := hb (x 2 4)
              have b30459 := hb (x 6 11)
              have b30460 := hb (x 5 1 && x 5 12)
              have b30461 := hb (x 4 2 && x 4 13)
              have b30462 := hb (x 3 3 && x 3 14)
              clear * - r30457 b30458 b30459 b30460 b30461 b30462 d30436 d30452 d28827 g9
              omega
            have d30463 : (x 6 3).toNat = 1 := by
              have r30464 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
              have b30465 := hb (x 6 3)
              have b30466 := hb (x 6 11)
              clear * - r30464 b30465 b30466 d30456
              omega
            have d30467 : (x 9 12).toNat = 0 := by
              have r30468 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30469 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e30470 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b30471 := hb (x 6 3)
              have b30472 := hb (x 7 2)
              have b30473 := hb (x 8 13)
              have b30474 := hb (x 9 12)
              clear * - r30468 e30469 e30470 b30471 b30472 b30473 b30474 d30463
              omega
            have d30475 : (x 8 13).toNat = 0 := by
              have r30476 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30477 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e30478 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b30479 := hb (x 6 3)
              have b30480 := hb (x 7 2)
              have b30481 := hb (x 8 13)
              have b30482 := hb (x 9 12)
              clear * - r30476 e30477 e30478 b30479 b30480 b30481 b30482 d30467 d30463
              omega
            have d30483 : (x 7 2).toNat = 0 := by
              have r30484 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30485 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e30486 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b30487 := hb (x 6 3)
              have b30488 := hb (x 7 2)
              have b30489 := hb (x 8 13)
              have b30490 := hb (x 9 12)
              clear * - r30484 e30485 e30486 b30487 b30488 b30489 b30490 d30467 d30475 d30463
              omega
            have d30491 : (x 7 10).toNat = 0 := by
              have r30492 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
              have b30493 := hb (x 7 2)
              have b30494 := hb (x 7 10)
              clear * - r30492 b30493 b30494 d30483
              omega
            have d30495 : (x 9 8).toNat = 0 := by
              have r30496 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30497 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e30498 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e30499 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e30500 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e30501 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e30502 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b30503 := hb (x 2 7)
              have b30504 := hb (x 3 6)
              have b30505 := hb (x 4 5)
              have b30506 := hb (x 5 4)
              have b30507 := hb (x 6 11)
              have b30508 := hb (x 7 10)
              have b30509 := hb (x 8 9)
              have b30510 := hb (x 9 8)
              clear * - r30496 e30497 e30498 e30499 e30500 e30501 e30502 b30503 b30504 b30505 b30506 b30507 b30508 b30509 b30510 d30491 d30456 d30440 d28835
              omega
            have d30511 : (x 8 9).toNat = 0 := by
              have r30512 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30513 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e30514 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e30515 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e30516 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e30517 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e30518 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b30519 := hb (x 2 7)
              have b30520 := hb (x 3 6)
              have b30521 := hb (x 4 5)
              have b30522 := hb (x 5 4)
              have b30523 := hb (x 6 11)
              have b30524 := hb (x 7 10)
              have b30525 := hb (x 8 9)
              have b30526 := hb (x 9 8)
              clear * - r30512 e30513 e30514 e30515 e30516 e30517 e30518 b30519 b30520 b30521 b30522 b30523 b30524 b30525 b30526 d30495 d30491 d30456 d30440 d28835
              omega
            have d30527 : (x 4 5).toNat = 0 := by
              have r30528 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30529 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e30530 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e30531 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e30532 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e30533 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e30534 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b30535 := hb (x 2 7)
              have b30536 := hb (x 3 6)
              have b30537 := hb (x 4 5)
              have b30538 := hb (x 5 4)
              have b30539 := hb (x 6 11)
              have b30540 := hb (x 7 10)
              have b30541 := hb (x 8 9)
              have b30542 := hb (x 9 8)
              clear * - r30528 e30529 e30530 e30531 e30532 e30533 e30534 b30535 b30536 b30537 b30538 b30539 b30540 b30541 b30542 d30495 d30511 d30491 d30456 d30440 d28835
              omega
            have d30543 : (x 2 7).toNat = 0 := by
              have r30544 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30545 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e30546 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e30547 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e30548 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e30549 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e30550 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b30551 := hb (x 2 7)
              have b30552 := hb (x 3 6)
              have b30553 := hb (x 4 5)
              have b30554 := hb (x 5 4)
              have b30555 := hb (x 6 11)
              have b30556 := hb (x 7 10)
              have b30557 := hb (x 8 9)
              have b30558 := hb (x 9 8)
              clear * - r30544 e30545 e30546 e30547 e30548 e30549 e30550 b30551 b30552 b30553 b30554 b30555 b30556 b30557 b30558 d30495 d30511 d30491 d30456 d30440 d30527 d28835
              omega
            have d30559 : (x 1 7 && x 1 13).toNat = 0 := by
              have r30560 := hand2 (x 1 7) (x 1 13)
              have b30561 := hb (x 1 13)
              have b30562 := hb (x 1 7 && x 1 13)
              clear * - r30560 b30561 b30562 d30304
              omega
            have d30563 : (x (-1) 3).toNat = 0 := by
              have r30564 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30565 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
              have e30566 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
              have b30567 := hb (x (-1) 3)
              have b30568 := hb (x 0 2)
              have b30569 := hb (x 1 13)
              have b30570 := hb (x 2 12)
              clear * - r30564 e30565 e30566 b30567 b30568 b30569 b30570 d30300 d30304 f28797
              omega
            have d30571 : (x (-1) 11).toNat = 0 := by
              have r30572 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
              have b30573 := hb (x (-1) 3)
              have b30574 := hb (x (-1) 11)
              clear * - r30572 b30573 b30574 d30563
              omega
            have d30575 : (x (-5) 6).toNat = 0 := by
              have r30576 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30577 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e30578 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e30579 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e30580 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e30581 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e30582 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b30583 := hb (x (-6) 7)
              have b30584 := hb (x (-5) 6)
              have b30585 := hb (x (-4) 5)
              have b30586 := hb (x (-3) 4)
              have b30587 := hb (x (-2) 11)
              have b30588 := hb (x (-1) 10)
              have b30589 := hb (x 0 9)
              have b30590 := hb (x 1 8)
              clear * - r30576 e30577 e30578 e30579 e30580 e30581 e30582 b30583 b30584 b30585 b30586 b30587 b30588 b30589 b30590 d30185 f30184 d28867 d30201 d30217 d30237
              omega
            have d30591 : (x (-2) 3 && x (-2) 12).toNat = 1 := by
              have r30592 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b30593 := hb (x (-5) 6)
              have b30594 := hb (x 1 9)
              have b30595 := hb (x 0 1 && x 0 10)
              have b30596 := hb (x (-1) 2 && x (-1) 11)
              have b30597 := hb (x (-2) 3 && x (-2) 12)
              have b30598 := hb (x (-3) 4 && x (-3) 13)
              have b30599 := hb (x (-4) 5 && x (-4) 14)
              clear * - r30592 b30593 b30594 b30595 b30596 b30597 b30598 b30599 d30336 d28802 d28863 d27940 d30253 d30575
              omega
            have d30600 : (x (-2) 12).toNat = 1 := by
              have r30601 := hand2 (x (-2) 3) (x (-2) 12)
              have b30602 := hb (x (-2) 12)
              have b30603 := hb (x (-2) 3 && x (-2) 12)
              clear * - r30601 b30602 b30603 d30591
              omega
            have d30604 : (x (-4) 2).toNat = 0 := by
              have r30605 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30606 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e30607 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b30608 := hb (x (-5) 3)
              have b30609 := hb (x (-4) 2)
              have b30610 := hb (x (-3) 13)
              have b30611 := hb (x (-2) 12)
              clear * - r30605 e30606 e30607 b30608 b30609 b30610 b30611 d30600 d27932
              omega
            have d30612 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
              have r30613 := hand1 (x (-4) 2) (x (-4) 13)
              have b30614 := hb (x (-4) 2)
              have b30615 := hb (x (-4) 2 && x (-4) 13)
              clear * - r30613 b30614 b30615 d30604
              omega
            have d30616 : (x (-4) 10).toNat = 0 := by
              have r30617 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
              have b30618 := hb (x (-4) 2)
              have b30619 := hb (x (-4) 10)
              clear * - r30617 b30618 b30619 d30604
              omega
            have d30620 : (x (-5) 3).toNat = 0 := by
              have r30621 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30622 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e30623 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b30624 := hb (x (-5) 3)
              have b30625 := hb (x (-4) 2)
              have b30626 := hb (x (-3) 13)
              have b30627 := hb (x (-2) 12)
              clear * - r30621 e30622 e30623 b30624 b30625 b30626 b30627 d30600 d27932 d30604
              omega
            have d30628 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
              have r30629 := hand1 (x (-5) 3) (x (-5) 14)
              have b30630 := hb (x (-5) 3)
              have b30631 := hb (x (-5) 3 && x (-5) 14)
              clear * - r30629 b30630 b30631 d30620
              omega
            have d30632 : (x (-6) 4).toNat = 1 := by
              have r30633 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b30634 := hb (x (-6) 4)
              have b30635 := hb (x (-2) 11)
              have b30636 := hb (x (-3) 1 && x (-3) 12)
              have b30637 := hb (x (-4) 2 && x (-4) 13)
              have b30638 := hb (x (-5) 3 && x (-5) 14)
              clear * - r30633 b30634 b30635 b30636 b30637 b30638 d30201 d27928 d30612 d30628
              omega
            have d30639 : (x (-6) 12).toNat = 1 := by
              have r30640 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
              have b30641 := hb (x (-6) 4)
              have b30642 := hb (x (-6) 12)
              clear * - r30640 b30641 b30642 d30632
              omega
            have d30643 : (x (-7) 13).toNat = 0 := by
              have r30644 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30645 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
              have e30646 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
              have b30647 := hb (x (-9) 3)
              have b30648 := hb (x (-8) 2)
              have b30649 := hb (x (-7) 13)
              have b30650 := hb (x (-6) 12)
              clear * - r30644 e30645 e30646 b30647 b30648 b30649 b30650 d30639
              omega
            have d30651 : (x (-7) 5).toNat = 0 := by
              have r30652 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
              have b30653 := hb (x (-7) 5)
              have b30654 := hb (x (-7) 13)
              clear * - r30652 b30653 b30654 d30643
              omega
            have d30655 : (x (-5) 11).toNat = 0 := by
              have r30656 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
              have b30657 := hb (x (-5) 3)
              have b30658 := hb (x (-5) 11)
              clear * - r30656 b30657 b30658 d30620
              omega
            have d30659 : (x (-2) 8).toNat = 0 := by
              have r30660 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30661 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e30662 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e30663 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e30664 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e30665 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e30666 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have b30667 := hb (x (-9) 7)
              have b30668 := hb (x (-8) 6)
              have b30669 := hb (x (-7) 5)
              have b30670 := hb (x (-6) 4)
              have b30671 := hb (x (-5) 11)
              have b30672 := hb (x (-4) 10)
              have b30673 := hb (x (-3) 9)
              have b30674 := hb (x (-2) 8)
              clear * - r30660 e30661 e30662 e30663 e30664 e30665 e30666 b30667 b30668 b30669 b30670 b30671 b30672 b30673 b30674 d27948 d30616 d30655 d30632 d30651
              omega
            have d30675 : (x (-2) 8 && x (-2) 12).toNat = 0 := by
              have r30676 := hand1 (x (-2) 8) (x (-2) 12)
              have b30677 := hb (x (-2) 8)
              have b30678 := hb (x (-2) 8 && x (-2) 12)
              clear * - r30676 b30677 b30678 d30659
              omega
            have r30679 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r30680 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r30681 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30682 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e30683 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e30684 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e30685 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e30686 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e30687 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have r30688 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30689 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e30690 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e30691 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e30692 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e30693 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e30694 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have r30695 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30696 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
            have e30697 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
            have r30698 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30699 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
            have e30700 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
            have r30701 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r30702 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r30703 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r30704 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r30705 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
            have r30706 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
            have r30707 := hand2 (x 4 2) (x 4 6)
            have r30708 := hand2 (x 3 3) (x 3 7)
            have r30709 := hand1 (x 8 2) (x 8 6)
            have r30710 := hand1 (x 7 3) (x 7 7)
            have r30711 := hand1 (x 2 8) (x 2 12)
            have r30712 := hand2 (x 7 1) (x 7 7)
            have r30713 := hand1 (x 2 6) (x 2 12)
            have r30714 := hand2 (x 5 1) (x 5 11)
            have r30715 := hand2 (x (-4) 1) (x (-4) 14)
            have r30716 := hand1 (x 8 1) (x 8 14)
            linarith only [r30679, r30680, r30681, e30682, e30683, e30684, e30685, e30686, e30687, r30688, e30689, e30690, e30691, e30692, e30693, e30694, r30695, e30696, e30697, r30698, e30699, e30700, r30701, r30702, r30703, r30704, r30705, r30706, r30707, r30708, r30709, r30710, r30711, r30712, r30713, r30714, r30715, r30716, d30655, d30616, d27932, d30201, d30600, g1, d28867, d30571, f30184, d28798, g8, d30185, d30336, d30543, d30372, d28835, d30356, d30527, d30440, d30463, d30483, g18, g19, d28806, g20, d30675, d27944, g21, g22, g23, g24, d30340, g31, g32, g33, g34, d30559, d28853, d30352, d30368, g43]
        · have f30797 : (x (-1) 2).toNat = 1 := by rw [h28857]; rfl
          have d30798 : (x (-1) 14).toNat = 1 := by
            have r30799 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
            have b30800 := hb (x (-1) 2)
            have b30801 := hb (x (-1) 14)
            clear * - r30799 b30800 b30801 f30797
            omega
          have d30802 : (x (-2) 1).toNat = 0 := by
            have r30803 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b30804 := hb (x (-2) 1)
            have b30805 := hb (x (-1) 14)
            clear * - r30803 b30804 b30805 d30798
            omega
          have d30806 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
            have r30807 := hand1 (x (-2) 1) (x (-2) 14)
            have b30808 := hb (x (-2) 1)
            have b30809 := hb (x (-2) 1 && x (-2) 14)
            clear * - r30807 b30808 b30809 d30802
            omega
          have d30810 : (x (-2) 13).toNat = 0 := by
            have r30811 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
            have b30812 := hb (x (-2) 1)
            have b30813 := hb (x (-2) 13)
            clear * - r30811 b30812 b30813 d30802
            omega
          have d30814 : (x (-3) 2).toNat = 1 := by
            have r30815 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b30816 := hb (x (-3) 2)
            have b30817 := hb (x (-1) 13)
            have b30818 := hb (x (-2) 1 && x (-2) 14)
            clear * - r30815 b30816 b30817 b30818 g2 d30806
            omega
          have d30819 : (x (-3) 14).toNat = 1 := by
            have r30820 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
            have b30821 := hb (x (-3) 2)
            have b30822 := hb (x (-3) 14)
            clear * - r30820 b30821 b30822 d30814
            omega
          have d30823 : (x (-4) 1).toNat = 0 := by
            have r30824 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b30825 := hb (x (-4) 1)
            have b30826 := hb (x (-3) 14)
            clear * - r30824 b30825 b30826 d30819
            omega
          have d30827 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
            have r30828 := hand1 (x (-4) 1) (x (-4) 14)
            have b30829 := hb (x (-4) 1)
            have b30830 := hb (x (-4) 1 && x (-4) 14)
            clear * - r30828 b30829 b30830 d30823
            omega
          have d30831 : (x (-4) 13).toNat = 0 := by
            have r30832 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
            have b30833 := hb (x (-4) 1)
            have b30834 := hb (x (-4) 13)
            clear * - r30832 b30833 b30834 d30823
            omega
          have d30835 : (x (-4) 2).toNat = 1 := by
            have r30836 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b30837 := hb (x (-4) 2)
            have b30838 := hb (x (-2) 13)
            have b30839 := hb (x (-3) 1 && x (-3) 14)
            clear * - r30836 b30837 b30838 b30839 d30810 d27924
            omega
          have d30840 : (x (-5) 2).toNat = 1 := by
            have r30841 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b30842 := hb (x (-5) 2)
            have b30843 := hb (x (-3) 13)
            have b30844 := hb (x (-4) 1 && x (-4) 14)
            clear * - r30841 b30842 b30843 b30844 d27932 d30827
            omega
          have d30845 : (x 1 12).toNat = 0 := by
            have r30846 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30847 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e30848 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b30849 := hb (x (-2) 3)
            have b30850 := hb (x (-1) 2)
            have b30851 := hb (x 0 13)
            have b30852 := hb (x 1 12)
            clear * - r30846 e30847 e30848 b30849 b30850 b30851 b30852 g6 f30797
            omega
          have d30853 : (x 1 1 && x 1 12).toNat = 0 := by
            have r30854 := hand2 (x 1 1) (x 1 12)
            have b30855 := hb (x 1 12)
            have b30856 := hb (x 1 1 && x 1 12)
            clear * - r30854 b30855 b30856 d30845
            omega
          have d30857 : (x (-2) 3).toNat = 0 := by
            have r30858 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30859 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e30860 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b30861 := hb (x (-2) 3)
            have b30862 := hb (x (-1) 2)
            have b30863 := hb (x 0 13)
            have b30864 := hb (x 1 12)
            clear * - r30858 e30859 e30860 b30861 b30862 b30863 b30864 d30845 g6 f30797
            omega
          have d30865 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
            have r30866 := hand1 (x (-2) 3) (x (-2) 14)
            have b30867 := hb (x (-2) 3)
            have b30868 := hb (x (-2) 3 && x (-2) 14)
            clear * - r30866 b30867 b30868 d30857
            omega
          have d30869 : (x (-1) 12).toNat = 0 := by
            have r30870 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30871 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e30872 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b30873 := hb (x (-4) 3)
            have b30874 := hb (x (-3) 2)
            have b30875 := hb (x (-2) 13)
            have b30876 := hb (x (-1) 12)
            clear * - r30870 e30871 e30872 b30873 b30874 b30875 b30876 d30810 d30814
            omega
          have d30877 : (x (-1) 4).toNat = 0 := by
            have r30878 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
            have b30879 := hb (x (-1) 4)
            have b30880 := hb (x (-1) 12)
            clear * - r30878 b30879 b30880 d30869
            omega
          have d30881 : (x (-2) 12).toNat = 0 := by
            have r30882 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30883 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e30884 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b30885 := hb (x (-5) 3)
            have b30886 := hb (x (-4) 2)
            have b30887 := hb (x (-3) 13)
            have b30888 := hb (x (-2) 12)
            clear * - r30882 e30883 e30884 b30885 b30886 b30887 b30888 d27932 d30835
            omega
          have d30889 : (x (-2) 4).toNat = 0 := by
            have r30890 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
            have b30891 := hb (x (-2) 4)
            have b30892 := hb (x (-2) 12)
            clear * - r30890 b30891 b30892 d30881
            omega
          have d30893 : (x (-3) 12).toNat = 0 := by
            have r30894 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30895 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e30896 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b30897 := hb (x (-6) 3)
            have b30898 := hb (x (-5) 2)
            have b30899 := hb (x (-4) 13)
            have b30900 := hb (x (-3) 12)
            clear * - r30894 e30895 e30896 b30897 b30898 b30899 b30900 d30831 d30840
            omega
          have d30901 : (x (-3) 4).toNat = 0 := by
            have r30902 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
            have b30903 := hb (x (-3) 4)
            have b30904 := hb (x (-3) 12)
            clear * - r30902 b30903 b30904 d30893
            omega
          have d30905 : (x 2 1 && x 2 12).toNat = 1 := by
            have r30906 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b30907 := hb (x (-1) 4)
            have b30908 := hb (x 3 11)
            have b30909 := hb (x 2 1 && x 2 12)
            have b30910 := hb (x 1 2 && x 1 13)
            have b30911 := hb (x 0 3 && x 0 14)
            clear * - r30906 b30907 b30908 b30909 b30910 b30911 g10 d28780 g46 d30877
            omega
          have d30912 : (x 2 12).toNat = 1 := by
            have r30913 := hand2 (x 2 1) (x 2 12)
            have b30914 := hb (x 2 12)
            have b30915 := hb (x 2 1 && x 2 12)
            clear * - r30913 b30914 b30915 d30905
            omega
          have d30916 : (x 1 13).toNat = 0 := by
            have r30917 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30918 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
            have e30919 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
            have b30920 := hb (x (-1) 3)
            have b30921 := hb (x 0 2)
            have b30922 := hb (x 1 13)
            have b30923 := hb (x 2 12)
            clear * - r30917 e30918 e30919 b30920 b30921 b30922 b30923 d30912 f28797
            omega
          have d30924 : (x (-1) 3).toNat = 0 := by
            have r30925 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30926 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
            have e30927 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
            have b30928 := hb (x (-1) 3)
            have b30929 := hb (x 0 2)
            have b30930 := hb (x 1 13)
            have b30931 := hb (x 2 12)
            clear * - r30925 e30926 e30927 b30928 b30929 b30930 b30931 d30912 d30916 f28797
            omega
          have d30932 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
            have r30933 := hand1 (x (-1) 3) (x (-1) 14)
            have b30934 := hb (x (-1) 3)
            have b30935 := hb (x (-1) 3 && x (-1) 14)
            clear * - r30933 b30934 b30935 d30924
            omega
          have d30936 : (x 2 11).toNat = 1 := by
            have r30937 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b30938 := hb (x (-2) 4)
            have b30939 := hb (x 2 11)
            have b30940 := hb (x 1 1 && x 1 12)
            have b30941 := hb (x 0 2 && x 0 13)
            have b30942 := hb (x (-1) 3 && x (-1) 14)
            clear * - r30937 b30938 b30939 b30940 b30941 b30942 d30853 d27891 d30932 d30889
            omega
          have d30943 : (x 2 3).toNat = 1 := by
            have r30944 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
            have b30945 := hb (x 2 3)
            have b30946 := hb (x 2 11)
            clear * - r30944 b30945 b30946 d30936
            omega
          have d30947 : (x 5 12).toNat = 0 := by
            have r30948 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30949 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e30950 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b30951 := hb (x 2 3)
            have b30952 := hb (x 3 2)
            have b30953 := hb (x 4 13)
            have b30954 := hb (x 5 12)
            clear * - r30948 e30949 e30950 b30951 b30952 b30953 b30954 d28843 d30943
            omega
          have d30955 : (x 4 13).toNat = 0 := by
            have r30956 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30957 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e30958 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b30959 := hb (x 2 3)
            have b30960 := hb (x 3 2)
            have b30961 := hb (x 4 13)
            have b30962 := hb (x 5 12)
            clear * - r30956 e30957 e30958 b30959 b30960 b30961 b30962 d30947 d28843 d30943
            omega
          have d30963 : (x 2 2).toNat = 1 := by
            have r30964 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b30965 := hb (x 2 2)
            have b30966 := hb (x 4 13)
            have b30967 := hb (x 3 1 && x 3 14)
            clear * - r30964 b30965 b30966 b30967 d30955 d28823
            omega
          have d30968 : (x 4 12).toNat = 0 := by
            have r30969 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30970 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e30971 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b30972 := hb (x 1 3)
            have b30973 := hb (x 2 2)
            have b30974 := hb (x 3 13)
            have b30975 := hb (x 4 12)
            clear * - r30969 e30970 e30971 b30972 b30973 b30974 b30975 d30963
            omega
          have d30976 : (x 3 13).toNat = 0 := by
            have r30977 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30978 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e30979 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b30980 := hb (x 1 3)
            have b30981 := hb (x 2 2)
            have b30982 := hb (x 3 13)
            have b30983 := hb (x 4 12)
            clear * - r30977 e30978 e30979 b30980 b30981 b30982 b30983 d30968 d30963
            omega
          have d30984 : (x 1 3).toNat = 0 := by
            have r30985 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30986 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e30987 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b30988 := hb (x 1 3)
            have b30989 := hb (x 2 2)
            have b30990 := hb (x 3 13)
            have b30991 := hb (x 4 12)
            clear * - r30985 e30986 e30987 b30988 b30989 b30990 b30991 d30968 d30976 d30963
            omega
          have d30992 : (x 1 11).toNat = 0 := by
            have r30993 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
            have b30994 := hb (x 1 3)
            have b30995 := hb (x 1 11)
            clear * - r30993 b30994 b30995 d30984
            omega
          have r30996 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b30997 := hb (x (-3) 4)
          have b30998 := hb (x 1 11)
          have b30999 := hb (x 0 1 && x 0 12)
          have b31000 := hb (x (-1) 2 && x (-1) 13)
          have b31001 := hb (x (-2) 3 && x (-2) 14)
          linarith only [r30996, b30997, b30998, b30999, b31000, b31001, d30992, d27960, g45, d30865, d30901]
      · have f31002 : (x 0 8).toNat = 1 := by rw [h28851]; rfl
        have d31003 : (x (-2) 10).toNat = 0 := by
          have r31004 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31005 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e31006 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e31007 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e31008 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e31009 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e31010 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b31011 := hb (x (-7) 7)
          have b31012 := hb (x (-6) 6)
          have b31013 := hb (x (-5) 5)
          have b31014 := hb (x (-4) 4)
          have b31015 := hb (x (-3) 11)
          have b31016 := hb (x (-2) 10)
          have b31017 := hb (x (-1) 9)
          have b31018 := hb (x 0 8)
          clear * - r31004 e31005 e31006 e31007 e31008 e31009 e31010 b31011 b31012 b31013 b31014 b31015 b31016 b31017 b31018 f31002 g1 d27996
          omega
        have d31019 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
          have r31020 := hand2 (x (-2) 1) (x (-2) 10)
          have b31021 := hb (x (-2) 10)
          have b31022 := hb (x (-2) 1 && x (-2) 10)
          clear * - r31020 b31021 b31022 d31003
          omega
        have d31023 : (x (-2) 5 && x (-2) 10).toNat = 0 := by
          have r31024 := hand2 (x (-2) 5) (x (-2) 10)
          have b31025 := hb (x (-2) 10)
          have b31026 := hb (x (-2) 5 && x (-2) 10)
          clear * - r31024 b31025 b31026 d31003
          omega
        have d31027 : (x (-4) 4).toNat = 0 := by
          have r31028 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31029 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e31030 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e31031 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e31032 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e31033 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e31034 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b31035 := hb (x (-7) 7)
          have b31036 := hb (x (-6) 6)
          have b31037 := hb (x (-5) 5)
          have b31038 := hb (x (-4) 4)
          have b31039 := hb (x (-3) 11)
          have b31040 := hb (x (-2) 10)
          have b31041 := hb (x (-1) 9)
          have b31042 := hb (x 0 8)
          clear * - r31028 e31029 e31030 e31031 e31032 e31033 e31034 b31035 b31036 b31037 b31038 b31039 b31040 b31041 b31042 f31002 g1 d31003 d27996
          omega
        have d31043 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
          have r31044 := hand1 (x (-4) 4) (x (-4) 11)
          have b31045 := hb (x (-4) 4)
          have b31046 := hb (x (-4) 4 && x (-4) 11)
          clear * - r31044 b31045 b31046 d31027
          omega
        have d31047 : (x (-4) 4 && x (-4) 8).toNat = 0 := by
          have r31048 := hand1 (x (-4) 4) (x (-4) 8)
          have b31049 := hb (x (-4) 4)
          have b31050 := hb (x (-4) 4 && x (-4) 8)
          clear * - r31048 b31049 b31050 d31027
          omega
        have d31051 : (x (-2) 2 && x (-2) 13).toNat = 1 := by
          have r31052 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31053 := hb (x (-4) 4)
          have b31054 := hb (x 0 11)
          have b31055 := hb (x (-1) 1 && x (-1) 12)
          have b31056 := hb (x (-2) 2 && x (-2) 13)
          have b31057 := hb (x (-3) 3 && x (-3) 14)
          clear * - r31052 b31053 b31054 b31055 b31056 b31057 g5 g44 d27980 d31027
          omega
        have d31058 : (x (-2) 13).toNat = 1 := by
          have r31059 := hand2 (x (-2) 2) (x (-2) 13)
          have b31060 := hb (x (-2) 13)
          have b31061 := hb (x (-2) 2 && x (-2) 13)
          clear * - r31059 b31060 b31061 d31051
          omega
        have d31062 : (x (-2) 1).toNat = 1 := by
          have r31063 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
          have b31064 := hb (x (-2) 1)
          have b31065 := hb (x (-2) 13)
          clear * - r31063 b31064 b31065 d31058
          omega
        have d31066 : (x (-1) 14).toNat = 0 := by
          have r31067 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31068 := hb (x (-2) 1)
          have b31069 := hb (x (-1) 14)
          clear * - r31067 b31068 b31069 d31062
          omega
        have d31070 : (x (-1) 6).toNat = 0 := by
          have r31071 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
          have b31072 := hb (x (-1) 6)
          have b31073 := hb (x (-1) 14)
          clear * - r31071 b31072 b31073 d31066
          omega
        have d31074 : (x (-1) 6 && x (-1) 10).toNat = 0 := by
          have r31075 := hand1 (x (-1) 6) (x (-1) 10)
          have b31076 := hb (x (-1) 6)
          have b31077 := hb (x (-1) 6 && x (-1) 10)
          clear * - r31075 b31076 b31077 d31070
          omega
        have d31078 : (x (-1) 12).toNat = 0 := by
          have r31079 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31080 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e31081 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b31082 := hb (x (-4) 3)
          have b31083 := hb (x (-3) 2)
          have b31084 := hb (x (-2) 13)
          have b31085 := hb (x (-1) 12)
          clear * - r31079 e31080 e31081 b31082 b31083 b31084 b31085 d31058
          omega
        have d31086 : (x (-1) 4).toNat = 0 := by
          have r31087 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
          have b31088 := hb (x (-1) 4)
          have b31089 := hb (x (-1) 12)
          clear * - r31087 b31088 b31089 d31078
          omega
        have d31090 : (x 2 1 && x 2 12).toNat = 1 := by
          have r31091 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31092 := hb (x (-1) 4)
          have b31093 := hb (x 3 11)
          have b31094 := hb (x 2 1 && x 2 12)
          have b31095 := hb (x 1 2 && x 1 13)
          have b31096 := hb (x 0 3 && x 0 14)
          clear * - r31091 b31092 b31093 b31094 b31095 b31096 g10 d28780 g46 d31086
          omega
        have d31097 : (x 2 12).toNat = 1 := by
          have r31098 := hand2 (x 2 1) (x 2 12)
          have b31099 := hb (x 2 12)
          have b31100 := hb (x 2 1 && x 2 12)
          clear * - r31098 b31099 b31100 d31090
          omega
        have d31101 : (x 1 13).toNat = 0 := by
          have r31102 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31103 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e31104 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b31105 := hb (x (-1) 3)
          have b31106 := hb (x 0 2)
          have b31107 := hb (x 1 13)
          have b31108 := hb (x 2 12)
          clear * - r31102 e31103 e31104 b31105 b31106 b31107 b31108 d31097 f28797
          omega
        have d31109 : (x 1 3 && x 1 13).toNat = 0 := by
          have r31110 := hand2 (x 1 3) (x 1 13)
          have b31111 := hb (x 1 13)
          have b31112 := hb (x 1 3 && x 1 13)
          clear * - r31110 b31111 b31112 d31101
          omega
        have d31113 : (x 2 2 && x 2 12).toNat = 1 := by
          have r31114 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31115 := hb (x (-1) 5)
          have b31116 := hb (x 4 10)
          have b31117 := hb (x 3 1 && x 3 11)
          have b31118 := hb (x 2 2 && x 2 12)
          have b31119 := hb (x 1 3 && x 1 13)
          have b31120 := hb (x 0 4 && x 0 14)
          clear * - r31114 b31115 b31116 b31117 b31118 b31119 b31120 g11 g42 d31109 d27968 g0
          omega
        have d31121 : (x 2 2).toNat = 1 := by
          have r31122 := hand1 (x 2 2) (x 2 12)
          have b31123 := hb (x 2 2)
          have b31124 := hb (x 2 2 && x 2 12)
          clear * - r31122 b31123 b31124 d31113
          omega
        have d31125 : (x 4 12).toNat = 0 := by
          have r31126 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31127 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e31128 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b31129 := hb (x 1 3)
          have b31130 := hb (x 2 2)
          have b31131 := hb (x 3 13)
          have b31132 := hb (x 4 12)
          clear * - r31126 e31127 e31128 b31129 b31130 b31131 b31132 d31121
          omega
        have d31133 : (x 4 2 && x 4 12).toNat = 0 := by
          have r31134 := hand2 (x 4 2) (x 4 12)
          have b31135 := hb (x 4 12)
          have b31136 := hb (x 4 2 && x 4 12)
          clear * - r31134 b31135 b31136 d31125
          omega
        have d31137 : (x 4 4).toNat = 0 := by
          have r31138 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b31139 := hb (x 4 4)
          have b31140 := hb (x 4 12)
          clear * - r31138 b31139 b31140 d31125
          omega
        have d31141 : (x 4 4 && x 4 13).toNat = 0 := by
          have r31142 := hand1 (x 4 4) (x 4 13)
          have b31143 := hb (x 4 4)
          have b31144 := hb (x 4 4 && x 4 13)
          clear * - r31142 b31143 b31144 d31137
          omega
        have d31145 : (x 3 13).toNat = 0 := by
          have r31146 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31147 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e31148 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b31149 := hb (x 1 3)
          have b31150 := hb (x 2 2)
          have b31151 := hb (x 3 13)
          have b31152 := hb (x 4 12)
          clear * - r31146 e31147 e31148 b31149 b31150 b31151 b31152 d31125 d31121
          omega
        have d31153 : (x 3 3 && x 3 13).toNat = 0 := by
          have r31154 := hand2 (x 3 3) (x 3 13)
          have b31155 := hb (x 3 13)
          have b31156 := hb (x 3 3 && x 3 13)
          clear * - r31154 b31155 b31156 d31145
          omega
        have d31157 : (x 3 5).toNat = 0 := by
          have r31158 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
          have b31159 := hb (x 3 5)
          have b31160 := hb (x 3 13)
          clear * - r31158 b31159 b31160 d31145
          omega
        have d31161 : (x 1 3).toNat = 0 := by
          have r31162 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31163 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e31164 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b31165 := hb (x 1 3)
          have b31166 := hb (x 2 2)
          have b31167 := hb (x 3 13)
          have b31168 := hb (x 4 12)
          clear * - r31162 e31163 e31164 b31165 b31166 b31167 b31168 d31125 d31145 d31121
          omega
        have d31169 : (x 1 11).toNat = 0 := by
          have r31170 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
          have b31171 := hb (x 1 3)
          have b31172 := hb (x 1 11)
          clear * - r31170 b31171 b31172 d31161
          omega
        have d31173 : (x 1 4 && x 1 13).toNat = 0 := by
          have r31174 := hand2 (x 1 4) (x 1 13)
          have b31175 := hb (x 1 13)
          have b31176 := hb (x 1 4 && x 1 13)
          clear * - r31174 b31175 b31176 d31101
          omega
        have d31177 : (x 2 3 && x 2 12).toNat = 1 := by
          have r31178 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31179 := hb (x (-1) 6)
          have b31180 := hb (x 5 9)
          have b31181 := hb (x 4 1 && x 4 10)
          have b31182 := hb (x 3 2 && x 3 11)
          have b31183 := hb (x 2 3 && x 2 12)
          have b31184 := hb (x 1 4 && x 1 13)
          have b31185 := hb (x 0 5 && x 0 14)
          clear * - r31178 b31179 b31180 b31181 b31182 b31183 b31184 b31185 g12 g39 g40 d31173 d27903 d31070
          omega
        have d31186 : (x 2 3).toNat = 1 := by
          have r31187 := hand1 (x 2 3) (x 2 12)
          have b31188 := hb (x 2 3)
          have b31189 := hb (x 2 3 && x 2 12)
          clear * - r31187 b31188 b31189 d31177
          omega
        have d31190 : (x 5 12).toNat = 0 := by
          have r31191 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31192 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e31193 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b31194 := hb (x 2 3)
          have b31195 := hb (x 3 2)
          have b31196 := hb (x 4 13)
          have b31197 := hb (x 5 12)
          clear * - r31191 e31192 e31193 b31194 b31195 b31196 b31197 d28843 d31186
          omega
        have d31198 : (x 5 1 && x 5 12).toNat = 0 := by
          have r31199 := hand2 (x 5 1) (x 5 12)
          have b31200 := hb (x 5 12)
          have b31201 := hb (x 5 1 && x 5 12)
          clear * - r31199 b31200 b31201 d31190
          omega
        have d31202 : (x 5 3 && x 5 12).toNat = 0 := by
          have r31203 := hand2 (x 5 3) (x 5 12)
          have b31204 := hb (x 5 12)
          have b31205 := hb (x 5 3 && x 5 12)
          clear * - r31203 b31204 b31205 d31190
          omega
        have d31206 : (x 5 4).toNat = 0 := by
          have r31207 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
          have b31208 := hb (x 5 4)
          have b31209 := hb (x 5 12)
          clear * - r31207 b31208 b31209 d31190
          omega
        have d31210 : (x 4 13).toNat = 0 := by
          have r31211 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31212 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e31213 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b31214 := hb (x 2 3)
          have b31215 := hb (x 3 2)
          have b31216 := hb (x 4 13)
          have b31217 := hb (x 5 12)
          clear * - r31211 e31212 e31213 b31214 b31215 b31216 b31217 d31190 d28843 d31186
          omega
        have d31218 : (x 4 2 && x 4 13).toNat = 0 := by
          have r31219 := hand2 (x 4 2) (x 4 13)
          have b31220 := hb (x 4 13)
          have b31221 := hb (x 4 2 && x 4 13)
          clear * - r31219 b31220 b31221 d31210
          omega
        have d31222 : (x 6 11).toNat = 1 := by
          have r31223 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31224 := hb (x 2 4)
          have b31225 := hb (x 6 11)
          have b31226 := hb (x 5 1 && x 5 12)
          have b31227 := hb (x 4 2 && x 4 13)
          have b31228 := hb (x 3 3 && x 3 14)
          clear * - r31223 b31224 b31225 b31226 b31227 b31228 d31198 d31218 d28827 g9
          omega
        have d31229 : (x 6 3).toNat = 1 := by
          have r31230 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
          have b31231 := hb (x 6 3)
          have b31232 := hb (x 6 11)
          clear * - r31230 b31231 b31232 d31222
          omega
        have d31233 : (x 9 12).toNat = 0 := by
          have r31234 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31235 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e31236 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b31237 := hb (x 6 3)
          have b31238 := hb (x 7 2)
          have b31239 := hb (x 8 13)
          have b31240 := hb (x 9 12)
          clear * - r31234 e31235 e31236 b31237 b31238 b31239 b31240 d31229
          omega
        have d31241 : (x 8 13).toNat = 0 := by
          have r31242 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31243 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e31244 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b31245 := hb (x 6 3)
          have b31246 := hb (x 7 2)
          have b31247 := hb (x 8 13)
          have b31248 := hb (x 9 12)
          clear * - r31242 e31243 e31244 b31245 b31246 b31247 b31248 d31233 d31229
          omega
        have d31249 : (x 7 2).toNat = 0 := by
          have r31250 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31251 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e31252 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b31253 := hb (x 6 3)
          have b31254 := hb (x 7 2)
          have b31255 := hb (x 8 13)
          have b31256 := hb (x 9 12)
          clear * - r31250 e31251 e31252 b31253 b31254 b31255 b31256 d31233 d31241 d31229
          omega
        have d31257 : (x 7 10).toNat = 0 := by
          have r31258 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
          have b31259 := hb (x 7 2)
          have b31260 := hb (x 7 10)
          clear * - r31258 b31259 b31260 d31249
          omega
        have d31261 : (x 7 1 && x 7 10).toNat = 0 := by
          have r31262 := hand2 (x 7 1) (x 7 10)
          have b31263 := hb (x 7 10)
          have b31264 := hb (x 7 1 && x 7 10)
          clear * - r31262 b31263 b31264 d31257
          omega
        have d31265 : (x 9 8).toNat = 0 := by
          have r31266 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31267 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e31268 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e31269 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e31270 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e31271 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e31272 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b31273 := hb (x 2 7)
          have b31274 := hb (x 3 6)
          have b31275 := hb (x 4 5)
          have b31276 := hb (x 5 4)
          have b31277 := hb (x 6 11)
          have b31278 := hb (x 7 10)
          have b31279 := hb (x 8 9)
          have b31280 := hb (x 9 8)
          clear * - r31266 e31267 e31268 e31269 e31270 e31271 e31272 b31273 b31274 b31275 b31276 b31277 b31278 b31279 b31280 d31257 d31222 d31206 d28835
          omega
        have d31281 : (x 8 9).toNat = 0 := by
          have r31282 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31283 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e31284 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e31285 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e31286 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e31287 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e31288 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b31289 := hb (x 2 7)
          have b31290 := hb (x 3 6)
          have b31291 := hb (x 4 5)
          have b31292 := hb (x 5 4)
          have b31293 := hb (x 6 11)
          have b31294 := hb (x 7 10)
          have b31295 := hb (x 8 9)
          have b31296 := hb (x 9 8)
          clear * - r31282 e31283 e31284 e31285 e31286 e31287 e31288 b31289 b31290 b31291 b31292 b31293 b31294 b31295 b31296 d31265 d31257 d31222 d31206 d28835
          omega
        have d31297 : (x 4 5).toNat = 0 := by
          have r31298 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31299 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e31300 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e31301 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e31302 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e31303 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e31304 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b31305 := hb (x 2 7)
          have b31306 := hb (x 3 6)
          have b31307 := hb (x 4 5)
          have b31308 := hb (x 5 4)
          have b31309 := hb (x 6 11)
          have b31310 := hb (x 7 10)
          have b31311 := hb (x 8 9)
          have b31312 := hb (x 9 8)
          clear * - r31298 e31299 e31300 e31301 e31302 e31303 e31304 b31305 b31306 b31307 b31308 b31309 b31310 b31311 b31312 d31265 d31281 d31257 d31222 d31206 d28835
          omega
        have d31313 : (x 2 7).toNat = 0 := by
          have r31314 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31315 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e31316 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e31317 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e31318 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e31319 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e31320 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b31321 := hb (x 2 7)
          have b31322 := hb (x 3 6)
          have b31323 := hb (x 4 5)
          have b31324 := hb (x 5 4)
          have b31325 := hb (x 6 11)
          have b31326 := hb (x 7 10)
          have b31327 := hb (x 8 9)
          have b31328 := hb (x 9 8)
          clear * - r31314 e31315 e31316 e31317 e31318 e31319 e31320 b31321 b31322 b31323 b31324 b31325 b31326 b31327 b31328 d31265 d31281 d31257 d31222 d31206 d31297 d28835
          omega
        have d31329 : (x 2 3 && x 2 7).toNat = 0 := by
          have r31330 := hand2 (x 2 3) (x 2 7)
          have b31331 := hb (x 2 7)
          have b31332 := hb (x 2 3 && x 2 7)
          clear * - r31330 b31331 b31332 d31313
          omega
        have d31333 : (x (-3) 2).toNat = 0 := by
          have r31334 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31335 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e31336 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b31337 := hb (x (-4) 3)
          have b31338 := hb (x (-3) 2)
          have b31339 := hb (x (-2) 13)
          have b31340 := hb (x (-1) 12)
          clear * - r31334 e31335 e31336 b31337 b31338 b31339 b31340 d31078 d31058
          omega
        have d31341 : (x (-3) 10).toNat = 0 := by
          have r31342 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
          have b31343 := hb (x (-3) 2)
          have b31344 := hb (x (-3) 10)
          clear * - r31342 b31343 b31344 d31333
          omega
        have d31345 : (x (-4) 3).toNat = 0 := by
          have r31346 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31347 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e31348 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b31349 := hb (x (-4) 3)
          have b31350 := hb (x (-3) 2)
          have b31351 := hb (x (-2) 13)
          have b31352 := hb (x (-1) 12)
          clear * - r31346 e31347 e31348 b31349 b31350 b31351 b31352 d31078 d31058 d31333
          omega
        have d31353 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
          have r31354 := hand1 (x (-4) 3) (x (-4) 12)
          have b31355 := hb (x (-4) 3)
          have b31356 := hb (x (-4) 3 && x (-4) 12)
          clear * - r31354 b31355 b31356 d31345
          omega
        have d31357 : (x (-4) 11).toNat = 0 := by
          have r31358 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
          have b31359 := hb (x (-4) 3)
          have b31360 := hb (x (-4) 11)
          clear * - r31358 b31359 b31360 d31345
          omega
        have d31361 : (x (-5) 5).toNat = 0 := by
          have r31362 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31363 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e31364 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e31365 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e31366 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e31367 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e31368 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b31369 := hb (x (-7) 7)
          have b31370 := hb (x (-6) 6)
          have b31371 := hb (x (-5) 5)
          have b31372 := hb (x (-4) 4)
          have b31373 := hb (x (-3) 11)
          have b31374 := hb (x (-2) 10)
          have b31375 := hb (x (-1) 9)
          have b31376 := hb (x 0 8)
          clear * - r31362 e31363 e31364 e31365 e31366 e31367 e31368 b31369 b31370 b31371 b31372 b31373 b31374 b31375 b31376 f31002 g1 d31003 d27996 d31027
          omega
        have d31377 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
          have r31378 := hand1 (x (-5) 5) (x (-5) 12)
          have b31379 := hb (x (-5) 5)
          have b31380 := hb (x (-5) 5 && x (-5) 12)
          clear * - r31378 b31379 b31380 d31361
          omega
        have d31381 : (x (-5) 5 && x (-5) 9).toNat = 0 := by
          have r31382 := hand1 (x (-5) 5) (x (-5) 9)
          have b31383 := hb (x (-5) 5)
          have b31384 := hb (x (-5) 5 && x (-5) 9)
          clear * - r31382 b31383 b31384 d31361
          omega
        have d31385 : (x (-6) 6).toNat = 0 := by
          have r31386 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31387 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e31388 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e31389 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e31390 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e31391 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e31392 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b31393 := hb (x (-7) 7)
          have b31394 := hb (x (-6) 6)
          have b31395 := hb (x (-5) 5)
          have b31396 := hb (x (-4) 4)
          have b31397 := hb (x (-3) 11)
          have b31398 := hb (x (-2) 10)
          have b31399 := hb (x (-1) 9)
          have b31400 := hb (x 0 8)
          clear * - r31386 e31387 e31388 e31389 e31390 e31391 e31392 b31393 b31394 b31395 b31396 b31397 b31398 b31399 b31400 f31002 g1 d31003 d27996 d31027 d31361
          omega
        have d31401 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
          have r31402 := hand1 (x (-6) 6) (x (-6) 13)
          have b31403 := hb (x (-6) 6)
          have b31404 := hb (x (-6) 6 && x (-6) 13)
          clear * - r31402 b31403 b31404 d31385
          omega
        have d31405 : (x (-6) 6 && x (-6) 10).toNat = 0 := by
          have r31406 := hand1 (x (-6) 6) (x (-6) 10)
          have b31407 := hb (x (-6) 6)
          have b31408 := hb (x (-6) 6 && x (-6) 10)
          clear * - r31406 b31407 b31408 d31385
          omega
        have d31409 : (x (-7) 7).toNat = 0 := by
          have r31410 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31411 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e31412 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e31413 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e31414 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e31415 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e31416 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b31417 := hb (x (-7) 7)
          have b31418 := hb (x (-6) 6)
          have b31419 := hb (x (-5) 5)
          have b31420 := hb (x (-4) 4)
          have b31421 := hb (x (-3) 11)
          have b31422 := hb (x (-2) 10)
          have b31423 := hb (x (-1) 9)
          have b31424 := hb (x 0 8)
          clear * - r31410 e31411 e31412 e31413 e31414 e31415 e31416 b31417 b31418 b31419 b31420 b31421 b31422 b31423 b31424 f31002 g1 d31003 d27996 d31027 d31361 d31385
          omega
        have d31425 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
          have r31426 := hand1 (x (-7) 7) (x (-7) 14)
          have b31427 := hb (x (-7) 7)
          have b31428 := hb (x (-7) 7 && x (-7) 14)
          clear * - r31426 b31427 b31428 d31409
          omega
        have d31429 : (x (-7) 7 && x (-7) 11).toNat = 0 := by
          have r31430 := hand1 (x (-7) 7) (x (-7) 11)
          have b31431 := hb (x (-7) 7)
          have b31432 := hb (x (-7) 7 && x (-7) 11)
          clear * - r31430 b31431 b31432 d31409
          omega
        have r31433 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r31434 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r31435 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31436 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e31437 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e31438 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e31439 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e31440 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e31441 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have r31442 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31443 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e31444 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e31445 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e31446 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e31447 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e31448 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have r31449 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31450 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
        have e31451 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
        have e31452 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
        have e31453 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
        have e31454 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
        have e31455 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
        have r31456 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31457 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e31458 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e31459 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e31460 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e31461 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e31462 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have r31463 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31464 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e31465 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have r31466 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r31467 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31468 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
        have e31469 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
        have r31470 : 1 ≤ (x 5 4).toNat + (x 4 1 && x 4 5).toNat + (x 3 2 && x 3 6).toNat + (x 2 3 && x 2 7).toNat + (x 1 4 && x 1 8).toNat + (x 0 5 && x 0 9).toNat + (x (-1) 6 && x (-1) 10).toNat + (x (-2) 7 && x (-2) 11).toNat + (x (-3) 8 && x (-3) 12).toNat + (x (-4) 9 && x (-4) 13).toNat + (x (-5) 10 && x (-5) 14).toNat + (x (-6) 11).toNat := by have q := hcov4 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31471 : (x 4 1 && x 4 5).toNat = (x 4 5).toNat := handr _ _ (fun h => hp13 4 (hp5 4 (h)))
        have e31472 : (x (-5) 10 && x (-5) 14).toNat = (x (-5) 10).toNat := handl _ _ (fun h => hp2 (-5) (hp10 (-5) (h)))
        have r31473 : 1 ≤ (x 3 5).toNat + (x 2 1 && x 2 6).toNat + (x 1 2 && x 1 7).toNat + (x 0 3 && x 0 8).toNat + (x (-1) 4 && x (-1) 9).toNat + (x (-2) 5 && x (-2) 10).toNat + (x (-3) 6 && x (-3) 11).toNat + (x (-4) 7 && x (-4) 12).toNat + (x (-5) 8 && x (-5) 13).toNat + (x (-6) 9 && x (-6) 14).toNat + (x (-7) 10).toNat := by have q := hcov5 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r31474 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r31475 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r31476 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r31477 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r31478 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r31479 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r31480 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r31481 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r31482 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
        have r31483 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
        have r31484 := hand2 (x (-2) 2) (x (-2) 6)
        have r31485 := hand2 (x (-8) 8) (x (-8) 12)
        have r31486 := hand1 (x (-9) 9) (x (-9) 13)
        have r31487 := hand1 (x 1 4) (x 1 8)
        have r31488 := hand1 (x (-2) 7) (x (-2) 11)
        have r31489 := hand1 (x (-3) 8) (x (-3) 12)
        have r31490 := hand1 (x (-4) 9) (x (-4) 13)
        have r31491 := hand2 (x 2 1) (x 2 6)
        have r31492 := hand1 (x (-4) 7) (x (-4) 12)
        have r31493 := hand1 (x (-5) 8) (x (-5) 13)
        have r31494 := hand1 (x (-6) 9) (x (-6) 14)
        have r31495 := hand2 (x (-2) 2) (x (-2) 9)
        have r31496 := hand1 (x (-5) 4) (x (-5) 13)
        have r31497 := hand1 (x (-6) 5) (x (-6) 14)
        have r31498 := hand2 (x 2 1) (x 2 10)
        have r31499 := hand1 (x (-2) 5) (x (-2) 14)
        have r31500 := hand1 (x 6 2) (x 6 11)
        have r31501 := hand2 (x 5 1) (x 5 11)
        have r31502 := hand2 (x (-9) 1) (x (-9) 12)
        have r31503 := hand2 (x (-10) 2) (x (-10) 13)
        have r31504 := hand1 (x (-11) 3) (x (-11) 14)
        have r31505 := hand2 (x (-9) 1) (x (-9) 14)
        have r31506 := hand1 (x 4 1) (x 4 14)
        linarith only [r31433, r31434, r31435, e31436, e31437, e31438, e31439, e31440, e31441, r31442, e31443, e31444, e31445, e31446, e31447, e31448, r31449, e31450, e31451, e31452, e31453, e31454, e31455, r31456, e31457, e31458, e31459, e31460, e31461, e31462, r31463, e31464, e31465, r31466, r31467, e31468, e31469, r31470, e31471, e31472, r31473, r31474, r31475, r31476, r31477, r31478, r31479, r31480, r31481, r31482, r31483, r31484, r31485, r31486, r31487, r31488, r31489, r31490, r31491, r31492, r31493, r31494, r31495, r31496, r31497, r31498, r31499, r31500, r31501, r31502, r31503, r31504, r31505, r31506, d31357, d31341, d31086, g0, d31070, g1, g3, d27964, d27899, g4, d28776, g8, d31169, d28815, d31186, d28843, d31157, d31137, d31297, d31206, d31281, d27992, d31047, d31381, d31405, d31429, d28839, d31329, d27907, d31074, d28788, g25, g26, d31023, d28004, g35, d27988, d31043, d31377, d31401, d31425, d31019, d28000, d31353, d28784, g37, g38, d31261, d31202, d31141, d28831, d31133, d31153, g43]
    · have f31637 : (x 0 2).toNat = 1 := by rw [h28796]; rfl
      have d31638 : (x 2 12).toNat = 0 := by
        have r31639 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31640 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e31641 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b31642 := hb (x (-1) 3)
        have b31643 := hb (x 0 2)
        have b31644 := hb (x 1 13)
        have b31645 := hb (x 2 12)
        clear * - r31639 e31640 e31641 b31642 b31643 b31644 b31645 f31637
        omega
      have d31646 : (x 2 2 && x 2 12).toNat = 0 := by
        have r31647 := hand2 (x 2 2) (x 2 12)
        have b31648 := hb (x 2 12)
        have b31649 := hb (x 2 2 && x 2 12)
        clear * - r31647 b31648 b31649 d31638
        omega
      have d31650 : (x 1 13).toNat = 0 := by
        have r31651 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31652 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e31653 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b31654 := hb (x (-1) 3)
        have b31655 := hb (x 0 2)
        have b31656 := hb (x 1 13)
        have b31657 := hb (x 2 12)
        clear * - r31651 e31652 e31653 b31654 b31655 b31656 b31657 d31638 f31637
        omega
      have d31658 : (x 1 3 && x 1 13).toNat = 0 := by
        have r31659 := hand2 (x 1 3) (x 1 13)
        have b31660 := hb (x 1 13)
        have b31661 := hb (x 1 3 && x 1 13)
        clear * - r31659 b31660 b31661 d31650
        omega
      have r31662 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b31663 := hb (x (-1) 5)
      have b31664 := hb (x 4 10)
      have b31665 := hb (x 3 1 && x 3 11)
      have b31666 := hb (x 2 2 && x 2 12)
      have b31667 := hb (x 1 3 && x 1 13)
      have b31668 := hb (x 0 4 && x 0 14)
      linarith only [r31662, b31663, b31664, b31665, b31666, b31667, b31668, g11, g42, d31646, d31658, d27968, g0]

theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a00 (x : ℤ → Fin 16 → Bool)
    (hcount : ∀ u : ℤ, (x (u - 1) 1).toNat + (x (u - 2) 2).toNat + (x (u - 3) 3).toNat + (x (u - 4) 4).toNat + (x (u - 5) 5).toNat + (x (u - 6) 6).toNat + (x (u - 7) 7).toNat + (x (u - 8) 8).toNat + (x (u - 9) 9).toNat + (x (u - 10) 10).toNat + (x (u - 11) 11).toNat + (x (u - 12) 12).toNat + (x (u - 13) 13).toNat + (x (u - 14) 14).toNat = 3)
    (hd14 : ∀ u : ℤ, (x u 14).toNat + (x (u - 1) 1).toNat = 1)
    (hd12 : ∀ u : ℤ, (x u 12).toNat + (x (u - 1) 1 && x (u - 1) 13).toNat + (x (u - 2) 2 && x (u - 2) 14).toNat + (x (u - 3) 3).toNat = 1)
    (hd8 : ∀ u : ℤ, (x u 8).toNat + (x (u - 1) 1 && x (u - 1) 9).toNat + (x (u - 2) 2 && x (u - 2) 10).toNat + (x (u - 3) 3 && x (u - 3) 11).toNat + (x (u - 4) 4 && x (u - 4) 12).toNat + (x (u - 5) 5 && x (u - 5) 13).toNat + (x (u - 6) 6 && x (u - 6) 14).toNat + (x (u - 7) 7).toNat = 1)
    (hcov1 : ∀ u : ℤ, 1 ≤ (x u 1).toNat + (x (u - 1) 1 && x (u - 1) 2).toNat + (x (u - 2) 2 && x (u - 2) 3).toNat + (x (u - 3) 3 && x (u - 3) 4).toNat + (x (u - 4) 4 && x (u - 4) 5).toNat + (x (u - 5) 5 && x (u - 5) 6).toNat + (x (u - 6) 6 && x (u - 6) 7).toNat + (x (u - 7) 7 && x (u - 7) 8).toNat + (x (u - 8) 8 && x (u - 8) 9).toNat + (x (u - 9) 9 && x (u - 9) 10).toNat + (x (u - 10) 10 && x (u - 10) 11).toNat + (x (u - 11) 11 && x (u - 11) 12).toNat + (x (u - 12) 12 && x (u - 12) 13).toNat + (x (u - 13) 13 && x (u - 13) 14).toNat + (x (u - 14) 14).toNat)
    (hcov2 : ∀ u : ℤ, 1 ≤ (x u 2).toNat + (x (u - 1) 1 && x (u - 1) 3).toNat + (x (u - 2) 2 && x (u - 2) 4).toNat + (x (u - 3) 3 && x (u - 3) 5).toNat + (x (u - 4) 4 && x (u - 4) 6).toNat + (x (u - 5) 5 && x (u - 5) 7).toNat + (x (u - 6) 6 && x (u - 6) 8).toNat + (x (u - 7) 7 && x (u - 7) 9).toNat + (x (u - 8) 8 && x (u - 8) 10).toNat + (x (u - 9) 9 && x (u - 9) 11).toNat + (x (u - 10) 10 && x (u - 10) 12).toNat + (x (u - 11) 11 && x (u - 11) 13).toNat + (x (u - 12) 12 && x (u - 12) 14).toNat + (x (u - 13) 13).toNat)
    (hcov3 : ∀ u : ℤ, 1 ≤ (x u 3).toNat + (x (u - 1) 1 && x (u - 1) 4).toNat + (x (u - 2) 2 && x (u - 2) 5).toNat + (x (u - 3) 3 && x (u - 3) 6).toNat + (x (u - 4) 4 && x (u - 4) 7).toNat + (x (u - 5) 5 && x (u - 5) 8).toNat + (x (u - 6) 6 && x (u - 6) 9).toNat + (x (u - 7) 7 && x (u - 7) 10).toNat + (x (u - 8) 8 && x (u - 8) 11).toNat + (x (u - 9) 9 && x (u - 9) 12).toNat + (x (u - 10) 10 && x (u - 10) 13).toNat + (x (u - 11) 11 && x (u - 11) 14).toNat + (x (u - 12) 12).toNat)
    (hcov4 : ∀ u : ℤ, 1 ≤ (x u 4).toNat + (x (u - 1) 1 && x (u - 1) 5).toNat + (x (u - 2) 2 && x (u - 2) 6).toNat + (x (u - 3) 3 && x (u - 3) 7).toNat + (x (u - 4) 4 && x (u - 4) 8).toNat + (x (u - 5) 5 && x (u - 5) 9).toNat + (x (u - 6) 6 && x (u - 6) 10).toNat + (x (u - 7) 7 && x (u - 7) 11).toNat + (x (u - 8) 8 && x (u - 8) 12).toNat + (x (u - 9) 9 && x (u - 9) 13).toNat + (x (u - 10) 10 && x (u - 10) 14).toNat + (x (u - 11) 11).toNat)
    (hcov5 : ∀ u : ℤ, 1 ≤ (x u 5).toNat + (x (u - 1) 1 && x (u - 1) 6).toNat + (x (u - 2) 2 && x (u - 2) 7).toNat + (x (u - 3) 3 && x (u - 3) 8).toNat + (x (u - 4) 4 && x (u - 4) 9).toNat + (x (u - 5) 5 && x (u - 5) 10).toNat + (x (u - 6) 6 && x (u - 6) 11).toNat + (x (u - 7) 7 && x (u - 7) 12).toNat + (x (u - 8) 8 && x (u - 8) 13).toNat + (x (u - 9) 9 && x (u - 9) 14).toNat + (x (u - 10) 10).toNat)
    (hcov6 : ∀ u : ℤ, 1 ≤ (x u 6).toNat + (x (u - 1) 1 && x (u - 1) 7).toNat + (x (u - 2) 2 && x (u - 2) 8).toNat + (x (u - 3) 3 && x (u - 3) 9).toNat + (x (u - 4) 4 && x (u - 4) 10).toNat + (x (u - 5) 5 && x (u - 5) 11).toNat + (x (u - 6) 6 && x (u - 6) 12).toNat + (x (u - 7) 7 && x (u - 7) 13).toNat + (x (u - 8) 8 && x (u - 8) 14).toNat + (x (u - 9) 9).toNat)
    (hcov7 : ∀ u : ℤ, 1 ≤ (x u 7).toNat + (x (u - 1) 1 && x (u - 1) 8).toNat + (x (u - 2) 2 && x (u - 2) 9).toNat + (x (u - 3) 3 && x (u - 3) 10).toNat + (x (u - 4) 4 && x (u - 4) 11).toNat + (x (u - 5) 5 && x (u - 5) 12).toNat + (x (u - 6) 6 && x (u - 6) 13).toNat + (x (u - 7) 7 && x (u - 7) 14).toNat + (x (u - 8) 8).toNat)
    (hcov9 : ∀ u : ℤ, 1 ≤ (x u 9).toNat + (x (u - 1) 1 && x (u - 1) 10).toNat + (x (u - 2) 2 && x (u - 2) 11).toNat + (x (u - 3) 3 && x (u - 3) 12).toNat + (x (u - 4) 4 && x (u - 4) 13).toNat + (x (u - 5) 5 && x (u - 5) 14).toNat + (x (u - 6) 6).toNat)
    (hcov10 : ∀ u : ℤ, 1 ≤ (x u 10).toNat + (x (u - 1) 1 && x (u - 1) 11).toNat + (x (u - 2) 2 && x (u - 2) 12).toNat + (x (u - 3) 3 && x (u - 3) 13).toNat + (x (u - 4) 4 && x (u - 4) 14).toNat + (x (u - 5) 5).toNat)
    (hcov11 : ∀ u : ℤ, 1 ≤ (x u 11).toNat + (x (u - 1) 1 && x (u - 1) 12).toNat + (x (u - 2) 2 && x (u - 2) 13).toNat + (x (u - 3) 3 && x (u - 3) 14).toNat + (x (u - 4) 4).toNat)
    (hcov13 : ∀ u : ℤ, 1 ≤ (x u 13).toNat + (x (u - 1) 1 && x (u - 1) 14).toNat + (x (u - 2) 2).toNat)
    (hp2 : ∀ p, x p 2 = true → x p 14 = true)
    (hp4 : ∀ p, x p 4 = true → x p 12 = true)
    (hp5 : ∀ p, x p 5 = true → x p 13 = true)
    (hp6 : ∀ p, x p 6 = true → x p 14 = true)
    (hp9 : ∀ p, x p 9 = true → x p 1 = true)
    (hp10 : ∀ p, x p 10 = true → x p 2 = true)
    (hp11 : ∀ p, x p 11 = true → x p 3 = true)
    (hp13 : ∀ p, x p 13 = true → x p 1 = true)
    (g0 : (x (-1) 5).toNat = 0)
    (g1 : (x (-1) 9).toNat = 0)
    (g2 : (x (-1) 13).toNat = 0)
    (g3 : (x 0 3).toNat = 0)
    (g4 : (x 0 7).toNat = 0)
    (g5 : (x 0 11).toNat = 0)
    (g6 : (x 0 13).toNat = 0)
    (g7 : (x 0 14).toNat = 1)
    (g8 : (x 1 5).toNat = 0)
    (g9 : (x 2 4).toNat = 0)
    (g10 : (x 3 11).toNat = 0)
    (g11 : (x 4 10).toNat = 0)
    (g12 : (x 5 9).toNat = 0)
    (g13 : (x 6 8).toNat = 0)
    (g14 : (x 6 7 && x 6 8).toNat = 0)
    (g15 : (x 5 8 && x 5 9).toNat = 0)
    (g16 : (x 4 9 && x 4 10).toNat = 0)
    (g17 : (x 3 10 && x 3 11).toNat = 0)
    (g18 : (x 2 4 && x 2 8).toNat = 0)
    (g19 : (x 1 5 && x 1 9).toNat = 0)
    (g20 : (x (-1) 7 && x (-1) 11).toNat = 0)
    (g21 : (x 6 4 && x 6 8).toNat = 0)
    (g22 : (x 5 5 && x 5 9).toNat = 0)
    (g23 : (x 4 6 && x 4 10).toNat = 0)
    (g24 : (x 3 7 && x 3 11).toNat = 0)
    (g25 : (x 0 3 && x 0 8).toNat = 0)
    (g26 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g27 : (x 6 3 && x 6 8).toNat = 0)
    (g28 : (x 5 4 && x 5 9).toNat = 0)
    (g29 : (x 4 5 && x 4 10).toNat = 0)
    (g30 : (x 3 6 && x 3 11).toNat = 0)
    (g31 : (x 6 2 && x 6 8).toNat = 0)
    (g32 : (x 5 3 && x 5 9).toNat = 0)
    (g33 : (x 4 4 && x 4 10).toNat = 0)
    (g34 : (x 3 5 && x 3 11).toNat = 0)
    (g35 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g36 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g37 : (x 0 3 && x 0 12).toNat = 0)
    (g38 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g39 : (x 4 1 && x 4 10).toNat = 0)
    (g40 : (x 3 2 && x 3 11).toNat = 0)
    (g41 : (x 0 1 && x 0 11).toNat = 0)
    (g42 : (x 3 1 && x 3 11).toNat = 0)
    (g43 : (x 2 4 && x 2 14).toNat = 0)
    (g44 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g45 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g46 : (x 0 3 && x 0 14).toNat = 0)
    (g47 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a00_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47
