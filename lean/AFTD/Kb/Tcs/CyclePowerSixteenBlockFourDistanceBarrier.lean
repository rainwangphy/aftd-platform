import AFTD.Prelude

/-!
# cycle_power_sixteen_block_four_distance_barrier

Topic: combinatorics   Node: 1a559d02b1c8

Provenance: helper lemma. Route barrier for OP-205 / RT-1. Experiment8071 found global periodic countermodels to a proposed four-distance shortcut. Experiment8075 exported the64 profile masks and independently checked all retained conditions. The Lean proof checks the entire finite certificate by kernel reduction. No main conjecture or research advance is claimed.

There exists a period64 rooted Boolean profile table on32 offsets with selected endpoints, parent matchings at distances16/24/28, monotone first/last four positions, exact pair ownership at distances16/24/28/30, and coverage of the four ordinary distances9/17/23/26. It selects offset7 and misses3 at root0, an upper-half vertical defect. It also fails coverage at distance10 at residue54. Thus this four-distance relaxation does not suffice. The predicate cp4_valid explicitly contains only those four ordinary distances; this is not a model of full ordinary coverage or a refutation of OP-205.
-/

open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def cp4_masks : Fin 64 → ℕ := ![2164261251,2147483649,3221225473,4026531847,2147483649,3221225473,4256825599,2147483649,3221225473,3221225473,4026793999,2147483651,2147483649,3221225473,4294967295,2147483649,3221225479,2147483649,3221225473,4160749583,2147483649,3221225475,2147483649,4286579199,2147483649,3221225479,2147483651,2147483649,4160765967,2147483649,3221225475,2147483649,4294966271,2147483651,2147483649,3758096387,2147483649,4160749599,2147483649,3221241857,3758096387,2147483649,4286584831,2147483649,3221225473,3221225473,4026531847,2147614723,2147483649,4261412927,2147483649,3221225487,2147483651,2147483651,2147483649,4294967295,2147483651,2147483651,2147483649,4026531855,2147483651,2147483649,3221225601,4244635711]
def cp4_model (p : Fin 64) (a : ℕ) : Bool := (cp4_masks p).testBit a

def cp4_root (v : Fin 64) (a : ℕ) : Fin 64 :=
  ⟨(v.val+64-a)%64, Nat.mod_lt _ (by decide)⟩

def cp4_distances : Fin 4 → ℕ := ![9,17,23,26]

def cp4_cover (B : Fin 64 → ℕ → Bool) (v : Fin 64) (d : ℕ) : Prop :=
  ∃ a : Fin 32, a.val < 32-d ∧ B (cp4_root v a.val) a.val = true ∧
    B (cp4_root v a.val) (a.val+d) = true

instance cp4_cover_decidable (B : Fin 64 → ℕ → Bool) (v : Fin 64) (d : ℕ) :
    Decidable (cp4_cover B v d) := by unfold cp4_cover; infer_instance

def cp4_valid (B : Fin 64 → ℕ → Bool) : Prop :=
  (∀ p : Fin 64, B p 0 = true ∧ B p 31 = true) ∧
  (∀ (p : Fin 64) (a : Fin 16),
    (a.val < 8 → B p (a.val+16) = true → B p a.val = true) ∧
    (8 ≤ a.val → B p a.val = true → B p (a.val+16) = true)) ∧
  (∀ (p : Fin 64) (a : Fin 8),
    (a.val < 4 → B p (a.val+24) = true → B p a.val = true) ∧
    (4 ≤ a.val → B p a.val = true → B p (a.val+24) = true)) ∧
  (∀ (p : Fin 64) (a : Fin 4),
    (a.val < 2 → B p (a.val+28) = true → B p a.val = true) ∧
    (2 ≤ a.val → B p a.val = true → B p (a.val+28) = true)) ∧
  (∀ (p : Fin 64) (a b : Fin 4), a.val ≤ b.val → B p b.val = true → B p a.val = true) ∧
  (∀ (p : Fin 64) (a b : Fin 4), a.val ≤ b.val → B p (28+a.val) = true → B p (28+b.val) = true) ∧
  (∀ v : Fin 64, (range 16).sum (fun a => (B (cp4_root v a) a && B (cp4_root v a) (a+16)).toNat) = 1) ∧
  (∀ v : Fin 64, (range 8).sum (fun a => (B (cp4_root v a) a && B (cp4_root v a) (a+24)).toNat) = 1) ∧
  (∀ v : Fin 64, (range 4).sum (fun a => (B (cp4_root v a) a && B (cp4_root v a) (a+28)).toNat) = 1) ∧
  (∀ v : Fin 64, (range 2).sum (fun a => (B (cp4_root v a) a && B (cp4_root v a) (a+30)).toNat) = 1) ∧
  (∀ (i : Fin 4) (v : Fin 64), cp4_cover B v (cp4_distances i))

instance cp4_valid_decidable (B : Fin 64 → ℕ → Bool) : Decidable (cp4_valid B) := by
  unfold cp4_valid; infer_instance

lemma cp4_checked : cp4_valid cp4_model := by decide +kernel
lemma cp4_defect : cp4_model 0 7 = true ∧ cp4_model 0 3 = false := by decide +kernel
lemma cp4_missing : ¬cp4_cover cp4_model 54 10 := by decide +kernel

theorem cycle_power_sixteen_block_four_distance_barrier :
    ∃ B : Fin 64 → ℕ → Bool, cp4_valid B ∧ B 0 7 = true ∧ B 0 3 = false ∧ ¬cp4_cover B 54 10 := by
  exact ⟨cp4_model,cp4_checked,cp4_defect.1,cp4_defect.2,cp4_missing⟩
