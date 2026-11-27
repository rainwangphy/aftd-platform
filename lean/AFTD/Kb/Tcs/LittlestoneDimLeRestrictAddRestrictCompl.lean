import AFTD.Prelude
import AFTD.Kb.Tcs.LittlestoneDim
import AFTD.Kb.Tcs.LittlestoneShatters
import AFTD.Kb.Tcs.ConceptClassRestrict
import AFTD.Kb.Tcs.ConceptClassRestrictNonempty
import AFTD.Kb.Tcs.G

/-!
# littlestone_dim_le_restrict_add_restrict_compl

Topic: learning   Node: 3ff05685ba65

Provenance: formalization of a published result. Source: arXiv:2611.26721 (Littlestone dimension and its dual), Fact 2.2 (subadditivity).

For every nonempty class H of functions X → Bool and every subset Y of X, the Littlestone dimension of H (in ℕ∞) is at most the Littlestone dimension of the restriction of H to Y plus the Littlestone dimension of the restriction of H to the complement X \ Y.
-/

theorem littlestone_shatters_nonempty {X : Type*} :
    ∀ (k : ℕ) (S : Set (X → Bool)), littlestone_shatters S k → S.Nonempty
  | 0, _, h => h
  | k + 1, _, ⟨_, hy, _⟩ => by
    obtain ⟨g, hg, _⟩ := littlestone_shatters_nonempty k _ hy
    exact ⟨g, hg⟩

theorem littlestone_shatters_mono {X : Type*} :
    ∀ (k : ℕ) (S T : Set (X → Bool)), S ⊆ T → littlestone_shatters S k →
      littlestone_shatters T k
  | 0, _, _, hST, h => Set.Nonempty.mono hST h
  | k + 1, _, _, hST, ⟨x, h0, h1⟩ =>
    ⟨x, littlestone_shatters_mono k _ _ (fun g hg => ⟨hST hg.1, hg.2⟩) h0,
      littlestone_shatters_mono k _ _ (fun g hg => ⟨hST hg.1, hg.2⟩) h1⟩

theorem littlestone_shatters_succ {X : Type*} :
    ∀ (k : ℕ) (S : Set (X → Bool)), littlestone_shatters S (k + 1) → littlestone_shatters S k
  | 0, _, ⟨_, h0, _⟩ => by
    obtain ⟨g, hg, _⟩ := littlestone_shatters_nonempty 0 _ h0
    exact ⟨g, hg⟩
  | k + 1, _, ⟨x, h0, h1⟩ =>
    ⟨x, littlestone_shatters_succ k _ h0, littlestone_shatters_succ k _ h1⟩

theorem littlestone_shatters_le {X : Type*} (S : Set (X → Bool)) (k d : ℕ) (hkd : k ≤ d)
    (h : littlestone_shatters S d) : littlestone_shatters S k := by
  induction d with
  | zero => rwa [Nat.le_zero.1 hkd]
  | succ d ih =>
    rcases Nat.lt_or_ge k (d + 1) with hk | hk
    · exact ih (by omega) (littlestone_shatters_succ d S h)
    · rwa [le_antisymm hkd hk]

theorem littlestone_restrict_fiber {X : Type*} (S : Set (X → Bool)) (Y : Set X) (y : Y)
    (b : Bool) :
    concept_class_restrict {h ∈ S | h y.1 = b} Y ⊆
      {g ∈ concept_class_restrict S Y | g y = b} := by
  rintro g ⟨h, ⟨hS, hb⟩, rfl⟩
  exact ⟨⟨h, hS, rfl⟩, hb⟩

theorem littlestone_restrict_mono {X : Type*} (S T : Set (X → Bool)) (Y : Set X)
    (hST : S ⊆ T) : concept_class_restrict S Y ⊆ concept_class_restrict T Y :=
  Set.image_mono hST

theorem littlestone_split_aux {X : Type*} :
    ∀ (n : ℕ) (S : Set (X → Bool)) (d1 d2 : ℕ) (Y Z : Set X), d1 + d2 = n →
      (∀ x, x ∈ Y ∨ x ∈ Z) → littlestone_shatters S (n + 1) →
      littlestone_shatters (concept_class_restrict S Y) (d1 + 1) ∨
        littlestone_shatters (concept_class_restrict S Z) (d2 + 1) := by
  intro n
  induction n with
  | zero =>
    intro S d1 d2 Y Z hd hYZ hS
    obtain ⟨x, h0, h1⟩ := hS
    have hd1 : d1 = 0 := by omega
    have hd2 : d2 = 0 := by omega
    subst hd1 hd2
    rcases hYZ x with hx | hx
    · left
      refine ⟨⟨x, hx⟩, ?_, ?_⟩
      · exact (concept_class_restrict_nonempty _ Y h0).mono
          (littlestone_restrict_fiber S Y ⟨x, hx⟩ false)
      · exact (concept_class_restrict_nonempty _ Y h1).mono
          (littlestone_restrict_fiber S Y ⟨x, hx⟩ true)
    · right
      refine ⟨⟨x, hx⟩, ?_, ?_⟩
      · exact (concept_class_restrict_nonempty _ Z h0).mono
          (littlestone_restrict_fiber S Z ⟨x, hx⟩ false)
      · exact (concept_class_restrict_nonempty _ Z h1).mono
          (littlestone_restrict_fiber S Z ⟨x, hx⟩ true)
  | succ n ih =>
    intro S d1 d2 Y Z hd hYZ hS
    obtain ⟨x, h0, h1⟩ := hS
    have sub0 : {h ∈ S | h x = false} ⊆ S := fun _ hg => hg.1
    have sub1 : {h ∈ S | h x = true} ⊆ S := fun _ hg => hg.1
    rcases hYZ x with hx | hx
    · rcases d1 with _ | d1
      · left
        refine ⟨⟨x, hx⟩, ?_, ?_⟩
        · exact (concept_class_restrict_nonempty _ Y
            (littlestone_shatters_nonempty _ _ h0)).mono
            (littlestone_restrict_fiber S Y ⟨x, hx⟩ false)
        · exact (concept_class_restrict_nonempty _ Y
            (littlestone_shatters_nonempty _ _ h1)).mono
            (littlestone_restrict_fiber S Y ⟨x, hx⟩ true)
      · rcases ih _ d1 d2 Y Z (by omega) hYZ h0 with a0 | a0
        · rcases ih _ d1 d2 Y Z (by omega) hYZ h1 with a1 | a1
          · left
            exact ⟨⟨x, hx⟩,
              littlestone_shatters_mono _ _ _ (littlestone_restrict_fiber S Y ⟨x, hx⟩ false) a0,
              littlestone_shatters_mono _ _ _ (littlestone_restrict_fiber S Y ⟨x, hx⟩ true) a1⟩
          · right
            exact littlestone_shatters_mono _ _ _ (littlestone_restrict_mono _ _ Z sub1) a1
        · right
          exact littlestone_shatters_mono _ _ _ (littlestone_restrict_mono _ _ Z sub0) a0
    · rcases d2 with _ | d2
      · right
        refine ⟨⟨x, hx⟩, ?_, ?_⟩
        · exact (concept_class_restrict_nonempty _ Z
            (littlestone_shatters_nonempty _ _ h0)).mono
            (littlestone_restrict_fiber S Z ⟨x, hx⟩ false)
        · exact (concept_class_restrict_nonempty _ Z
            (littlestone_shatters_nonempty _ _ h1)).mono
            (littlestone_restrict_fiber S Z ⟨x, hx⟩ true)
      · rcases ih _ d1 d2 Y Z (by omega) hYZ h0 with a0 | a0
        · left
          exact littlestone_shatters_mono _ _ _ (littlestone_restrict_mono _ _ Y sub0) a0
        · rcases ih _ d1 d2 Y Z (by omega) hYZ h1 with a1 | a1
          · left
            exact littlestone_shatters_mono _ _ _ (littlestone_restrict_mono _ _ Y sub1) a1
          · right
            exact ⟨⟨x, hx⟩,
              littlestone_shatters_mono _ _ _ (littlestone_restrict_fiber S Z ⟨x, hx⟩ false) a0,
              littlestone_shatters_mono _ _ _ (littlestone_restrict_fiber S Z ⟨x, hx⟩ true) a1⟩

theorem littlestone_dim_le_restrict_add_restrict_compl {X : Type*} (H : Set (X → Bool))
    (hH : H.Nonempty) (Y : Set X) :
    littlestone_dim H ≤
      littlestone_dim (concept_class_restrict H Y) + littlestone_dim (concept_class_restrict H Yᶜ) := by
  rcases eq_top_or_lt_top (littlestone_dim (concept_class_restrict H Y)) with ha | ha
  · rw [ha, top_add]; exact le_top
  rcases eq_top_or_lt_top (littlestone_dim (concept_class_restrict H Yᶜ)) with hb | hb
  · rw [hb, add_top]; exact le_top
  obtain ⟨a, ha'⟩ := ENat.ne_top_iff_exists.1 ha.ne
  obtain ⟨b, hb'⟩ := ENat.ne_top_iff_exists.1 hb.ne
  rw [← ha', ← hb']
  unfold littlestone_dim
  apply iSup₂_le
  intro d hd
  by_contra hlt
  have hlt' : a + b + 1 ≤ d := by
    have : ¬ d ≤ a + b := fun h => hlt (by rw [← Nat.cast_add]; exact Nat.cast_le.2 h)
    omega
  have hs := littlestone_shatters_le H (a + b + 1) d hlt' hd
  rcases littlestone_split_aux (a + b) H a b Y Yᶜ rfl (fun x => em (x ∈ Y)) hs with h | h
  · have : ((a + 1 : ℕ) : ℕ∞) ≤ littlestone_dim (concept_class_restrict H Y) :=
      le_iSup₂ (f := fun (d : ℕ) (_ : littlestone_shatters (concept_class_restrict H Y) d) =>
        (d : ℕ∞)) (a + 1) h
    rw [← ha'] at this
    have : a + 1 ≤ a := Nat.cast_le.1 this
    omega
  · have : ((b + 1 : ℕ) : ℕ∞) ≤ littlestone_dim (concept_class_restrict H Yᶜ) :=
      le_iSup₂ (f := fun (d : ℕ) (_ : littlestone_shatters (concept_class_restrict H Yᶜ) d) =>
        (d : ℕ∞)) (b + 1) h
    rw [← hb'] at this
    have : b + 1 ≤ b := Nat.cast_le.1 this
    omega
