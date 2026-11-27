import AFTD.Prelude

/-!
# op309_uniform28_four_palette_kernel

Topic: graphs   Node: cf8b4aa5f12e

Provenance: helper lemma. OP-309 girth-six uniform-host five-color quotient, experiment 42517.

The nine-class palette pattern consisting of two four-cliques and three cross constraints cannot be colored with four colors.
-/

private theorem uniform28_three_exclusion (b c d h i : Fin 4)
    (hdh : d ≠ h) (hdi : d ≠ i) (hhi : h ≠ i)
    (hbd : b ≠ d) (hbh : b ≠ h) (hbi : b ≠ i)
    (hcd : c ≠ d) (hch : c ≠ h) (hci : c ≠ i) : b = c := by
  fin_cases d <;> fin_cases h <;> simp_all
  all_goals fin_cases i <;> simp_all
  all_goals fin_cases b <;> simp_all
  all_goals fin_cases c <;> simp_all

private theorem uniform28_two_sides_disjoint (a b e f g : Fin 4)
    (hae : a ≠ e) (haf : a ≠ f) (hag : a ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hba : b ≠ a) (hbe : b ≠ e) (hbf : b ≠ f) (hbg : b ≠ g) : False := by
  fin_cases a <;> fin_cases e <;> simp_all
  all_goals fin_cases f <;> simp_all
  all_goals fin_cases g <;> simp_all
  all_goals fin_cases b <;> simp_all

theorem op309_uniform28_four_palette_kernel
    (a b c d e f g h i : Fin 4)
    (hae : a ≠ e) (haf : a ≠ f) (hag : a ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hba : b ≠ a) (hbe : b ≠ e)
    (hcf : c ≠ f) (hcg : c ≠ g)
    (hcd : c ≠ d) (hch : c ≠ h) (hci : c ≠ i)
    (hdh : d ≠ h) (hdi : d ≠ i) (hhi : h ≠ i)
    (hbd : b ≠ d) (hbh : b ≠ h) (hbi : b ≠ i) : False := by
  have hbc := uniform28_three_exclusion b c d h i hdh hdi hhi hbd hbh hbi hcd hch hci
  subst c
  exact uniform28_two_sides_disjoint a b e f g hae haf hag hef heg hfg hba hbe hcf hcg
