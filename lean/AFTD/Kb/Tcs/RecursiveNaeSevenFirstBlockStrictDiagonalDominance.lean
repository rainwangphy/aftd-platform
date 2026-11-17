import AFTD.Prelude

/-!
# recursive_nae_seven_first_block_strict_diagonal_dominance

Topic: quantum   Node: ea40fb2d53b6

Provenance: helper lemma. The exact seven-query candidate in experiments 29997 to 29999; this lemma checks only the first twelve-dimensional block, not the full dual certificate.

The specified integral congruence of the first twelve-dimensional symmetry block is strictly diagonally dominant.
-/

open scoped BigOperators
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

def recursiveNaeSevenBlock0 : Matrix (Fin 12) (Fin 12) ℤ := !![306720, 420336, 420336, 95472, -259920, 720, 720, -298800, 280800, -343008, -343008, -237024;
420336, 1855440, 388368, 262008, -569376, -524808, 186048, -579312, -217728, -526032, -82944, -415008;
420336, 388368, 1855440, 262008, -569376, 186048, -524808, -579312, -217728, -82944, -526032, -415008;
95472, 262008, 262008, 1853280, 182016, -658944, -658944, -844848, -74880, -176832, -176832, -16992;
-259920, -569376, -569376, 182016, 375696, -65016, -65016, 144432, -24192, 254592, 254592, 264096;
720, -524808, 186048, -658944, -65016, 528624, 153792, 442728, 254592, -96624, -214704, -29736;
720, 186048, -524808, -658944, -65016, 153792, 528624, 442728, 254592, -214704, -96624, -29736;
-298800, -579312, -579312, -844848, 144432, 442728, 442728, 1386576, 264096, -29736, -29736, -368352;
280800, -217728, -217728, -74880, -24192, 254592, 254592, 264096, 1186848, -663696, -663696, -501984;
-343008, -526032, -82944, -176832, 254592, -96624, -214704, -29736, -663696, 1540944, 78480, 349272;
-343008, -82944, -526032, -176832, 254592, -214704, -96624, -29736, -663696, 78480, 1540944, 349272;
-237024, -415008, -415008, -16992, 264096, -29736, -29736, -368352, -501984, 349272, 349272, 1131264]

def recursiveNaeSevenBlock0Basis : Matrix (Fin 12) (Fin 12) ℤ := !![256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
-351, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
-402, 38, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0;
5, -31, -31, 256, 0, 0, 0, 0, 0, 0, 0, 0;
79, 55, 55, -45, 256, 0, 0, 0, 0, 0, 0, 0;
-4, 164, 40, 29, 338, 256, 0, 0, 0, 0, 0, 0;
-2, -41, 144, 15, 170, -127, 256, 0, 0, 0, 0, 0;
383, 12, 12, -82, 165, -224, -224, 256, 0, 0, 0, 0;
-716, 114, 114, -30, -69, 6, 6, -122, 256, 0, 0, 0;
114, 238, -234, 173, -114, 593, -221, 23, 41, 256, 0, 0;
196, -63, 70, 298, -196, 203, 434, 39, 70, 183, 256, 0;
-119, 127, 127, 12, -73, -107, -107, 184, 270, 73, 73, 256]

def recursiveNaeSevenBlock0Congruence : Matrix (Fin 12) (Fin 12) ℤ := recursiveNaeSevenBlock0Basis * recursiveNaeSevenBlock0 * recursiveNaeSevenBlock0Basis.transpose

/-- A Lean-checked arithmetic component of the seven-query dual candidate. -/
theorem recursive_nae_seven_first_block_strict_diagonal_dominance :  ∀ i : Fin 12, (∑ j ∈ Finset.univ.erase i, |recursiveNaeSevenBlock0Congruence i j|) < recursiveNaeSevenBlock0Congruence i i := by
  intro i
  fin_cases i <;> decide
