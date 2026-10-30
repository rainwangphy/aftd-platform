import AFTD.Prelude

/-!
# op652_divisor_list

Topic: graphs   Node: fcc1a41f4b4c

Provenance: helper lemma. step towards op_652_half_degree_packing_negation

The 36 positive divisors of 1248191226 = 2·3²·37⁵, listed explicitly as a Finset ℕ.
-/

/-- The positive divisors of n = 1248191226, as an explicit Finset (a cheap carrier, unlike `Nat.divisors 1248191226` which the kernel cannot enumerate). -/
def op652_divisor_list : Finset ℕ := {1,2,3,6,9,18,37,74,111,222,333,666,1369,2738,4107,8214,12321,24642,50653,101306,151959,303918,455877,911754,1874161,3748322,5622483,11244966,16867449,33734898,69343957,138687914,208031871,416063742,624095613,1248191226}
