import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck000
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck001
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck002
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck010
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck011
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck012
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck020
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck021
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck022
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck100
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck101
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck102
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck110
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck111
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck112
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck120
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck121
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck122
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck200
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck201
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck202
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck210
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck211
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck212
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck220
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck221
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck222
import AFTD.Kb.GameTheoryEconomics.Pmms3cVerify
import AFTD.Kb.GameTheoryEconomics.Pmms3cTreeGet
import AFTD.Kb.GameTheoryEconomics.Pmms3cCert

/-!
# pmms3c_check

Topic: fair_division   Node: 2bfc4d98a114

Every one of the 3^9 allocations passes the certificate check.
-/

theorem pmms3c_check (a b c d e f g h k : Fin 3) : pmms3c_verify ![a, b, c, d, e, f, g, h, k] (pmms3c_tree_get pmms3c_cert [a, b, c, d, e, f, g, h, k]) = true := by
  fin_cases a <;> fin_cases b <;> fin_cases c
  exacts [pmms3c_check_000 d e f g h k,
    pmms3c_check_001 d e f g h k,
    pmms3c_check_002 d e f g h k,
    pmms3c_check_010 d e f g h k,
    pmms3c_check_011 d e f g h k,
    pmms3c_check_012 d e f g h k,
    pmms3c_check_020 d e f g h k,
    pmms3c_check_021 d e f g h k,
    pmms3c_check_022 d e f g h k,
    pmms3c_check_100 d e f g h k,
    pmms3c_check_101 d e f g h k,
    pmms3c_check_102 d e f g h k,
    pmms3c_check_110 d e f g h k,
    pmms3c_check_111 d e f g h k,
    pmms3c_check_112 d e f g h k,
    pmms3c_check_120 d e f g h k,
    pmms3c_check_121 d e f g h k,
    pmms3c_check_122 d e f g h k,
    pmms3c_check_200 d e f g h k,
    pmms3c_check_201 d e f g h k,
    pmms3c_check_202 d e f g h k,
    pmms3c_check_210 d e f g h k,
    pmms3c_check_211 d e f g h k,
    pmms3c_check_212 d e f g h k,
    pmms3c_check_220 d e f g h k,
    pmms3c_check_221 d e f g h k,
    pmms3c_check_222 d e f g h k]
