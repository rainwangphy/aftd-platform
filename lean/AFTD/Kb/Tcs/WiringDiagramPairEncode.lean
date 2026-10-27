import AFTD.Prelude
import AFTD.Kb.Tcs.WiringDiagramPair
import AFTD.Kb.Tcs.FinTriples
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.OrderedTriple

/-!
# wiring_diagram_pair_encode

Topic: np_completeness   Node: dcd261fa6316

Provenance: formalization of a published result. Source: arXiv:2610.03808 Sec. 2

Encodes an instance of a pair of wiring diagrams on m pseudolines as a list of Booleans consisting of m unary ones followed by false and the truth values of u and v on all ordered triples.
-/

/-- Boolean list encoding of a pair of wiring diagrams on m pseudolines. -/
def wiring_diagram_pair_encode (inst : WiringDiagramPair) : List Bool :=
  List.replicate inst.m true ++ [false] ++
    (fin_triples inst.m).map (fun t => inst.u t == 1) ++
    (fin_triples inst.m).map (fun t => inst.v t == 1)
