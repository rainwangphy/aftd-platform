import AFTD.Prelude

/-!
# triangle_hypergraph_obstruction

Topic: graphs   Node: 7a2713f4bb13

Provenance: helper lemma. Related work: https://web.math.princeton.edu/~pds/barbados17/openproblems2017.pdf, problem 10, describes restrictions on triangle hypergraphs. This explicit finite obstruction was found in experiment 13104.

The six-triple seven-point linear hypergraph used to show that the triangle packing-cover inequality does not extend to all linear degree-three triple systems without the full seven-edge plane.
-/

def triangle_hypergraph_obstruction : Finset (Finset (Fin 7)) := {{0, 1, 6}, {3, 4, 6}, {0, 2, 3}, {2, 5, 6}, {1, 3, 5}, {0, 4, 5}}
