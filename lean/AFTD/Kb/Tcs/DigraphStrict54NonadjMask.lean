import AFTD.Prelude

/-!
# digraph_strict54_nonadj_mask

Topic: graphs   Node: 5785bf2f5cb0

Provenance: helper lemma. Bitmask certificate for the 54-vertex strictness witness of the weighted center route (IN-522).

Bit v of the value at u is set exactly when v differs from u and u, v have no common predecessor in the 54-vertex strictness witness graph.
-/

def digraph_strict54_nonadj_mask (u : ℕ) : ℕ :=
  (bif u.blt 27 then (bif u.blt 13 then (bif u.blt 6 then (bif u.blt 3 then (bif u.blt 1 then 1156687314554376 else (bif u.blt 2 then 2313374629108752 else 4626749258217472)) else (bif u.blt 4 then 9253498516435009 else (bif u.blt 5 then 492598523338882 else 985197046726656))) else (bif u.blt 9 then (bif u.blt 7 then 10977593348293128 else (bif u.blt 8 then 12947987441845264 else 7881576374208512)) else (bif u.blt 11 then (bif u.blt 10 then 6755953493676097 else 13511906987352195) else (bif u.blt 12 then 9009415465222407 else 9011631675703822)))) else (bif u.blt 20 then (bif u.blt 16 then (bif u.blt 14 then 9016064096666652 else (bif u.blt 15 then 17729683851272 else 35459367702592)) else (bif u.blt 18 then (bif u.blt 17 then 70918735405280 else 141837470810560) else (bif u.blt 19 then 283674941621120 else 9574549137983232))) else (bif u.blt 23 then (bif u.blt 21 then 10141899021225472 else (bif u.blt 22 then 11276598787709952 else 13545998320678912)) else (bif u.blt 25 then (bif u.blt 24 then 9077598131875841 else 9147997009010690) else (bif u.blt 26 then 281595508539396 else 563191017078792))))) else (bif u.blt 40 then (bif u.blt 33 then (bif u.blt 30 then (bif u.blt 28 then 10133581288898576 else (bif u.blt 29 then 2252764068315168 else 4505528136630336)) else (bif u.blt 31 then 9011056273260673 else (bif u.blt 32 then 7714037039362 else 15428074078724))) else (bif u.blt 36 then (bif u.blt 34 then 30856148157448 else (bif u.blt 35 then 61712296314896 else 9130623847370784)) else (bif u.blt 38 then (bif u.blt 37 then 9254048440000576 else 9500897625260160) else (bif u.blt 39 then 9994595995779328 else 1974793482076672)))) else (bif u.blt 47 then (bif u.blt 43 then (bif u.blt 41 then 12956786218894336 else (bif u.blt 42 then 7899173928306688 else 15798347856613377)) else (bif u.blt 45 then (bif u.blt 44 then 13582297203744771 else 9150195898007559) else (bif u.blt 46 then 285993286533134 else 9579185827807260))) else (bif u.blt 50 then (bif u.blt 48 then 10151172400873528 else (bif u.blt 49 then 11295145547006064 else 4575892584530144)) else (bif u.blt 52 then (bif u.blt 51 then 144585914319297 else 9296371083379586) else (bif u.blt 53 then 9585542912018180 else 7280383124585672))))))
