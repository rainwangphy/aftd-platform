import AFTD.Prelude

/-!
# digraph_strict54_out_mask

Topic: graphs   Node: d82158046956

Provenance: helper lemma. Bitmask certificate for the 54-vertex strictness witness of the weighted center route (IN-522).

Bit v of the value at u is set exactly when u -> v is an arc of the 54-vertex strictness witness graph.
-/

def digraph_strict54_out_mask (u : ℕ) : ℕ :=
  (bif u.blt 27 then (bif u.blt 13 then (bif u.blt 6 then (bif u.blt 3 then (bif u.blt 1 then 9007212408160514 else (bif u.blt 2 then 9007225561580036 else 52613678088)) else (bif u.blt 4 then 105227356176 else (bif u.blt 5 then 210454712352 else 420909424704))) else (bif u.blt 9 then (bif u.blt 7 then 841818849408 else (bif u.blt 8 then 1683637698816 else 3367275397632)) else (bif u.blt 11 then (bif u.blt 10 then 6734550795264 else 13469101590528) else (bif u.blt 12 then 26938203181056 else 53876406362112)))) else (bif u.blt 20 then (bif u.blt 16 then (bif u.blt 14 then 107752812724224 else (bif u.blt 15 then 215505625448448 else 431011250896896)) else (bif u.blt 18 then (bif u.blt 17 then 862022501793792 else 10731244258328576) else (bif u.blt 19 then 3448090007175168 else 6896180014350336))) else (bif u.blt 23 then (bif u.blt 21 then 4785160773959681 else (bif u.blt 22 then 563122293178371 else 1126244586356742)) else (bif u.blt 25 then (bif u.blt 24 then 2252489172713484 else 4504978345426968) else (bif u.blt 26 then 9009956690853937 else 5514872225890))))) else (bif u.blt 40 then (bif u.blt 33 then (bif u.blt 30 then (bif u.blt 28 then 11029744451780 else (bif u.blt 29 then 22059488903560 else 44118977807120)) else (bif u.blt 31 then 88237955614240 else (bif u.blt 32 then 176475911228480 else 352951822456960))) else (bif u.blt 36 then (bif u.blt 34 then 705903644913920 else (bif u.blt 35 then 1411807289827840 else 2823614579655680)) else (bif u.blt 38 then (bif u.blt 37 then 5647229159311360 else 2287259063881729) else (bif u.blt 39 then 4574518127763458 else 141837000785925)))) else (bif u.blt 47 then (bif u.blt 43 then (bif u.blt 41 then 283674001571850 else (bif u.blt 42 then 567348003143700 else 1134696006287400)) else (bif u.blt 45 then (bif u.blt 44 then 2269392012574800 else 4538784025149600) else (bif u.blt 46 then 70368795558209 else 140737591116418))) else (bif u.blt 50 then (bif u.blt 48 then 281475182232836 else (bif u.blt 49 then 562950364465672 else 1125900728931344)) else (bif u.blt 52 then (bif u.blt 51 then 2251801457862688 else 4503602915725376) else (bif u.blt 53 then 6576709761 else 536920372))))))
