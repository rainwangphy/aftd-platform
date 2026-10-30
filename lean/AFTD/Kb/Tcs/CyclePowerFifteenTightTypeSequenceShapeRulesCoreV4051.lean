import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_shape_rules_core_v40_51

Topic: combinatorics   Node: ef9465ab4b1a

Provenance: helper lemma. Research thread RT-1, open case k = 15 (m = 4) of OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Experiment 9757: on the integer window [-24, 24] the layer-free tight-class model leaves 13 class types at the centre, none with an island; on [-32, 32] the six types {0,15}, {0,1,14,15}, {0..3,12..15}, {0..7,12..15}, {0..3,8..15}, {0..15}.

Window refutation for k = 15: in the layer-free tight-class model on the integer line (x p j: the class starting at p contains p + j; inner count 3 per vertex, distances 14, 12, 8 covered exactly once, the other distances covered, classes closed under the tight-class parent map), with x p 1 = x p 14 and x p 2 = x p 3 everywhere, the class at 0 cannot have bit 4 = 0 and bit 5 = 1.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v40_51_aux (x : ℤ → Fin 16 → Bool)
    (hcount : ∀ u : ℤ, (x (u - 1) 1).toNat + (x (u - 2) 2).toNat + (x (u - 3) 3).toNat + (x (u - 4) 4).toNat + (x (u - 5) 5).toNat + (x (u - 6) 6).toNat + (x (u - 7) 7).toNat + (x (u - 8) 8).toNat + (x (u - 9) 9).toNat + (x (u - 10) 10).toNat + (x (u - 11) 11).toNat + (x (u - 12) 12).toNat + (x (u - 13) 13).toNat + (x (u - 14) 14).toNat = 3)
    (hd14 : ∀ u : ℤ, (x u 14).toNat + (x (u - 1) 1).toNat = 1)
    (hd12 : ∀ u : ℤ, (x u 12).toNat + (x (u - 1) 1 && x (u - 1) 13).toNat + (x (u - 2) 2 && x (u - 2) 14).toNat + (x (u - 3) 3).toNat = 1)
    (hd8 : ∀ u : ℤ, (x u 8).toNat + (x (u - 1) 1 && x (u - 1) 9).toNat + (x (u - 2) 2 && x (u - 2) 10).toNat + (x (u - 3) 3 && x (u - 3) 11).toNat + (x (u - 4) 4 && x (u - 4) 12).toNat + (x (u - 5) 5 && x (u - 5) 13).toNat + (x (u - 6) 6 && x (u - 6) 14).toNat + (x (u - 7) 7).toNat = 1)
    (hcov1 : ∀ u : ℤ, 1 ≤ (x u 1).toNat + (x (u - 1) 1 && x (u - 1) 2).toNat + (x (u - 2) 2 && x (u - 2) 3).toNat + (x (u - 3) 3 && x (u - 3) 4).toNat + (x (u - 4) 4 && x (u - 4) 5).toNat + (x (u - 5) 5 && x (u - 5) 6).toNat + (x (u - 6) 6 && x (u - 6) 7).toNat + (x (u - 7) 7 && x (u - 7) 8).toNat + (x (u - 8) 8 && x (u - 8) 9).toNat + (x (u - 9) 9 && x (u - 9) 10).toNat + (x (u - 10) 10 && x (u - 10) 11).toNat + (x (u - 11) 11 && x (u - 11) 12).toNat + (x (u - 12) 12 && x (u - 12) 13).toNat + (x (u - 13) 13 && x (u - 13) 14).toNat + (x (u - 14) 14).toNat)
    (hcov2 : ∀ u : ℤ, 1 ≤ (x u 2).toNat + (x (u - 1) 1 && x (u - 1) 3).toNat + (x (u - 2) 2 && x (u - 2) 4).toNat + (x (u - 3) 3 && x (u - 3) 5).toNat + (x (u - 4) 4 && x (u - 4) 6).toNat + (x (u - 5) 5 && x (u - 5) 7).toNat + (x (u - 6) 6 && x (u - 6) 8).toNat + (x (u - 7) 7 && x (u - 7) 9).toNat + (x (u - 8) 8 && x (u - 8) 10).toNat + (x (u - 9) 9 && x (u - 9) 11).toNat + (x (u - 10) 10 && x (u - 10) 12).toNat + (x (u - 11) 11 && x (u - 11) 13).toNat + (x (u - 12) 12 && x (u - 12) 14).toNat + (x (u - 13) 13).toNat)
    (hcov3 : ∀ u : ℤ, 1 ≤ (x u 3).toNat + (x (u - 1) 1 && x (u - 1) 4).toNat + (x (u - 2) 2 && x (u - 2) 5).toNat + (x (u - 3) 3 && x (u - 3) 6).toNat + (x (u - 4) 4 && x (u - 4) 7).toNat + (x (u - 5) 5 && x (u - 5) 8).toNat + (x (u - 6) 6 && x (u - 6) 9).toNat + (x (u - 7) 7 && x (u - 7) 10).toNat + (x (u - 8) 8 && x (u - 8) 11).toNat + (x (u - 9) 9 && x (u - 9) 12).toNat + (x (u - 10) 10 && x (u - 10) 13).toNat + (x (u - 11) 11 && x (u - 11) 14).toNat + (x (u - 12) 12).toNat)
    (hcov4 : ∀ u : ℤ, 1 ≤ (x u 4).toNat + (x (u - 1) 1 && x (u - 1) 5).toNat + (x (u - 2) 2 && x (u - 2) 6).toNat + (x (u - 3) 3 && x (u - 3) 7).toNat + (x (u - 4) 4 && x (u - 4) 8).toNat + (x (u - 5) 5 && x (u - 5) 9).toNat + (x (u - 6) 6 && x (u - 6) 10).toNat + (x (u - 7) 7 && x (u - 7) 11).toNat + (x (u - 8) 8 && x (u - 8) 12).toNat + (x (u - 9) 9 && x (u - 9) 13).toNat + (x (u - 10) 10 && x (u - 10) 14).toNat + (x (u - 11) 11).toNat)
    (hcov5 : ∀ u : ℤ, 1 ≤ (x u 5).toNat + (x (u - 1) 1 && x (u - 1) 6).toNat + (x (u - 2) 2 && x (u - 2) 7).toNat + (x (u - 3) 3 && x (u - 3) 8).toNat + (x (u - 4) 4 && x (u - 4) 9).toNat + (x (u - 5) 5 && x (u - 5) 10).toNat + (x (u - 6) 6 && x (u - 6) 11).toNat + (x (u - 7) 7 && x (u - 7) 12).toNat + (x (u - 8) 8 && x (u - 8) 13).toNat + (x (u - 9) 9 && x (u - 9) 14).toNat + (x (u - 10) 10).toNat)
    (hcov6 : ∀ u : ℤ, 1 ≤ (x u 6).toNat + (x (u - 1) 1 && x (u - 1) 7).toNat + (x (u - 2) 2 && x (u - 2) 8).toNat + (x (u - 3) 3 && x (u - 3) 9).toNat + (x (u - 4) 4 && x (u - 4) 10).toNat + (x (u - 5) 5 && x (u - 5) 11).toNat + (x (u - 6) 6 && x (u - 6) 12).toNat + (x (u - 7) 7 && x (u - 7) 13).toNat + (x (u - 8) 8 && x (u - 8) 14).toNat + (x (u - 9) 9).toNat)
    (hcov7 : ∀ u : ℤ, 1 ≤ (x u 7).toNat + (x (u - 1) 1 && x (u - 1) 8).toNat + (x (u - 2) 2 && x (u - 2) 9).toNat + (x (u - 3) 3 && x (u - 3) 10).toNat + (x (u - 4) 4 && x (u - 4) 11).toNat + (x (u - 5) 5 && x (u - 5) 12).toNat + (x (u - 6) 6 && x (u - 6) 13).toNat + (x (u - 7) 7 && x (u - 7) 14).toNat + (x (u - 8) 8).toNat)
    (hcov9 : ∀ u : ℤ, 1 ≤ (x u 9).toNat + (x (u - 1) 1 && x (u - 1) 10).toNat + (x (u - 2) 2 && x (u - 2) 11).toNat + (x (u - 3) 3 && x (u - 3) 12).toNat + (x (u - 4) 4 && x (u - 4) 13).toNat + (x (u - 5) 5 && x (u - 5) 14).toNat + (x (u - 6) 6).toNat)
    (hcov10 : ∀ u : ℤ, 1 ≤ (x u 10).toNat + (x (u - 1) 1 && x (u - 1) 11).toNat + (x (u - 2) 2 && x (u - 2) 12).toNat + (x (u - 3) 3 && x (u - 3) 13).toNat + (x (u - 4) 4 && x (u - 4) 14).toNat + (x (u - 5) 5).toNat)
    (hcov11 : ∀ u : ℤ, 1 ≤ (x u 11).toNat + (x (u - 1) 1 && x (u - 1) 12).toNat + (x (u - 2) 2 && x (u - 2) 13).toNat + (x (u - 3) 3 && x (u - 3) 14).toNat + (x (u - 4) 4).toNat)
    (hcov13 : ∀ u : ℤ, 1 ≤ (x u 13).toNat + (x (u - 1) 1 && x (u - 1) 14).toNat + (x (u - 2) 2).toNat)
    (hp2 : ∀ p, x p 2 = true → x p 14 = true)
    (hp4 : ∀ p, x p 4 = true → x p 12 = true)
    (hp5 : ∀ p, x p 5 = true → x p 13 = true)
    (hp6 : ∀ p, x p 6 = true → x p 14 = true)
    (hp9 : ∀ p, x p 9 = true → x p 1 = true)
    (hp10 : ∀ p, x p 10 = true → x p 2 = true)
    (hp11 : ∀ p, x p 11 = true → x p 3 = true)
    (hp13 : ∀ p, x p 13 = true → x p 1 = true)
    (h114 : ∀ p, x p 1 = x p 14)
    (h23 : ∀ p, x p 2 = x p 3)
    (g0 : (x 0 4).toNat = 0) (g1 : (x 0 5).toNat = 1) : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d1405 : (x 0 4 && x 0 14).toNat = 0 := by
    have r1406 := hand1 (x 0 4) (x 0 14)
    have b1407 := hb (x 0 4)
    have b1408 := hb (x 0 4 && x 0 14)
    clear * - r1406 b1407 b1408 g0
    omega
  have d1409 : (x 0 4 && x 0 13).toNat = 0 := by
    have r1410 := hand1 (x 0 4) (x 0 13)
    have b1411 := hb (x 0 4)
    have b1412 := hb (x 0 4 && x 0 13)
    clear * - r1410 b1411 b1412 g0
    omega
  have d1413 : (x 0 4 && x 0 10).toNat = 0 := by
    have r1414 := hand1 (x 0 4) (x 0 10)
    have b1415 := hb (x 0 4)
    have b1416 := hb (x 0 4 && x 0 10)
    clear * - r1414 b1415 b1416 g0
    omega
  have d1417 : (x 0 4 && x 0 9).toNat = 0 := by
    have r1418 := hand1 (x 0 4) (x 0 9)
    have b1419 := hb (x 0 4)
    have b1420 := hb (x 0 4 && x 0 9)
    clear * - r1418 b1419 b1420 g0
    omega
  have d1421 : (x 0 13).toNat = 1 := by
    have r1422 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
    have b1423 := hb (x 0 5)
    have b1424 := hb (x 0 13)
    clear * - r1422 b1423 b1424 g1
    omega
  have d1425 : (x 0 1).toNat = 1 := by
    have r1426 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
    have b1427 := hb (x 0 1)
    have b1428 := hb (x 0 13)
    clear * - r1426 b1427 b1428 d1421
    omega
  have d1429 : (x 0 14).toNat = 1 := by
    have r1430 : (x 0 1).toNat = (x 0 14).toNat := congrArg Bool.toNat (h114 0)
    have b1431 := hb (x 0 1)
    have b1432 := hb (x 0 14)
    clear * - r1430 b1431 b1432 d1425
    omega
  have d1433 : (x 1 14).toNat = 0 := by
    have r1434 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1435 := hb (x 0 1)
    have b1436 := hb (x 1 14)
    clear * - r1434 b1435 b1436 d1425
    omega
  have d1437 : (x 1 3 && x 1 14).toNat = 0 := by
    have r1438 := hand2 (x 1 3) (x 1 14)
    have b1439 := hb (x 1 14)
    have b1440 := hb (x 1 3 && x 1 14)
    clear * - r1438 b1439 b1440 d1433
    omega
  have d1441 : (x 1 1).toNat = 0 := by
    have r1442 : (x 1 1).toNat = (x 1 14).toNat := congrArg Bool.toNat (h114 1)
    have b1443 := hb (x 1 1)
    have b1444 := hb (x 1 14)
    clear * - r1442 b1443 b1444 d1433
    omega
  have d1445 : (x 1 1 && x 1 12).toNat = 0 := by
    have r1446 := hand1 (x 1 1) (x 1 12)
    have b1447 := hb (x 1 1)
    have b1448 := hb (x 1 1 && x 1 12)
    clear * - r1446 b1447 b1448 d1441
    omega
  have d1449 : (x 1 13).toNat = 0 := by
    have r1450 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b1451 := hb (x 1 1)
    have b1452 := hb (x 1 13)
    clear * - r1450 b1451 b1452 d1441
    omega
  have d1453 : (x 1 3 && x 1 13).toNat = 0 := by
    have r1454 := hand2 (x 1 3) (x 1 13)
    have b1455 := hb (x 1 13)
    have b1456 := hb (x 1 3 && x 1 13)
    clear * - r1454 b1455 b1456 d1449
    omega
  have d1457 : (x 1 5).toNat = 0 := by
    have r1458 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b1459 := hb (x 1 5)
    have b1460 := hb (x 1 13)
    clear * - r1458 b1459 b1460 d1449
    omega
  have d1461 : (x 1 5 && x 1 12).toNat = 0 := by
    have r1462 := hand1 (x 1 5) (x 1 12)
    have b1463 := hb (x 1 5)
    have b1464 := hb (x 1 5 && x 1 12)
    clear * - r1462 b1463 b1464 d1457
    omega
  have d1465 : (x 1 9).toNat = 0 := by
    have r1466 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
    have b1467 := hb (x 1 1)
    have b1468 := hb (x 1 9)
    clear * - r1466 b1467 b1468 d1441
    omega
  have d1469 : (x 1 3 && x 1 9).toNat = 0 := by
    have r1470 := hand2 (x 1 3) (x 1 9)
    have b1471 := hb (x 1 9)
    have b1472 := hb (x 1 3 && x 1 9)
    clear * - r1470 b1471 b1472 d1465
    omega
  have d1473 : (x 2 14).toNat = 1 := by
    have r1474 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1475 := hb (x 1 1)
    have b1476 := hb (x 2 14)
    clear * - r1474 b1475 b1476 d1441
    omega
  have d1477 : (x 2 1).toNat = 1 := by
    have r1478 : (x 2 1).toNat = (x 2 14).toNat := congrArg Bool.toNat (h114 2)
    have b1479 := hb (x 2 1)
    have b1480 := hb (x 2 14)
    clear * - r1478 b1479 b1480 d1473
    omega
  have d1481 : (x 3 14).toNat = 0 := by
    have r1482 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1483 := hb (x 2 1)
    have b1484 := hb (x 3 14)
    clear * - r1482 b1483 b1484 d1477
    omega
  have d1485 : (x 3 1).toNat = 0 := by
    have r1486 : (x 3 1).toNat = (x 3 14).toNat := congrArg Bool.toNat (h114 3)
    have b1487 := hb (x 3 1)
    have b1488 := hb (x 3 14)
    clear * - r1486 b1487 b1488 d1481
    omega
  have d1489 : (x 3 1 && x 3 12).toNat = 0 := by
    have r1490 := hand1 (x 3 1) (x 3 12)
    have b1491 := hb (x 3 1)
    have b1492 := hb (x 3 1 && x 3 12)
    clear * - r1490 b1491 b1492 d1485
    omega
  have d1493 : (x 3 1 && x 3 11).toNat = 0 := by
    have r1494 := hand1 (x 3 1) (x 3 11)
    have b1495 := hb (x 3 1)
    have b1496 := hb (x 3 1 && x 3 11)
    clear * - r1494 b1495 b1496 d1485
    omega
  have d1497 : (x 3 1 && x 3 10).toNat = 0 := by
    have r1498 := hand1 (x 3 1) (x 3 10)
    have b1499 := hb (x 3 1)
    have b1500 := hb (x 3 1 && x 3 10)
    clear * - r1498 b1499 b1500 d1485
    omega
  have d1501 : (x 3 1 && x 3 7).toNat = 0 := by
    have r1502 := hand1 (x 3 1) (x 3 7)
    have b1503 := hb (x 3 1)
    have b1504 := hb (x 3 1 && x 3 7)
    clear * - r1502 b1503 b1504 d1485
    omega
  have d1505 : (x 3 1 && x 3 6).toNat = 0 := by
    have r1506 := hand1 (x 3 1) (x 3 6)
    have b1507 := hb (x 3 1)
    have b1508 := hb (x 3 1 && x 3 6)
    clear * - r1506 b1507 b1508 d1485
    omega
  have d1509 : (x 3 13).toNat = 0 := by
    have r1510 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b1511 := hb (x 3 1)
    have b1512 := hb (x 3 13)
    clear * - r1510 b1511 b1512 d1485
    omega
  have d1513 : (x 3 5).toNat = 0 := by
    have r1514 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
    have b1515 := hb (x 3 5)
    have b1516 := hb (x 3 13)
    clear * - r1514 b1515 b1516 d1509
    omega
  have d1517 : (x 3 5 && x 3 10).toNat = 0 := by
    have r1518 := hand1 (x 3 5) (x 3 10)
    have b1519 := hb (x 3 5)
    have b1520 := hb (x 3 5 && x 3 10)
    clear * - r1518 b1519 b1520 d1513
    omega
  have d1521 : (x 3 9).toNat = 0 := by
    have r1522 : (x 3 9).toNat ≤ (x 3 1).toNat := himp _ _ (hp9 3)
    have b1523 := hb (x 3 1)
    have b1524 := hb (x 3 9)
    clear * - r1522 b1523 b1524 d1485
    omega
  have d1525 : (x 4 14).toNat = 1 := by
    have r1526 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1527 := hb (x 3 1)
    have b1528 := hb (x 4 14)
    clear * - r1526 b1527 b1528 d1485
    omega
  have d1529 : (x 4 1).toNat = 1 := by
    have r1530 : (x 4 1).toNat = (x 4 14).toNat := congrArg Bool.toNat (h114 4)
    have b1531 := hb (x 4 1)
    have b1532 := hb (x 4 14)
    clear * - r1530 b1531 b1532 d1525
    omega
  have d1533 : (x 5 14).toNat = 0 := by
    have r1534 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1535 := hb (x 4 1)
    have b1536 := hb (x 5 14)
    clear * - r1534 b1535 b1536 d1529
    omega
  have d1537 : (x 5 1).toNat = 0 := by
    have r1538 : (x 5 1).toNat = (x 5 14).toNat := congrArg Bool.toNat (h114 5)
    have b1539 := hb (x 5 1)
    have b1540 := hb (x 5 14)
    clear * - r1538 b1539 b1540 d1533
    omega
  have d1541 : (x 5 1 && x 5 8).toNat = 0 := by
    have r1542 := hand1 (x 5 1) (x 5 8)
    have b1543 := hb (x 5 1)
    have b1544 := hb (x 5 1 && x 5 8)
    clear * - r1542 b1543 b1544 d1537
    omega
  have d1545 : (x 5 13).toNat = 0 := by
    have r1546 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
    have b1547 := hb (x 5 1)
    have b1548 := hb (x 5 13)
    clear * - r1546 b1547 b1548 d1537
    omega
  have d1549 : (x 5 3 && x 5 13).toNat = 0 := by
    have r1550 := hand2 (x 5 3) (x 5 13)
    have b1551 := hb (x 5 13)
    have b1552 := hb (x 5 3 && x 5 13)
    clear * - r1550 b1551 b1552 d1545
    omega
  have d1553 : (x 5 5).toNat = 0 := by
    have r1554 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
    have b1555 := hb (x 5 5)
    have b1556 := hb (x 5 13)
    clear * - r1554 b1555 b1556 d1545
    omega
  have d1557 : (x 5 9).toNat = 0 := by
    have r1558 : (x 5 9).toNat ≤ (x 5 1).toNat := himp _ _ (hp9 5)
    have b1559 := hb (x 5 1)
    have b1560 := hb (x 5 9)
    clear * - r1558 b1559 b1560 d1537
    omega
  have d1561 : (x 6 14).toNat = 1 := by
    have r1562 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1563 := hb (x 5 1)
    have b1564 := hb (x 6 14)
    clear * - r1562 b1563 b1564 d1537
    omega
  have d1565 : (x 6 1).toNat = 1 := by
    have r1566 : (x 6 1).toNat = (x 6 14).toNat := congrArg Bool.toNat (h114 6)
    have b1567 := hb (x 6 1)
    have b1568 := hb (x 6 14)
    clear * - r1566 b1567 b1568 d1561
    omega
  have d1569 : (x 7 14).toNat = 0 := by
    have r1570 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1571 := hb (x 6 1)
    have b1572 := hb (x 7 14)
    clear * - r1570 b1571 b1572 d1565
    omega
  have d1573 : (x 7 3 && x 7 14).toNat = 0 := by
    have r1574 := hand2 (x 7 3) (x 7 14)
    have b1575 := hb (x 7 14)
    have b1576 := hb (x 7 3 && x 7 14)
    clear * - r1574 b1575 b1576 d1569
    omega
  have d1577 : (x 7 1).toNat = 0 := by
    have r1578 : (x 7 1).toNat = (x 7 14).toNat := congrArg Bool.toNat (h114 7)
    have b1579 := hb (x 7 1)
    have b1580 := hb (x 7 14)
    clear * - r1578 b1579 b1580 d1569
    omega
  have d1581 : (x 7 1 && x 7 11).toNat = 0 := by
    have r1582 := hand1 (x 7 1) (x 7 11)
    have b1583 := hb (x 7 1)
    have b1584 := hb (x 7 1 && x 7 11)
    clear * - r1582 b1583 b1584 d1577
    omega
  have d1585 : (x 7 1 && x 7 6).toNat = 0 := by
    have r1586 := hand1 (x 7 1) (x 7 6)
    have b1587 := hb (x 7 1)
    have b1588 := hb (x 7 1 && x 7 6)
    clear * - r1586 b1587 b1588 d1577
    omega
  have d1589 : (x 8 14).toNat = 1 := by
    have r1590 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1591 := hb (x 7 1)
    have b1592 := hb (x 8 14)
    clear * - r1590 b1591 b1592 d1577
    omega
  have d1593 : (x 8 1).toNat = 1 := by
    have r1594 : (x 8 1).toNat = (x 8 14).toNat := congrArg Bool.toNat (h114 8)
    have b1595 := hb (x 8 1)
    have b1596 := hb (x 8 14)
    clear * - r1594 b1595 b1596 d1589
    omega
  have d1597 : (x 9 14).toNat = 0 := by
    have r1598 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1599 := hb (x 8 1)
    have b1600 := hb (x 9 14)
    clear * - r1598 b1599 b1600 d1593
    omega
  have d1601 : (x 9 1).toNat = 0 := by
    have r1602 : (x 9 1).toNat = (x 9 14).toNat := congrArg Bool.toNat (h114 9)
    have b1603 := hb (x 9 1)
    have b1604 := hb (x 9 14)
    clear * - r1602 b1603 b1604 d1597
    omega
  have d1605 : (x 9 1 && x 9 12).toNat = 0 := by
    have r1606 := hand1 (x 9 1) (x 9 12)
    have b1607 := hb (x 9 1)
    have b1608 := hb (x 9 1 && x 9 12)
    clear * - r1606 b1607 b1608 d1601
    omega
  have d1609 : (x 7 6).toNat = 0 := by
    have r1610 : (x 7 6).toNat ≤ (x 7 14).toNat := himp _ _ (hp6 7)
    have b1611 := hb (x 7 6)
    have b1612 := hb (x 7 14)
    clear * - r1610 b1611 b1612 d1569
    omega
  have d1613 : (x 7 2 && x 7 6).toNat = 0 := by
    have r1614 := hand2 (x 7 2) (x 7 6)
    have b1615 := hb (x 7 6)
    have b1616 := hb (x 7 2 && x 7 6)
    clear * - r1614 b1615 b1616 d1609
    omega
  have d1617 : (x 7 2).toNat = 0 := by
    have r1618 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b1619 := hb (x 7 2)
    have b1620 := hb (x 7 14)
    clear * - r1618 b1619 b1620 d1569
    omega
  have d1621 : (x 7 3).toNat = 0 := by
    have r1622 : (x 7 2).toNat = (x 7 3).toNat := congrArg Bool.toNat (h23 7)
    have b1623 := hb (x 7 2)
    have b1624 := hb (x 7 3)
    clear * - r1622 b1623 b1624 d1617
    omega
  have d1625 : (x 5 2).toNat = 0 := by
    have r1626 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b1627 := hb (x 5 2)
    have b1628 := hb (x 5 14)
    clear * - r1626 b1627 b1628 d1533
    omega
  have d1629 : (x 5 3).toNat = 0 := by
    have r1630 : (x 5 2).toNat = (x 5 3).toNat := congrArg Bool.toNat (h23 5)
    have b1631 := hb (x 5 2)
    have b1632 := hb (x 5 3)
    clear * - r1630 b1631 b1632 d1625
    omega
  have d1633 : (x 5 3 && x 5 8).toNat = 0 := by
    have r1634 := hand1 (x 5 3) (x 5 8)
    have b1635 := hb (x 5 3)
    have b1636 := hb (x 5 3 && x 5 8)
    clear * - r1634 b1635 b1636 d1629
    omega
  have d1637 : (x 3 6).toNat = 0 := by
    have r1638 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
    have b1639 := hb (x 3 6)
    have b1640 := hb (x 3 14)
    clear * - r1638 b1639 b1640 d1481
    omega
  have d1641 : (x 3 6 && x 3 10).toNat = 0 := by
    have r1642 := hand1 (x 3 6) (x 3 10)
    have b1643 := hb (x 3 6)
    have b1644 := hb (x 3 6 && x 3 10)
    clear * - r1642 b1643 b1644 d1637
    omega
  have d1645 : (x 3 2 && x 3 6).toNat = 0 := by
    have r1646 := hand2 (x 3 2) (x 3 6)
    have b1647 := hb (x 3 6)
    have b1648 := hb (x 3 2 && x 3 6)
    clear * - r1646 b1647 b1648 d1637
    omega
  have d1649 : (x 3 2).toNat = 0 := by
    have r1650 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b1651 := hb (x 3 2)
    have b1652 := hb (x 3 14)
    clear * - r1650 b1651 b1652 d1481
    omega
  have d1653 : (x 3 3).toNat = 0 := by
    have r1654 : (x 3 2).toNat = (x 3 3).toNat := congrArg Bool.toNat (h23 3)
    have b1655 := hb (x 3 2)
    have b1656 := hb (x 3 3)
    clear * - r1654 b1655 b1656 d1649
    omega
  have d1657 : (x 3 3 && x 3 10).toNat = 0 := by
    have r1658 := hand1 (x 3 3) (x 3 10)
    have b1659 := hb (x 3 3)
    have b1660 := hb (x 3 3 && x 3 10)
    clear * - r1658 b1659 b1660 d1653
    omega
  have d1661 : (x 3 11).toNat = 0 := by
    have r1662 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b1663 := hb (x 3 3)
    have b1664 := hb (x 3 11)
    clear * - r1662 b1663 b1664 d1653
    omega
  have d1665 : (x 3 10).toNat = 0 := by
    have r1666 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
    have b1667 := hb (x 3 2)
    have b1668 := hb (x 3 10)
    clear * - r1666 b1667 b1668 d1649
    omega
  have d1669 : (x 1 2).toNat = 0 := by
    have r1670 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
    have b1671 := hb (x 1 2)
    have b1672 := hb (x 1 14)
    clear * - r1670 b1671 b1672 d1433
    omega
  have d1673 : (x 1 2 && x 1 12).toNat = 0 := by
    have r1674 := hand1 (x 1 2) (x 1 12)
    have b1675 := hb (x 1 2)
    have b1676 := hb (x 1 2 && x 1 12)
    clear * - r1674 b1675 b1676 d1669
    omega
  have d1677 : (x 1 2 && x 1 8).toNat = 0 := by
    have r1678 := hand1 (x 1 2) (x 1 8)
    have b1679 := hb (x 1 2)
    have b1680 := hb (x 1 2 && x 1 8)
    clear * - r1678 b1679 b1680 d1669
    omega
  have d1681 : (x 1 3).toNat = 0 := by
    have r1682 : (x 1 2).toNat = (x 1 3).toNat := congrArg Bool.toNat (h23 1)
    have b1683 := hb (x 1 2)
    have b1684 := hb (x 1 3)
    clear * - r1682 b1683 b1684 d1669
    omega
  have d1685 : (x 1 3 && x 1 12).toNat = 0 := by
    have r1686 := hand1 (x 1 3) (x 1 12)
    have b1687 := hb (x 1 3)
    have b1688 := hb (x 1 3 && x 1 12)
    clear * - r1686 b1687 b1688 d1681
    omega
  have d1689 : (x 1 3 && x 1 8).toNat = 0 := by
    have r1690 := hand1 (x 1 3) (x 1 8)
    have b1691 := hb (x 1 3)
    have b1692 := hb (x 1 3 && x 1 8)
    clear * - r1690 b1691 b1692 d1681
    omega
  have d1693 : (x 1 11).toNat = 0 := by
    have r1694 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b1695 := hb (x 1 3)
    have b1696 := hb (x 1 11)
    clear * - r1694 b1695 b1696 d1681
    omega
  have d1697 : (x (-1) 1).toNat = 0 := by
    have r1698 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1699 := hb (x (-1) 1)
    have b1700 := hb (x 0 14)
    clear * - r1698 b1699 b1700 d1429
    omega
  have d1701 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
    have r1702 := hand1 (x (-1) 1) (x (-1) 11)
    have b1703 := hb (x (-1) 1)
    have b1704 := hb (x (-1) 1 && x (-1) 11)
    clear * - r1702 b1703 b1704 d1697
    omega
  have d1705 : (x (-1) 14).toNat = 0 := by
    have r1706 : (x (-1) 1).toNat = (x (-1) 14).toNat := congrArg Bool.toNat (h114 (-1))
    have b1707 := hb (x (-1) 1)
    have b1708 := hb (x (-1) 14)
    clear * - r1706 b1707 b1708 d1697
    omega
  have d1709 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
    have r1710 := hand2 (x (-1) 3) (x (-1) 14)
    have b1711 := hb (x (-1) 14)
    have b1712 := hb (x (-1) 3 && x (-1) 14)
    clear * - r1710 b1711 b1712 d1705
    omega
  have d1713 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
    have r1714 := hand2 (x (-1) 4) (x (-1) 14)
    have b1715 := hb (x (-1) 14)
    have b1716 := hb (x (-1) 4 && x (-1) 14)
    clear * - r1714 b1715 b1716 d1705
    omega
  have d1717 : (x (-1) 5 && x (-1) 14).toNat = 0 := by
    have r1718 := hand2 (x (-1) 5) (x (-1) 14)
    have b1719 := hb (x (-1) 14)
    have b1720 := hb (x (-1) 5 && x (-1) 14)
    clear * - r1718 b1719 b1720 d1705
    omega
  have d1721 : (x (-1) 7 && x (-1) 14).toNat = 0 := by
    have r1722 := hand2 (x (-1) 7) (x (-1) 14)
    have b1723 := hb (x (-1) 14)
    have b1724 := hb (x (-1) 7 && x (-1) 14)
    clear * - r1722 b1723 b1724 d1705
    omega
  have d1725 : (x (-1) 9 && x (-1) 14).toNat = 0 := by
    have r1726 := hand2 (x (-1) 9) (x (-1) 14)
    have b1727 := hb (x (-1) 14)
    have b1728 := hb (x (-1) 9 && x (-1) 14)
    clear * - r1726 b1727 b1728 d1705
    omega
  have d1729 : (x (-1) 6).toNat = 0 := by
    have r1730 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
    have b1731 := hb (x (-1) 6)
    have b1732 := hb (x (-1) 14)
    clear * - r1730 b1731 b1732 d1705
    omega
  have d1733 : (x (-1) 6 && x (-1) 10).toNat = 0 := by
    have r1734 := hand1 (x (-1) 6) (x (-1) 10)
    have b1735 := hb (x (-1) 6)
    have b1736 := hb (x (-1) 6 && x (-1) 10)
    clear * - r1734 b1735 b1736 d1729
    omega
  have d1737 : (x (-1) 2).toNat = 0 := by
    have r1738 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have b1739 := hb (x (-1) 2)
    have b1740 := hb (x (-1) 14)
    clear * - r1738 b1739 b1740 d1705
    omega
  have d1741 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
    have r1742 := hand1 (x (-1) 2) (x (-1) 11)
    have b1743 := hb (x (-1) 2)
    have b1744 := hb (x (-1) 2 && x (-1) 11)
    clear * - r1742 b1743 b1744 d1737
    omega
  have d1745 : (x (-1) 3).toNat = 0 := by
    have r1746 : (x (-1) 2).toNat = (x (-1) 3).toNat := congrArg Bool.toNat (h23 (-1))
    have b1747 := hb (x (-1) 2)
    have b1748 := hb (x (-1) 3)
    clear * - r1746 b1747 b1748 d1737
    omega
  have d1749 : (x (-1) 3 && x (-1) 7).toNat = 0 := by
    have r1750 := hand1 (x (-1) 3) (x (-1) 7)
    have b1751 := hb (x (-1) 3)
    have b1752 := hb (x (-1) 3 && x (-1) 7)
    clear * - r1750 b1751 b1752 d1745
    omega
  have d1753 : (x (-1) 11).toNat = 0 := by
    have r1754 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b1755 := hb (x (-1) 3)
    have b1756 := hb (x (-1) 11)
    clear * - r1754 b1755 b1756 d1745
    omega
  have d1757 : (x (-1) 5 && x (-1) 11).toNat = 0 := by
    have r1758 := hand2 (x (-1) 5) (x (-1) 11)
    have b1759 := hb (x (-1) 11)
    have b1760 := hb (x (-1) 5 && x (-1) 11)
    clear * - r1758 b1759 b1760 d1753
    omega
  have d1761 : (x (-1) 10).toNat = 0 := by
    have r1762 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
    have b1763 := hb (x (-1) 2)
    have b1764 := hb (x (-1) 10)
    clear * - r1762 b1763 b1764 d1737
    omega
  have d1765 : (x (-1) 4 && x (-1) 10).toNat = 0 := by
    have r1766 := hand2 (x (-1) 4) (x (-1) 10)
    have b1767 := hb (x (-1) 10)
    have b1768 := hb (x (-1) 4 && x (-1) 10)
    clear * - r1766 b1767 b1768 d1761
    omega
  have d1769 : (x (-1) 5 && x (-1) 10).toNat = 0 := by
    have r1770 := hand2 (x (-1) 5) (x (-1) 10)
    have b1771 := hb (x (-1) 10)
    have b1772 := hb (x (-1) 5 && x (-1) 10)
    clear * - r1770 b1771 b1772 d1761
    omega
  have d1773 : (x (-1) 13).toNat = 0 := by
    have r1774 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b1775 := hb (x (-1) 1)
    have b1776 := hb (x (-1) 13)
    clear * - r1774 b1775 b1776 d1697
    omega
  have d1777 : (x (-1) 5).toNat = 0 := by
    have r1778 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b1779 := hb (x (-1) 5)
    have b1780 := hb (x (-1) 13)
    clear * - r1778 b1779 b1780 d1773
    omega
  have d1781 : (x (-1) 9).toNat = 0 := by
    have r1782 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
    have b1783 := hb (x (-1) 1)
    have b1784 := hb (x (-1) 9)
    clear * - r1782 b1783 b1784 d1697
    omega
  have d1785 : (x (-2) 1).toNat = 1 := by
    have r1786 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1787 := hb (x (-2) 1)
    have b1788 := hb (x (-1) 14)
    clear * - r1786 b1787 b1788 d1705
    omega
  have d1789 : (x (-2) 14).toNat = 1 := by
    have r1790 : (x (-2) 1).toNat = (x (-2) 14).toNat := congrArg Bool.toNat (h114 (-2))
    have b1791 := hb (x (-2) 1)
    have b1792 := hb (x (-2) 14)
    clear * - r1790 b1791 b1792 d1785
    omega
  have d1793 : (x (-3) 1).toNat = 0 := by
    have r1794 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1795 := hb (x (-3) 1)
    have b1796 := hb (x (-2) 14)
    clear * - r1794 b1795 b1796 d1789
    omega
  have d1797 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
    have r1798 := hand1 (x (-3) 1) (x (-3) 12)
    have b1799 := hb (x (-3) 1)
    have b1800 := hb (x (-3) 1 && x (-3) 12)
    clear * - r1798 b1799 b1800 d1793
    omega
  have d1801 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
    have r1802 := hand1 (x (-3) 1) (x (-3) 11)
    have b1803 := hb (x (-3) 1)
    have b1804 := hb (x (-3) 1 && x (-3) 11)
    clear * - r1802 b1803 b1804 d1793
    omega
  have d1805 : (x (-3) 14).toNat = 0 := by
    have r1806 : (x (-3) 1).toNat = (x (-3) 14).toNat := congrArg Bool.toNat (h114 (-3))
    have b1807 := hb (x (-3) 1)
    have b1808 := hb (x (-3) 14)
    clear * - r1806 b1807 b1808 d1793
    omega
  have d1809 : (x (-3) 6).toNat = 0 := by
    have r1810 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
    have b1811 := hb (x (-3) 6)
    have b1812 := hb (x (-3) 14)
    clear * - r1810 b1811 b1812 d1805
    omega
  have d1813 : (x (-3) 6 && x (-3) 12).toNat = 0 := by
    have r1814 := hand1 (x (-3) 6) (x (-3) 12)
    have b1815 := hb (x (-3) 6)
    have b1816 := hb (x (-3) 6 && x (-3) 12)
    clear * - r1814 b1815 b1816 d1809
    omega
  have d1817 : (x (-3) 2).toNat = 0 := by
    have r1818 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b1819 := hb (x (-3) 2)
    have b1820 := hb (x (-3) 14)
    clear * - r1818 b1819 b1820 d1805
    omega
  have d1821 : (x (-3) 3).toNat = 0 := by
    have r1822 : (x (-3) 2).toNat = (x (-3) 3).toNat := congrArg Bool.toNat (h23 (-3))
    have b1823 := hb (x (-3) 2)
    have b1824 := hb (x (-3) 3)
    clear * - r1822 b1823 b1824 d1817
    omega
  have d1825 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
    have r1826 := hand1 (x (-3) 3) (x (-3) 13)
    have b1827 := hb (x (-3) 3)
    have b1828 := hb (x (-3) 3 && x (-3) 13)
    clear * - r1826 b1827 b1828 d1821
    omega
  have d1829 : (x (-3) 3 && x (-3) 7).toNat = 0 := by
    have r1830 := hand1 (x (-3) 3) (x (-3) 7)
    have b1831 := hb (x (-3) 3)
    have b1832 := hb (x (-3) 3 && x (-3) 7)
    clear * - r1830 b1831 b1832 d1821
    omega
  have d1833 : (x (-3) 11).toNat = 0 := by
    have r1834 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b1835 := hb (x (-3) 3)
    have b1836 := hb (x (-3) 11)
    clear * - r1834 b1835 b1836 d1821
    omega
  have d1837 : (x (-3) 13).toNat = 0 := by
    have r1838 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b1839 := hb (x (-3) 1)
    have b1840 := hb (x (-3) 13)
    clear * - r1838 b1839 b1840 d1793
    omega
  have d1841 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
    have r1842 := hand2 (x (-3) 4) (x (-3) 13)
    have b1843 := hb (x (-3) 13)
    have b1844 := hb (x (-3) 4 && x (-3) 13)
    clear * - r1842 b1843 b1844 d1837
    omega
  have d1845 : (x (-3) 7 && x (-3) 13).toNat = 0 := by
    have r1846 := hand2 (x (-3) 7) (x (-3) 13)
    have b1847 := hb (x (-3) 13)
    have b1848 := hb (x (-3) 7 && x (-3) 13)
    clear * - r1846 b1847 b1848 d1837
    omega
  have d1849 : (x (-3) 5).toNat = 0 := by
    have r1850 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
    have b1851 := hb (x (-3) 5)
    have b1852 := hb (x (-3) 13)
    clear * - r1850 b1851 b1852 d1837
    omega
  have d1853 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
    have r1854 := hand1 (x (-3) 5) (x (-3) 9)
    have b1855 := hb (x (-3) 5)
    have b1856 := hb (x (-3) 5 && x (-3) 9)
    clear * - r1854 b1855 b1856 d1849
    omega
  have d1857 : (x (-3) 9).toNat = 0 := by
    have r1858 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
    have b1859 := hb (x (-3) 1)
    have b1860 := hb (x (-3) 9)
    clear * - r1858 b1859 b1860 d1793
    omega
  have d1861 : (x (-4) 1).toNat = 1 := by
    have r1862 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1863 := hb (x (-4) 1)
    have b1864 := hb (x (-3) 14)
    clear * - r1862 b1863 b1864 d1805
    omega
  have d1865 : (x (-4) 14).toNat = 1 := by
    have r1866 : (x (-4) 1).toNat = (x (-4) 14).toNat := congrArg Bool.toNat (h114 (-4))
    have b1867 := hb (x (-4) 1)
    have b1868 := hb (x (-4) 14)
    clear * - r1866 b1867 b1868 d1861
    omega
  have d1869 : (x (-5) 1).toNat = 0 := by
    have r1870 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1871 := hb (x (-5) 1)
    have b1872 := hb (x (-4) 14)
    clear * - r1870 b1871 b1872 d1865
    omega
  have d1873 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
    have r1874 := hand1 (x (-5) 1) (x (-5) 14)
    have b1875 := hb (x (-5) 1)
    have b1876 := hb (x (-5) 1 && x (-5) 14)
    clear * - r1874 b1875 b1876 d1869
    omega
  have d1877 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
    have r1878 := hand1 (x (-5) 1) (x (-5) 11)
    have b1879 := hb (x (-5) 1)
    have b1880 := hb (x (-5) 1 && x (-5) 11)
    clear * - r1878 b1879 b1880 d1869
    omega
  have d1881 : (x (-5) 14).toNat = 0 := by
    have r1882 : (x (-5) 1).toNat = (x (-5) 14).toNat := congrArg Bool.toNat (h114 (-5))
    have b1883 := hb (x (-5) 1)
    have b1884 := hb (x (-5) 14)
    clear * - r1882 b1883 b1884 d1869
    omega
  have d1885 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
    have r1886 := hand2 (x (-5) 3) (x (-5) 14)
    have b1887 := hb (x (-5) 14)
    have b1888 := hb (x (-5) 3 && x (-5) 14)
    clear * - r1886 b1887 b1888 d1881
    omega
  have d1889 : (x (-5) 8 && x (-5) 14).toNat = 0 := by
    have r1890 := hand2 (x (-5) 8) (x (-5) 14)
    have b1891 := hb (x (-5) 14)
    have b1892 := hb (x (-5) 8 && x (-5) 14)
    clear * - r1890 b1891 b1892 d1881
    omega
  have d1893 : (x (-5) 9 && x (-5) 14).toNat = 0 := by
    have r1894 := hand2 (x (-5) 9) (x (-5) 14)
    have b1895 := hb (x (-5) 14)
    have b1896 := hb (x (-5) 9 && x (-5) 14)
    clear * - r1894 b1895 b1896 d1881
    omega
  have d1897 : (x (-5) 6).toNat = 0 := by
    have r1898 : (x (-5) 6).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp6 (-5))
    have b1899 := hb (x (-5) 6)
    have b1900 := hb (x (-5) 14)
    clear * - r1898 b1899 b1900 d1881
    omega
  have d1901 : (x (-5) 2).toNat = 0 := by
    have r1902 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
    have b1903 := hb (x (-5) 2)
    have b1904 := hb (x (-5) 14)
    clear * - r1902 b1903 b1904 d1881
    omega
  have d1905 : (x (-5) 3).toNat = 0 := by
    have r1906 : (x (-5) 2).toNat = (x (-5) 3).toNat := congrArg Bool.toNat (h23 (-5))
    have b1907 := hb (x (-5) 2)
    have b1908 := hb (x (-5) 3)
    clear * - r1906 b1907 b1908 d1901
    omega
  have d1909 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
    have r1910 := hand1 (x (-5) 3) (x (-5) 13)
    have b1911 := hb (x (-5) 3)
    have b1912 := hb (x (-5) 3 && x (-5) 13)
    clear * - r1910 b1911 b1912 d1905
    omega
  have d1913 : (x (-5) 11).toNat = 0 := by
    have r1914 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
    have b1915 := hb (x (-5) 3)
    have b1916 := hb (x (-5) 11)
    clear * - r1914 b1915 b1916 d1905
    omega
  have d1917 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
    have r1918 := hand2 (x (-5) 7) (x (-5) 11)
    have b1919 := hb (x (-5) 11)
    have b1920 := hb (x (-5) 7 && x (-5) 11)
    clear * - r1918 b1919 b1920 d1913
    omega
  have d1921 : (x (-5) 10).toNat = 0 := by
    have r1922 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
    have b1923 := hb (x (-5) 2)
    have b1924 := hb (x (-5) 10)
    clear * - r1922 b1923 b1924 d1901
    omega
  have d1925 : (x (-5) 13).toNat = 0 := by
    have r1926 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
    have b1927 := hb (x (-5) 1)
    have b1928 := hb (x (-5) 13)
    clear * - r1926 b1927 b1928 d1869
    omega
  have d1929 : (x (-5) 5).toNat = 0 := by
    have r1930 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b1931 := hb (x (-5) 5)
    have b1932 := hb (x (-5) 13)
    clear * - r1930 b1931 b1932 d1925
    omega
  have d1933 : (x (-5) 5 && x (-5) 9).toNat = 0 := by
    have r1934 := hand1 (x (-5) 5) (x (-5) 9)
    have b1935 := hb (x (-5) 5)
    have b1936 := hb (x (-5) 5 && x (-5) 9)
    clear * - r1934 b1935 b1936 d1929
    omega
  have d1937 : (x (-5) 9).toNat = 0 := by
    have r1938 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
    have b1939 := hb (x (-5) 1)
    have b1940 := hb (x (-5) 9)
    clear * - r1938 b1939 b1940 d1869
    omega
  have d1941 : (x (-6) 1).toNat = 1 := by
    have r1942 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1943 := hb (x (-6) 1)
    have b1944 := hb (x (-5) 14)
    clear * - r1942 b1943 b1944 d1881
    omega
  have d1945 : (x (-6) 14).toNat = 1 := by
    have r1946 : (x (-6) 1).toNat = (x (-6) 14).toNat := congrArg Bool.toNat (h114 (-6))
    have b1947 := hb (x (-6) 1)
    have b1948 := hb (x (-6) 14)
    clear * - r1946 b1947 b1948 d1941
    omega
  have d1949 : (x (-7) 1).toNat = 0 := by
    have r1950 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1951 := hb (x (-7) 1)
    have b1952 := hb (x (-6) 14)
    clear * - r1950 b1951 b1952 d1945
    omega
  have d1953 : (x (-7) 1 && x (-7) 11).toNat = 0 := by
    have r1954 := hand1 (x (-7) 1) (x (-7) 11)
    have b1955 := hb (x (-7) 1)
    have b1956 := hb (x (-7) 1 && x (-7) 11)
    clear * - r1954 b1955 b1956 d1949
    omega
  have d1957 : (x (-7) 14).toNat = 0 := by
    have r1958 : (x (-7) 1).toNat = (x (-7) 14).toNat := congrArg Bool.toNat (h114 (-7))
    have b1959 := hb (x (-7) 1)
    have b1960 := hb (x (-7) 14)
    clear * - r1958 b1959 b1960 d1949
    omega
  have d1961 : (x (-7) 2).toNat = 0 := by
    have r1962 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
    have b1963 := hb (x (-7) 2)
    have b1964 := hb (x (-7) 14)
    clear * - r1962 b1963 b1964 d1957
    omega
  have d1965 : (x (-7) 2 && x (-7) 12).toNat = 0 := by
    have r1966 := hand1 (x (-7) 2) (x (-7) 12)
    have b1967 := hb (x (-7) 2)
    have b1968 := hb (x (-7) 2 && x (-7) 12)
    clear * - r1966 b1967 b1968 d1961
    omega
  have d1969 : (x (-7) 3).toNat = 0 := by
    have r1970 : (x (-7) 2).toNat = (x (-7) 3).toNat := congrArg Bool.toNat (h23 (-7))
    have b1971 := hb (x (-7) 2)
    have b1972 := hb (x (-7) 3)
    clear * - r1970 b1971 b1972 d1961
    omega
  have d1973 : (x (-7) 3 && x (-7) 13).toNat = 0 := by
    have r1974 := hand1 (x (-7) 3) (x (-7) 13)
    have b1975 := hb (x (-7) 3)
    have b1976 := hb (x (-7) 3 && x (-7) 13)
    clear * - r1974 b1975 b1976 d1969
    omega
  have d1977 : (x (-7) 11).toNat = 0 := by
    have r1978 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have b1979 := hb (x (-7) 3)
    have b1980 := hb (x (-7) 11)
    clear * - r1978 b1979 b1980 d1969
    omega
  have d1981 : (x (-7) 7 && x (-7) 11).toNat = 0 := by
    have r1982 := hand2 (x (-7) 7) (x (-7) 11)
    have b1983 := hb (x (-7) 11)
    have b1984 := hb (x (-7) 7 && x (-7) 11)
    clear * - r1982 b1983 b1984 d1977
    omega
  have d1985 : (x (-7) 10).toNat = 0 := by
    have r1986 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
    have b1987 := hb (x (-7) 2)
    have b1988 := hb (x (-7) 10)
    clear * - r1986 b1987 b1988 d1961
    omega
  have d1989 : (x (-7) 13).toNat = 0 := by
    have r1990 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
    have b1991 := hb (x (-7) 1)
    have b1992 := hb (x (-7) 13)
    clear * - r1990 b1991 b1992 d1949
    omega
  have d1993 : (x (-7) 9 && x (-7) 13).toNat = 0 := by
    have r1994 := hand2 (x (-7) 9) (x (-7) 13)
    have b1995 := hb (x (-7) 13)
    have b1996 := hb (x (-7) 9 && x (-7) 13)
    clear * - r1994 b1995 b1996 d1989
    omega
  have d1997 : (x (-7) 5).toNat = 0 := by
    have r1998 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
    have b1999 := hb (x (-7) 5)
    have b2000 := hb (x (-7) 13)
    clear * - r1998 b1999 b2000 d1989
    omega
  have d2001 : (x (-7) 9).toNat = 0 := by
    have r2002 : (x (-7) 9).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp9 (-7))
    have b2003 := hb (x (-7) 1)
    have b2004 := hb (x (-7) 9)
    clear * - r2002 b2003 b2004 d1949
    omega
  have d2005 : (x (-8) 1).toNat = 1 := by
    have r2006 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2007 := hb (x (-8) 1)
    have b2008 := hb (x (-7) 14)
    clear * - r2006 b2007 b2008 d1957
    omega
  have d2009 : (x (-8) 14).toNat = 1 := by
    have r2010 : (x (-8) 1).toNat = (x (-8) 14).toNat := congrArg Bool.toNat (h114 (-8))
    have b2011 := hb (x (-8) 1)
    have b2012 := hb (x (-8) 14)
    clear * - r2010 b2011 b2012 d2005
    omega
  have d2013 : (x (-9) 1).toNat = 0 := by
    have r2014 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2015 := hb (x (-9) 1)
    have b2016 := hb (x (-8) 14)
    clear * - r2014 b2015 b2016 d2009
    omega
  have d2017 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
    have r2018 := hand1 (x (-9) 1) (x (-9) 12)
    have b2019 := hb (x (-9) 1)
    have b2020 := hb (x (-9) 1 && x (-9) 12)
    clear * - r2018 b2019 b2020 d2013
    omega
  have d2021 : (x (-9) 14).toNat = 0 := by
    have r2022 : (x (-9) 1).toNat = (x (-9) 14).toNat := congrArg Bool.toNat (h114 (-9))
    have b2023 := hb (x (-9) 1)
    have b2024 := hb (x (-9) 14)
    clear * - r2022 b2023 b2024 d2013
    omega
  have d2025 : (x (-9) 4 && x (-9) 14).toNat = 0 := by
    have r2026 := hand2 (x (-9) 4) (x (-9) 14)
    have b2027 := hb (x (-9) 14)
    have b2028 := hb (x (-9) 4 && x (-9) 14)
    clear * - r2026 b2027 b2028 d2021
    omega
  have d2029 : (x (-9) 2).toNat = 0 := by
    have r2030 : (x (-9) 2).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp2 (-9))
    have b2031 := hb (x (-9) 2)
    have b2032 := hb (x (-9) 14)
    clear * - r2030 b2031 b2032 d2021
    omega
  have d2033 : (x (-9) 3).toNat = 0 := by
    have r2034 : (x (-9) 2).toNat = (x (-9) 3).toNat := congrArg Bool.toNat (h23 (-9))
    have b2035 := hb (x (-9) 2)
    have b2036 := hb (x (-9) 3)
    clear * - r2034 b2035 b2036 d2029
    omega
  have d2037 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
    have r2038 := hand1 (x (-9) 3) (x (-9) 13)
    have b2039 := hb (x (-9) 3)
    have b2040 := hb (x (-9) 3 && x (-9) 13)
    clear * - r2038 b2039 b2040 d2033
    omega
  have d2041 : (x (-9) 11).toNat = 0 := by
    have r2042 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
    have b2043 := hb (x (-9) 3)
    have b2044 := hb (x (-9) 11)
    clear * - r2042 b2043 b2044 d2033
    omega
  have d2045 : (x (-9) 13).toNat = 0 := by
    have r2046 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
    have b2047 := hb (x (-9) 1)
    have b2048 := hb (x (-9) 13)
    clear * - r2046 b2047 b2048 d2013
    omega
  have d2049 : (x (-9) 9 && x (-9) 13).toNat = 0 := by
    have r2050 := hand2 (x (-9) 9) (x (-9) 13)
    have b2051 := hb (x (-9) 13)
    have b2052 := hb (x (-9) 9 && x (-9) 13)
    clear * - r2050 b2051 b2052 d2045
    omega
  have d2053 : (x (-9) 5).toNat = 0 := by
    have r2054 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
    have b2055 := hb (x (-9) 5)
    have b2056 := hb (x (-9) 13)
    clear * - r2054 b2055 b2056 d2045
    omega
  have d2057 : (x (-9) 9).toNat = 0 := by
    have r2058 : (x (-9) 9).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp9 (-9))
    have b2059 := hb (x (-9) 1)
    have b2060 := hb (x (-9) 9)
    clear * - r2058 b2059 b2060 d2013
    omega
  have d2061 : (x (-10) 1).toNat = 1 := by
    have r2062 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2063 := hb (x (-10) 1)
    have b2064 := hb (x (-9) 14)
    clear * - r2062 b2063 b2064 d2021
    omega
  have d2065 : (x (-10) 14).toNat = 1 := by
    have r2066 : (x (-10) 1).toNat = (x (-10) 14).toNat := congrArg Bool.toNat (h114 (-10))
    have b2067 := hb (x (-10) 1)
    have b2068 := hb (x (-10) 14)
    clear * - r2066 b2067 b2068 d2061
    omega
  have d2069 : (x 1 12).toNat = 0 := by
    have r2070 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2071 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e2072 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b2073 := hb (x (-2) 3)
    have b2074 := hb (x (-1) 2)
    have b2075 := hb (x 0 13)
    have b2076 := hb (x 1 12)
    clear * - r2070 e2071 e2072 b2073 b2074 b2075 b2076 d1421 d1737
    omega
  have d2077 : (x 1 7 && x 1 12).toNat = 0 := by
    have r2078 := hand2 (x 1 7) (x 1 12)
    have b2079 := hb (x 1 12)
    have b2080 := hb (x 1 7 && x 1 12)
    clear * - r2078 b2079 b2080 d2069
    omega
  have d2081 : (x 1 8 && x 1 12).toNat = 0 := by
    have r2082 := hand2 (x 1 8) (x 1 12)
    have b2083 := hb (x 1 12)
    have b2084 := hb (x 1 8 && x 1 12)
    clear * - r2082 b2083 b2084 d2069
    omega
  have d2085 : (x 1 4).toNat = 0 := by
    have r2086 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b2087 := hb (x 1 4)
    have b2088 := hb (x 1 12)
    clear * - r2086 b2087 b2088 d2069
    omega
  have d2089 : (x 1 4 && x 1 8).toNat = 0 := by
    have r2090 := hand1 (x 1 4) (x 1 8)
    have b2091 := hb (x 1 4)
    have b2092 := hb (x 1 4 && x 1 8)
    clear * - r2090 b2091 b2092 d2085
    omega
  have d2093 : (x (-2) 3).toNat = 0 := by
    have r2094 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2095 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e2096 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b2097 := hb (x (-2) 3)
    have b2098 := hb (x (-1) 2)
    have b2099 := hb (x 0 13)
    have b2100 := hb (x 1 12)
    clear * - r2094 e2095 e2096 b2097 b2098 b2099 b2100 d2069 d1421 d1737
    omega
  have d2101 : (x (-2) 3 && x (-2) 12).toNat = 0 := by
    have r2102 := hand1 (x (-2) 3) (x (-2) 12)
    have b2103 := hb (x (-2) 3)
    have b2104 := hb (x (-2) 3 && x (-2) 12)
    clear * - r2102 b2103 b2104 d2093
    omega
  have d2105 : (x (-2) 2).toNat = 0 := by
    have r2106 : (x (-2) 2).toNat = (x (-2) 3).toNat := congrArg Bool.toNat (h23 (-2))
    have b2107 := hb (x (-2) 2)
    have b2108 := hb (x (-2) 3)
    clear * - r2106 b2107 b2108 d2093
    omega
  have d2109 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
    have r2110 := hand1 (x (-2) 2) (x (-2) 12)
    have b2111 := hb (x (-2) 2)
    have b2112 := hb (x (-2) 2 && x (-2) 12)
    clear * - r2110 b2111 b2112 d2105
    omega
  have d2113 : (x (-2) 2 && x (-2) 6).toNat = 0 := by
    have r2114 := hand1 (x (-2) 2) (x (-2) 6)
    have b2115 := hb (x (-2) 2)
    have b2116 := hb (x (-2) 2 && x (-2) 6)
    clear * - r2114 b2115 b2116 d2105
    omega
  have d2117 : (x (-2) 10).toNat = 0 := by
    have r2118 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
    have b2119 := hb (x (-2) 2)
    have b2120 := hb (x (-2) 10)
    clear * - r2118 b2119 b2120 d2105
    omega
  have d2121 : (x (-2) 11).toNat = 0 := by
    have r2122 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
    have b2123 := hb (x (-2) 3)
    have b2124 := hb (x (-2) 11)
    clear * - r2122 b2123 b2124 d2093
    omega
  have d2125 : (x (-2) 5 && x (-2) 11).toNat = 0 := by
    have r2126 := hand2 (x (-2) 5) (x (-2) 11)
    have b2127 := hb (x (-2) 11)
    have b2128 := hb (x (-2) 5 && x (-2) 11)
    clear * - r2126 b2127 b2128 d2121
    omega
  have d2129 : (x (-2) 6 && x (-2) 11).toNat = 0 := by
    have r2130 := hand2 (x (-2) 6) (x (-2) 11)
    have b2131 := hb (x (-2) 11)
    have b2132 := hb (x (-2) 6 && x (-2) 11)
    clear * - r2130 b2131 b2132 d2121
    omega
  have d2133 : (x (-2) 7 && x (-2) 11).toNat = 0 := by
    have r2134 := hand2 (x (-2) 7) (x (-2) 11)
    have b2135 := hb (x (-2) 11)
    have b2136 := hb (x (-2) 7 && x (-2) 11)
    clear * - r2134 b2135 b2136 d2121
    omega
  have d2137 : (x 5 8).toNat = 0 := by
    have r2138 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2139 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e2140 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e2141 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e2142 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e2143 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e2144 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b2145 := hb (x (-2) 7)
    have b2146 := hb (x (-1) 6)
    have b2147 := hb (x 0 5)
    have b2148 := hb (x 1 4)
    have b2149 := hb (x 2 11)
    have b2150 := hb (x 3 10)
    have b2151 := hb (x 4 9)
    have b2152 := hb (x 5 8)
    clear * - r2138 e2139 e2140 e2141 e2142 e2143 e2144 b2145 b2146 b2147 b2148 b2149 b2150 b2151 b2152 d1665 d2085 g1 d1729
    omega
  have d2153 : (x 5 4 && x 5 8).toNat = 0 := by
    have r2154 := hand2 (x 5 4) (x 5 8)
    have b2155 := hb (x 5 8)
    have b2156 := hb (x 5 4 && x 5 8)
    clear * - r2154 b2155 b2156 d2137
    omega
  have d2157 : (x 4 9).toNat = 0 := by
    have r2158 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2159 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e2160 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e2161 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e2162 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e2163 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e2164 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b2165 := hb (x (-2) 7)
    have b2166 := hb (x (-1) 6)
    have b2167 := hb (x 0 5)
    have b2168 := hb (x 1 4)
    have b2169 := hb (x 2 11)
    have b2170 := hb (x 3 10)
    have b2171 := hb (x 4 9)
    have b2172 := hb (x 5 8)
    clear * - r2158 e2159 e2160 e2161 e2162 e2163 e2164 b2165 b2166 b2167 b2168 b2169 b2170 b2171 b2172 d2137 d1665 d2085 g1 d1729
    omega
  have d2173 : (x 4 2 && x 4 9).toNat = 0 := by
    have r2174 := hand2 (x 4 2) (x 4 9)
    have b2175 := hb (x 4 9)
    have b2176 := hb (x 4 2 && x 4 9)
    clear * - r2174 b2175 b2176 d2157
    omega
  have d2177 : (x 4 4 && x 4 9).toNat = 0 := by
    have r2178 := hand2 (x 4 4) (x 4 9)
    have b2179 := hb (x 4 9)
    have b2180 := hb (x 4 4 && x 4 9)
    clear * - r2178 b2179 b2180 d2157
    omega
  have d2181 : (x 4 5 && x 4 9).toNat = 0 := by
    have r2182 := hand2 (x 4 5) (x 4 9)
    have b2183 := hb (x 4 9)
    have b2184 := hb (x 4 5 && x 4 9)
    clear * - r2182 b2183 b2184 d2157
    omega
  have d2185 : (x 2 11).toNat = 0 := by
    have r2186 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2187 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e2188 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e2189 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e2190 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e2191 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e2192 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b2193 := hb (x (-2) 7)
    have b2194 := hb (x (-1) 6)
    have b2195 := hb (x 0 5)
    have b2196 := hb (x 1 4)
    have b2197 := hb (x 2 11)
    have b2198 := hb (x 3 10)
    have b2199 := hb (x 4 9)
    have b2200 := hb (x 5 8)
    clear * - r2186 e2187 e2188 e2189 e2190 e2191 e2192 b2193 b2194 b2195 b2196 b2197 b2198 b2199 b2200 d2137 d2157 d1665 d2085 g1 d1729
    omega
  have d2201 : (x 2 1 && x 2 11).toNat = 0 := by
    have r2202 := hand2 (x 2 1) (x 2 11)
    have b2203 := hb (x 2 11)
    have b2204 := hb (x 2 1 && x 2 11)
    clear * - r2202 b2203 b2204 d2185
    omega
  have d2205 : (x 2 2 && x 2 11).toNat = 0 := by
    have r2206 := hand2 (x 2 2) (x 2 11)
    have b2207 := hb (x 2 11)
    have b2208 := hb (x 2 2 && x 2 11)
    clear * - r2206 b2207 b2208 d2185
    omega
  have d2209 : (x (-2) 6).toNat = 1 := by
    have r2210 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2211 := hb (x (-2) 6)
    have b2212 := hb (x 4 9)
    have b2213 := hb (x 3 1 && x 3 10)
    have b2214 := hb (x 2 2 && x 2 11)
    have b2215 := hb (x 1 3 && x 1 12)
    have b2216 := hb (x 0 4 && x 0 13)
    have b2217 := hb (x (-1) 5 && x (-1) 14)
    clear * - r2210 b2211 b2212 b2213 b2214 b2215 b2216 b2217 d2157 d1497 d2205 d1685 d1409 d1717
    omega
  have d2218 : (x 2 4 && x 2 11).toNat = 0 := by
    have r2219 := hand2 (x 2 4) (x 2 11)
    have b2220 := hb (x 2 11)
    have b2221 := hb (x 2 4 && x 2 11)
    clear * - r2219 b2220 b2221 d2185
    omega
  have d2222 : (x 2 6 && x 2 11).toNat = 0 := by
    have r2223 := hand2 (x 2 6) (x 2 11)
    have b2224 := hb (x 2 11)
    have b2225 := hb (x 2 6 && x 2 11)
    clear * - r2223 b2224 b2225 d2185
    omega
  have d2226 : (x 2 7 && x 2 11).toNat = 0 := by
    have r2227 := hand2 (x 2 7) (x 2 11)
    have b2228 := hb (x 2 11)
    have b2229 := hb (x 2 7 && x 2 11)
    clear * - r2227 b2228 b2229 d2185
    omega
  have d2230 : (x (-2) 7).toNat = 0 := by
    have r2231 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2232 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e2233 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e2234 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e2235 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e2236 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e2237 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b2238 := hb (x (-2) 7)
    have b2239 := hb (x (-1) 6)
    have b2240 := hb (x 0 5)
    have b2241 := hb (x 1 4)
    have b2242 := hb (x 2 11)
    have b2243 := hb (x 3 10)
    have b2244 := hb (x 4 9)
    have b2245 := hb (x 5 8)
    clear * - r2231 e2232 e2233 e2234 e2235 e2236 e2237 b2238 b2239 b2240 b2241 b2242 b2243 b2244 b2245 d2137 d2157 d1665 d2185 d2085 g1 d1729
    omega
  have d2246 : (x 4 8).toNat = 0 := by
    have r2247 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2248 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e2249 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e2250 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e2251 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e2252 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e2253 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b2254 := hb (x (-3) 7)
    have b2255 := hb (x (-2) 6)
    have b2256 := hb (x (-1) 5)
    have b2257 := hb (x 0 4)
    have b2258 := hb (x 1 11)
    have b2259 := hb (x 2 10)
    have b2260 := hb (x 3 9)
    have b2261 := hb (x 4 8)
    clear * - r2247 e2248 e2249 e2250 e2251 e2252 e2253 b2254 b2255 b2256 b2257 b2258 b2259 b2260 b2261 d1521 d1693 g0 d1777 d2209
    omega
  have d2262 : (x 2 10).toNat = 0 := by
    have r2263 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2264 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e2265 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e2266 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e2267 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e2268 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e2269 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b2270 := hb (x (-3) 7)
    have b2271 := hb (x (-2) 6)
    have b2272 := hb (x (-1) 5)
    have b2273 := hb (x 0 4)
    have b2274 := hb (x 1 11)
    have b2275 := hb (x 2 10)
    have b2276 := hb (x 3 9)
    have b2277 := hb (x 4 8)
    clear * - r2263 e2264 e2265 e2266 e2267 e2268 e2269 b2270 b2271 b2272 b2273 b2274 b2275 b2276 b2277 d2246 d1521 d1693 g0 d1777 d2209
    omega
  have d2278 : (x (-3) 7).toNat = 0 := by
    have r2279 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2280 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e2281 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e2282 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e2283 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e2284 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e2285 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b2286 := hb (x (-3) 7)
    have b2287 := hb (x (-2) 6)
    have b2288 := hb (x (-1) 5)
    have b2289 := hb (x 0 4)
    have b2290 := hb (x 1 11)
    have b2291 := hb (x 2 10)
    have b2292 := hb (x 3 9)
    have b2293 := hb (x 4 8)
    clear * - r2279 e2280 e2281 e2282 e2283 e2284 e2285 b2286 b2287 b2288 b2289 b2290 b2291 b2292 b2293 d2246 d1521 d2262 d1693 g0 d1777 d2209
    omega
  have d2294 : (x (-3) 7 && x (-3) 12).toNat = 0 := by
    have r2295 := hand1 (x (-3) 7) (x (-3) 12)
    have b2296 := hb (x (-3) 7)
    have b2297 := hb (x (-3) 7 && x (-3) 12)
    clear * - r2295 b2296 b2297 d2278
    omega
  cases h2298 : x 0 10
  · have f2299 : (x 0 10).toNat = 0 := by rw [h2298]; rfl
    have d2300 : (x 0 1 && x 0 10).toNat = 0 := by
      have r2301 := hand2 (x 0 1) (x 0 10)
      have b2302 := hb (x 0 10)
      have b2303 := hb (x 0 1 && x 0 10)
      clear * - r2301 b2302 b2303 f2299
      omega
    have d2304 : (x (-4) 4 && x (-4) 14).toNat = 1 := by
      have r2305 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2306 := hb (x (-5) 5)
      have b2307 := hb (x 0 10)
      have b2308 := hb (x (-1) 1 && x (-1) 11)
      have b2309 := hb (x (-2) 2 && x (-2) 12)
      have b2310 := hb (x (-3) 3 && x (-3) 13)
      have b2311 := hb (x (-4) 4 && x (-4) 14)
      clear * - r2305 b2306 b2307 b2308 b2309 b2310 b2311 f2299 d1701 d2109 d1825 d1929
      omega
    have d2312 : (x (-4) 4).toNat = 1 := by
      have r2313 := hand1 (x (-4) 4) (x (-4) 14)
      have b2314 := hb (x (-4) 4)
      have b2315 := hb (x (-4) 4 && x (-4) 14)
      clear * - r2313 b2314 b2315 d2304
      omega
    have d2316 : (x (-4) 12).toNat = 1 := by
      have r2317 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have b2318 := hb (x (-4) 4)
      have b2319 := hb (x (-4) 12)
      clear * - r2317 b2318 b2319 d2312
      omega
    have d2320 : (x (-6) 2).toNat = 0 := by
      have r2321 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2322 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e2323 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b2324 := hb (x (-7) 3)
      have b2325 := hb (x (-6) 2)
      have b2326 := hb (x (-5) 13)
      have b2327 := hb (x (-4) 12)
      clear * - r2321 e2322 e2323 b2324 b2325 b2326 b2327 d2316 d1925 d1969
      omega
    have d2328 : (x (-6) 2 && x (-6) 12).toNat = 0 := by
      have r2329 := hand1 (x (-6) 2) (x (-6) 12)
      have b2330 := hb (x (-6) 2)
      have b2331 := hb (x (-6) 2 && x (-6) 12)
      clear * - r2329 b2330 b2331 d2320
      omega
    have d2332 : (x (-6) 3).toNat = 0 := by
      have r2333 : (x (-6) 2).toNat = (x (-6) 3).toNat := congrArg Bool.toNat (h23 (-6))
      have b2334 := hb (x (-6) 2)
      have b2335 := hb (x (-6) 3)
      clear * - r2333 b2334 b2335 d2320
      omega
    have d2336 : (x (-6) 11).toNat = 0 := by
      have r2337 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
      have b2338 := hb (x (-6) 3)
      have b2339 := hb (x (-6) 11)
      clear * - r2337 b2338 b2339 d2332
      omega
    have d2340 : (x (-6) 1 && x (-6) 11).toNat = 0 := by
      have r2341 := hand2 (x (-6) 1) (x (-6) 11)
      have b2342 := hb (x (-6) 11)
      have b2343 := hb (x (-6) 1 && x (-6) 11)
      clear * - r2341 b2342 b2343 d2336
      omega
    have d2344 : (x (-6) 10).toNat = 0 := by
      have r2345 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
      have b2346 := hb (x (-6) 2)
      have b2347 := hb (x (-6) 10)
      clear * - r2345 b2346 b2347 d2320
      omega
    have d2348 : (x (-6) 6 && x (-6) 10).toNat = 0 := by
      have r2349 := hand2 (x (-6) 6) (x (-6) 10)
      have b2350 := hb (x (-6) 10)
      have b2351 := hb (x (-6) 6 && x (-6) 10)
      clear * - r2349 b2350 b2351 d2344
      omega
    have d2352 : (x (-4) 13).toNat = 1 := by
      have r2353 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2354 := hb (x (-6) 2)
      have b2355 := hb (x (-4) 13)
      have b2356 := hb (x (-5) 1 && x (-5) 14)
      clear * - r2353 b2354 b2355 b2356 d1873 d2320
      omega
    have d2357 : (x (-3) 12).toNat = 0 := by
      have r2358 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2359 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e2360 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b2361 := hb (x (-6) 3)
      have b2362 := hb (x (-5) 2)
      have b2363 := hb (x (-4) 13)
      have b2364 := hb (x (-3) 12)
      clear * - r2358 e2359 e2360 b2361 b2362 b2363 b2364 d2352 d1901 d2332
      omega
    have d2365 : (x (-3) 8 && x (-3) 12).toNat = 0 := by
      have r2366 := hand2 (x (-3) 8) (x (-3) 12)
      have b2367 := hb (x (-3) 12)
      have b2368 := hb (x (-3) 8 && x (-3) 12)
      clear * - r2366 b2367 b2368 d2357
      omega
    have d2369 : (x (-3) 4).toNat = 0 := by
      have r2370 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
      have b2371 := hb (x (-3) 4)
      have b2372 := hb (x (-3) 12)
      clear * - r2370 b2371 b2372 d2357
      omega
    have d2373 : (x (-4) 5 && x (-4) 14).toNat = 1 := by
      have r2374 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2375 := hb (x (-5) 6)
      have b2376 := hb (x 1 9)
      have b2377 := hb (x 0 1 && x 0 10)
      have b2378 := hb (x (-1) 2 && x (-1) 11)
      have b2379 := hb (x (-2) 3 && x (-2) 12)
      have b2380 := hb (x (-3) 4 && x (-3) 13)
      have b2381 := hb (x (-4) 5 && x (-4) 14)
      clear * - r2374 b2375 b2376 b2377 b2378 b2379 b2380 b2381 d1465 d2300 d1741 d2101 d1841 d1897
      omega
    have d2382 : (x (-4) 5).toNat = 1 := by
      have r2383 := hand1 (x (-4) 5) (x (-4) 14)
      have b2384 := hb (x (-4) 5)
      have b2385 := hb (x (-4) 5 && x (-4) 14)
      clear * - r2383 b2384 b2385 d2373
      omega
    have d2386 : (x 1 8).toNat = 0 := by
      have r2387 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2388 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e2389 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e2390 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e2391 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e2392 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e2393 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b2394 := hb (x (-6) 7)
      have b2395 := hb (x (-5) 6)
      have b2396 := hb (x (-4) 5)
      have b2397 := hb (x (-3) 4)
      have b2398 := hb (x (-2) 11)
      have b2399 := hb (x (-1) 10)
      have b2400 := hb (x 0 9)
      have b2401 := hb (x 1 8)
      clear * - r2387 e2388 e2389 e2390 e2391 e2392 e2393 b2394 b2395 b2396 b2397 b2398 b2399 b2400 b2401 d1761 d2121 d2369 d2382 d1897
      omega
    have d2402 : (x 0 9).toNat = 0 := by
      have r2403 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2404 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e2405 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e2406 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e2407 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e2408 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e2409 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b2410 := hb (x (-6) 7)
      have b2411 := hb (x (-5) 6)
      have b2412 := hb (x (-4) 5)
      have b2413 := hb (x (-3) 4)
      have b2414 := hb (x (-2) 11)
      have b2415 := hb (x (-1) 10)
      have b2416 := hb (x 0 9)
      have b2417 := hb (x 1 8)
      clear * - r2403 e2404 e2405 e2406 e2407 e2408 e2409 b2410 b2411 b2412 b2413 b2414 b2415 b2416 b2417 d2386 d1761 d2121 d2369 d2382 d1897
      omega
    have d2418 : (x 0 3 && x 0 9).toNat = 0 := by
      have r2419 := hand2 (x 0 3) (x 0 9)
      have b2420 := hb (x 0 9)
      have b2421 := hb (x 0 3 && x 0 9)
      clear * - r2419 b2420 b2421 d2402
      omega
    have d2422 : (x 0 9 && x 0 13).toNat = 0 := by
      have r2423 := hand1 (x 0 9) (x 0 13)
      have b2424 := hb (x 0 9)
      have b2425 := hb (x 0 9 && x 0 13)
      clear * - r2423 b2424 b2425 d2402
      omega
    have d2426 : (x 0 5 && x 0 9).toNat = 0 := by
      have r2427 := hand2 (x 0 5) (x 0 9)
      have b2428 := hb (x 0 9)
      have b2429 := hb (x 0 5 && x 0 9)
      clear * - r2427 b2428 b2429 d2402
      omega
    have r2430 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2431 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2432 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2433 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2434 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2435 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
    have e2436 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
    have e2437 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
    have e2438 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
    have e2439 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
    have e2440 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
    have r2441 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2442 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e2443 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e2444 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e2445 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e2446 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e2447 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have r2448 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2449 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e2450 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e2451 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e2452 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e2453 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e2454 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have r2455 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2456 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e2457 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e2458 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e2459 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e2460 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e2461 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have r2462 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2463 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e2464 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have r2465 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2466 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e2467 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have r2468 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2469 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
    have e2470 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
    have r2471 : 1 ≤ (x 5 4).toNat + (x 4 1 && x 4 5).toNat + (x 3 2 && x 3 6).toNat + (x 2 3 && x 2 7).toNat + (x 1 4 && x 1 8).toNat + (x 0 5 && x 0 9).toNat + (x (-1) 6 && x (-1) 10).toNat + (x (-2) 7 && x (-2) 11).toNat + (x (-3) 8 && x (-3) 12).toNat + (x (-4) 9 && x (-4) 13).toNat + (x (-5) 10 && x (-5) 14).toNat + (x (-6) 11).toNat := by have q := hcov4 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2472 : (x 4 1 && x 4 5).toNat = (x 4 5).toNat := handr _ _ (fun h => hp13 4 (hp5 4 (h)))
    have e2473 : (x (-5) 10 && x (-5) 14).toNat = (x (-5) 10).toNat := handl _ _ (fun h => hp2 (-5) (hp10 (-5) (h)))
    have r2474 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2475 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
    have e2476 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
    have r2477 : 1 ≤ (x 4 5).toNat + (x 3 1 && x 3 6).toNat + (x 2 2 && x 2 7).toNat + (x 1 3 && x 1 8).toNat + (x 0 4 && x 0 9).toNat + (x (-1) 5 && x (-1) 10).toNat + (x (-2) 6 && x (-2) 11).toNat + (x (-3) 7 && x (-3) 12).toNat + (x (-4) 8 && x (-4) 13).toNat + (x (-5) 9 && x (-5) 14).toNat + (x (-6) 10).toNat := by have q := hcov5 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2478 : 1 ≤ (x 3 6).toNat + (x 2 1 && x 2 7).toNat + (x 1 2 && x 1 8).toNat + (x 0 3 && x 0 9).toNat + (x (-1) 4 && x (-1) 10).toNat + (x (-2) 5 && x (-2) 11).toNat + (x (-3) 6 && x (-3) 12).toNat + (x (-4) 7 && x (-4) 13).toNat + (x (-5) 8 && x (-5) 14).toNat + (x (-6) 9).toNat := by have q := hcov6 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2479 : 1 ≤ (x 6 7).toNat + (x 5 1 && x 5 8).toNat + (x 4 2 && x 4 9).toNat + (x 3 3 && x 3 10).toNat + (x 2 4 && x 2 11).toNat + (x 1 5 && x 1 12).toNat + (x 0 6 && x 0 13).toNat + (x (-1) 7 && x (-1) 14).toNat + (x (-2) 8).toNat := by have q := hcov7 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2480 : 1 ≤ (x (-5) 10).toNat + (x (-6) 1 && x (-6) 11).toNat + (x (-7) 2 && x (-7) 12).toNat + (x (-8) 3 && x (-8) 13).toNat + (x (-9) 4 && x (-9) 14).toNat + (x (-10) 5).toNat := by have q := hcov10 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2481 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2482 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2483 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2484 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2485 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2486 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2487 : (x (-10) 5).toNat ≤ (x (-10) 13).toNat := himp _ _ (hp5 (-10))
    have r2488 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
    have r2489 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
    have r2490 := hand2 (x (-4) 4) (x (-4) 8)
    have r2491 := hand1 (x (-8) 8) (x (-8) 12)
    have r2492 := hand1 (x 2 3) (x 2 7)
    have r2493 := hand1 (x (-4) 9) (x (-4) 13)
    have r2494 := hand1 (x 6 3) (x 6 7)
    have r2495 := hand1 (x 2 2) (x 2 7)
    have r2496 := hand1 (x (-4) 8) (x (-4) 13)
    have r2497 := hand2 (x 2 1) (x 2 7)
    have r2498 := hand1 (x (-4) 7) (x (-4) 13)
    have r2499 := hand1 (x 0 6) (x 0 13)
    have r2500 := hand2 (x (-8) 3) (x (-8) 13)
    have r2501 := hand1 (x (-8) 4) (x (-8) 14)
    have r2502 := hand1 (x 0 3) (x 0 13)
    have r2503 := hand2 (x 2 2) (x 2 12)
    have r2504 := hand2 (x (-10) 2) (x (-10) 13)
    have r2505 := hand2 (x (-11) 3) (x (-11) 14)
    have r2506 := hand1 (x (-4) 2) (x (-4) 13)
    have r2507 := hand1 (x 0 2) (x 0 13)
    have b2508 := hb (x (-15) 7)
    have b2509 := hb (x (-14) 6)
    have b2510 := hb (x (-13) 5)
    have b2511 := hb (x (-12) 4)
    have b2512 := hb (x (-11) 11)
    have b2513 := hb (x (-11) 14)
    have b2514 := hb (x (-10) 5)
    have b2515 := hb (x (-10) 10)
    have b2516 := hb (x (-10) 13)
    have b2517 := hb (x (-10) 14)
    have b2518 := hb (x (-9) 5)
    have b2519 := hb (x (-9) 7)
    have b2520 := hb (x (-9) 9)
    have b2521 := hb (x (-9) 12)
    have b2522 := hb (x (-9) 13)
    have b2523 := hb (x (-9) 14)
    have b2524 := hb (x (-8) 4)
    have b2525 := hb (x (-8) 6)
    have b2526 := hb (x (-8) 8)
    have b2527 := hb (x (-8) 11)
    have b2528 := hb (x (-8) 12)
    have b2529 := hb (x (-8) 13)
    have b2530 := hb (x (-7) 5)
    have b2531 := hb (x (-7) 10)
    have b2532 := hb (x (-7) 11)
    have b2533 := hb (x (-7) 12)
    have b2534 := hb (x (-6) 4)
    have b2535 := hb (x (-6) 9)
    have b2536 := hb (x (-6) 10)
    have b2537 := hb (x (-6) 11)
    have b2538 := hb (x (-5) 3)
    have b2539 := hb (x (-5) 8)
    have b2540 := hb (x (-5) 9)
    have b2541 := hb (x (-5) 10)
    have b2542 := hb (x (-5) 11)
    have b2543 := hb (x (-5) 14)
    have b2544 := hb (x (-4) 2)
    have b2545 := hb (x (-4) 7)
    have b2546 := hb (x (-4) 8)
    have b2547 := hb (x (-4) 9)
    have b2548 := hb (x (-4) 10)
    have b2549 := hb (x (-4) 13)
    have b2550 := hb (x (-3) 6)
    have b2551 := hb (x (-3) 7)
    have b2552 := hb (x (-3) 8)
    have b2553 := hb (x (-3) 9)
    have b2554 := hb (x (-3) 12)
    have b2555 := hb (x (-3) 13)
    have b2556 := hb (x (-2) 4)
    have b2557 := hb (x (-2) 5)
    have b2558 := hb (x (-2) 6)
    have b2559 := hb (x (-2) 7)
    have b2560 := hb (x (-2) 8)
    have b2561 := hb (x (-2) 11)
    have b2562 := hb (x (-2) 12)
    have b2563 := hb (x (-1) 3)
    have b2564 := hb (x (-1) 4)
    have b2565 := hb (x (-1) 5)
    have b2566 := hb (x (-1) 6)
    have b2567 := hb (x (-1) 7)
    have b2568 := hb (x (-1) 10)
    have b2569 := hb (x 0 2)
    have b2570 := hb (x 0 3)
    have b2571 := hb (x 0 4)
    have b2572 := hb (x 0 5)
    have b2573 := hb (x 0 6)
    have b2574 := hb (x 0 9)
    have b2575 := hb (x 1 2)
    have b2576 := hb (x 1 3)
    have b2577 := hb (x 1 4)
    have b2578 := hb (x 1 5)
    have b2579 := hb (x 1 8)
    have b2580 := hb (x 1 13)
    have b2581 := hb (x 2 1)
    have b2582 := hb (x 2 2)
    have b2583 := hb (x 2 3)
    have b2584 := hb (x 2 4)
    have b2585 := hb (x 2 7)
    have b2586 := hb (x 2 11)
    have b2587 := hb (x 2 12)
    have b2588 := hb (x 3 1)
    have b2589 := hb (x 3 2)
    have b2590 := hb (x 3 6)
    have b2591 := hb (x 3 10)
    have b2592 := hb (x 3 11)
    have b2593 := hb (x 4 1)
    have b2594 := hb (x 4 5)
    have b2595 := hb (x 4 10)
    have b2596 := hb (x 5 4)
    have b2597 := hb (x 5 9)
    have b2598 := hb (x 6 3)
    have b2599 := hb (x 6 7)
    have b2600 := hb (x 6 8)
    have b2601 := hb (x 7 2)
    have b2602 := hb (x 7 6)
    have b2603 := hb (x 8 1)
    have b2604 := hb (x 8 5)
    have b2605 := hb (x 9 4)
    have b2606 := hb (x 10 11)
    have b2607 := hb (x 11 10)
    have b2608 := hb (x 12 9)
    have b2609 := hb (x 13 8)
    have b2610 := hb (x (-2) 2 && x (-2) 6)
    have b2611 := hb (x (-3) 3 && x (-3) 7)
    have b2612 := hb (x (-4) 4 && x (-4) 8)
    have b2613 := hb (x (-5) 5 && x (-5) 9)
    have b2614 := hb (x (-6) 6 && x (-6) 10)
    have b2615 := hb (x (-7) 7 && x (-7) 11)
    have b2616 := hb (x (-8) 8 && x (-8) 12)
    have b2617 := hb (x (-9) 9 && x (-9) 13)
    have b2618 := hb (x 3 2 && x 3 6)
    have b2619 := hb (x 2 3 && x 2 7)
    have b2620 := hb (x 1 4 && x 1 8)
    have b2621 := hb (x 0 5 && x 0 9)
    have b2622 := hb (x (-1) 6 && x (-1) 10)
    have b2623 := hb (x (-2) 7 && x (-2) 11)
    have b2624 := hb (x (-3) 8 && x (-3) 12)
    have b2625 := hb (x (-4) 9 && x (-4) 13)
    have b2626 := hb (x 7 2 && x 7 6)
    have b2627 := hb (x 6 3 && x 6 7)
    have b2628 := hb (x 5 4 && x 5 8)
    have b2629 := hb (x 4 5 && x 4 9)
    have b2630 := hb (x 3 6 && x 3 10)
    have b2631 := hb (x 2 7 && x 2 11)
    have b2632 := hb (x 1 8 && x 1 12)
    have b2633 := hb (x 0 9 && x 0 13)
    have b2634 := hb (x 3 1 && x 3 6)
    have b2635 := hb (x 2 2 && x 2 7)
    have b2636 := hb (x 1 3 && x 1 8)
    have b2637 := hb (x 0 4 && x 0 9)
    have b2638 := hb (x (-1) 5 && x (-1) 10)
    have b2639 := hb (x (-2) 6 && x (-2) 11)
    have b2640 := hb (x (-3) 7 && x (-3) 12)
    have b2641 := hb (x (-4) 8 && x (-4) 13)
    have b2642 := hb (x (-5) 9 && x (-5) 14)
    have b2643 := hb (x 2 1 && x 2 7)
    have b2644 := hb (x 1 2 && x 1 8)
    have b2645 := hb (x 0 3 && x 0 9)
    have b2646 := hb (x (-1) 4 && x (-1) 10)
    have b2647 := hb (x (-2) 5 && x (-2) 11)
    have b2648 := hb (x (-3) 6 && x (-3) 12)
    have b2649 := hb (x (-4) 7 && x (-4) 13)
    have b2650 := hb (x (-5) 8 && x (-5) 14)
    have b2651 := hb (x 5 1 && x 5 8)
    have b2652 := hb (x 4 2 && x 4 9)
    have b2653 := hb (x 3 3 && x 3 10)
    have b2654 := hb (x 2 4 && x 2 11)
    have b2655 := hb (x 1 5 && x 1 12)
    have b2656 := hb (x 0 6 && x 0 13)
    have b2657 := hb (x (-1) 7 && x (-1) 14)
    have b2658 := hb (x (-6) 1 && x (-6) 11)
    have b2659 := hb (x (-7) 2 && x (-7) 12)
    have b2660 := hb (x (-8) 3 && x (-8) 13)
    have b2661 := hb (x (-9) 4 && x (-9) 14)
    have b2662 := hb (x (-5) 1 && x (-5) 11)
    have b2663 := hb (x (-6) 2 && x (-6) 12)
    have b2664 := hb (x (-7) 3 && x (-7) 13)
    have b2665 := hb (x (-8) 4 && x (-8) 14)
    have b2666 := hb (x 2 1 && x 2 11)
    have b2667 := hb (x 1 2 && x 1 12)
    have b2668 := hb (x 0 3 && x 0 13)
    have b2669 := hb (x (-1) 4 && x (-1) 14)
    have b2670 := hb (x 3 1 && x 3 11)
    have b2671 := hb (x 2 2 && x 2 12)
    have b2672 := hb (x 1 3 && x 1 13)
    have b2673 := hb (x 0 4 && x 0 14)
    have b2674 := hb (x (-9) 1 && x (-9) 12)
    have b2675 := hb (x (-10) 2 && x (-10) 13)
    have b2676 := hb (x (-11) 3 && x (-11) 14)
    have b2677 := hb (x (-3) 1 && x (-3) 12)
    have b2678 := hb (x (-4) 2 && x (-4) 13)
    have b2679 := hb (x (-5) 3 && x (-5) 14)
    have b2680 := hb (x 1 1 && x 1 12)
    have b2681 := hb (x 0 2 && x 0 13)
    have b2682 := hb (x (-1) 3 && x (-1) 14)
    linarith only [r2430, r2431, r2432, r2433, r2434, e2435, e2436, e2437, e2438, e2439, e2440, r2441, e2442, e2443, e2444, e2445, e2446, e2447, r2448, e2449, e2450, e2451, e2452, e2453, e2454, r2455, e2456, e2457, e2458, e2459, e2460, e2461, r2462, e2463, e2464, r2465, e2466, e2467, r2468, e2469, e2470, r2471, e2472, e2473, r2474, e2475, e2476, r2477, r2478, r2479, r2480, r2481, r2482, r2483, r2484, r2485, r2486, r2487, r2488, r2489, r2490, r2491, r2492, r2493, r2494, r2495, r2496, r2497, r2498, r2499, r2500, r2501, r2502, r2503, r2504, r2505, r2506, r2507, b2508, b2509, b2510, b2511, b2512, b2513, b2514, b2515, b2516, b2517, b2518, b2519, b2520, b2521, b2522, b2523, b2524, b2525, b2526, b2527, b2528, b2529, b2530, b2531, b2532, b2533, b2534, b2535, b2536, b2537, b2538, b2539, b2540, b2541, b2542, b2543, b2544, b2545, b2546, b2547, b2548, b2549, b2550, b2551, b2552, b2553, b2554, b2555, b2556, b2557, b2558, b2559, b2560, b2561, b2562, b2563, b2564, b2565, b2566, b2567, b2568, b2569, b2570, b2571, b2572, b2573, b2574, b2575, b2576, b2577, b2578, b2579, b2580, b2581, b2582, b2583, b2584, b2585, b2586, b2587, b2588, b2589, b2590, b2591, b2592, b2593, b2594, b2595, b2596, b2597, b2598, b2599, b2600, b2601, b2602, b2603, b2604, b2605, b2606, b2607, b2608, b2609, b2610, b2611, b2612, b2613, b2614, b2615, b2616, b2617, b2618, b2619, b2620, b2621, b2622, b2623, b2624, b2625, b2626, b2627, b2628, b2629, b2630, b2631, b2632, b2633, b2634, b2635, b2636, b2637, b2638, b2639, b2640, b2641, b2642, b2643, b2644, b2645, b2646, b2647, b2648, b2649, b2650, b2651, b2652, b2653, b2654, b2655, b2656, b2657, b2658, b2659, b2660, b2661, b2662, b2663, b2664, b2665, b2666, b2667, b2668, b2669, b2670, b2671, b2672, b2673, b2674, b2675, b2676, b2677, b2678, b2679, b2680, b2681, b2682, d2065, d2053, d2057, d2045, d2021, d1997, d1985, d1977, d2344, d2336, d1905, d1937, d1921, d1913, d1881, d2352, d1809, d2278, d1857, d2357, d1837, d2209, d2230, d2121, d1745, d1777, d1729, d1761, g0, g1, d2402, d1669, d1681, d2085, d1457, d2386, d1449, d1477, d2185, d1485, d1649, d1637, d1665, d1661, d1529, d1557, d1617, d1609, d1593, d2113, d1829, d1933, d2348, d1981, d2049, d1645, d2089, d2426, d1733, d2133, d2365, d1613, d2153, d2181, d1641, d2226, d2081, d2422, d1505, d1689, d1417, d1769, d2129, d2294, d1893, d1677, d2418, d1765, d2125, d1813, d1889, d1541, d2173, d1657, d2218, d1461, d1721, d2340, d1965, d2025, d1877, d2328, d1973, d2201, d1673, d1713, d1493, d1453, d1405, d2017, d1797, d1885, d1445, d1709]
  · have f2683 : (x 0 10).toNat = 1 := by rw [h2298]; rfl
    have d2684 : (x 0 2).toNat = 1 := by
      have r2685 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
      have b2686 := hb (x 0 2)
      have b2687 := hb (x 0 10)
      clear * - r2685 b2686 b2687 f2683
      omega
    have d2688 : (x 0 3).toNat = 1 := by
      have r2689 : (x 0 2).toNat = (x 0 3).toNat := congrArg Bool.toNat (h23 0)
      have b2690 := hb (x 0 2)
      have b2691 := hb (x 0 3)
      clear * - r2689 b2690 b2691 d2684
      omega
    have d2692 : (x 3 12).toNat = 0 := by
      have r2693 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2694 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e2695 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b2696 := hb (x 0 3)
      have b2697 := hb (x 1 2)
      have b2698 := hb (x 2 13)
      have b2699 := hb (x 3 12)
      clear * - r2693 e2694 e2695 b2696 b2697 b2698 b2699 d1669 d2688
      omega
    have d2700 : (x 2 13).toNat = 0 := by
      have r2701 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2702 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e2703 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b2704 := hb (x 0 3)
      have b2705 := hb (x 1 2)
      have b2706 := hb (x 2 13)
      have b2707 := hb (x 3 12)
      clear * - r2701 e2702 e2703 b2704 b2705 b2706 b2707 d2692 d1669 d2688
      omega
    have d2708 : (x 2 2 && x 2 13).toNat = 0 := by
      have r2709 := hand2 (x 2 2) (x 2 13)
      have b2710 := hb (x 2 13)
      have b2711 := hb (x 2 2 && x 2 13)
      clear * - r2709 b2710 b2711 d2700
      omega
    have d2712 : (x 2 12).toNat = 0 := by
      have r2713 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2714 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e2715 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b2716 := hb (x (-1) 3)
      have b2717 := hb (x 0 2)
      have b2718 := hb (x 1 13)
      have b2719 := hb (x 2 12)
      clear * - r2713 e2714 e2715 b2716 b2717 b2718 b2719 d1449 d2684 d1745
      omega
    have d2720 : (x 2 2 && x 2 12).toNat = 0 := by
      have r2721 := hand2 (x 2 2) (x 2 12)
      have b2722 := hb (x 2 12)
      have b2723 := hb (x 2 2 && x 2 12)
      clear * - r2721 b2722 b2723 d2712
      omega
    have d2724 : (x 2 4).toNat = 0 := by
      have r2725 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
      have b2726 := hb (x 2 4)
      have b2727 := hb (x 2 12)
      clear * - r2725 b2726 b2727 d2712
      omega
    have d2728 : (x 4 11).toNat = 1 := by
      have r2729 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2730 := hb (x 0 4)
      have b2731 := hb (x 4 11)
      have b2732 := hb (x 3 1 && x 3 12)
      have b2733 := hb (x 2 2 && x 2 13)
      have b2734 := hb (x 1 3 && x 1 14)
      clear * - r2729 b2730 b2731 b2732 b2733 b2734 d1489 d2708 d1437 g0
      omega
    have d2735 : (x 4 3).toNat = 1 := by
      have r2736 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
      have b2737 := hb (x 4 3)
      have b2738 := hb (x 4 11)
      clear * - r2736 b2737 b2738 d2728
      omega
    have d2739 : (x 4 2).toNat = 1 := by
      have r2740 : (x 4 2).toNat = (x 4 3).toNat := congrArg Bool.toNat (h23 4)
      have b2741 := hb (x 4 2)
      have b2742 := hb (x 4 3)
      clear * - r2740 b2741 b2742 d2735
      omega
    have d2743 : (x 6 12).toNat = 0 := by
      have r2744 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2745 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e2746 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b2747 := hb (x 3 3)
      have b2748 := hb (x 4 2)
      have b2749 := hb (x 5 13)
      have b2750 := hb (x 6 12)
      clear * - r2744 e2745 e2746 b2747 b2748 b2749 b2750 d1545 d2739 d1653
      omega
    have d2751 : (x 6 2 && x 6 12).toNat = 0 := by
      have r2752 := hand2 (x 6 2) (x 6 12)
      have b2753 := hb (x 6 12)
      have b2754 := hb (x 6 2 && x 6 12)
      clear * - r2752 b2753 b2754 d2743
      omega
    have d2755 : (x 6 4).toNat = 0 := by
      have r2756 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
      have b2757 := hb (x 6 4)
      have b2758 := hb (x 6 12)
      clear * - r2756 b2757 b2758 d2743
      omega
    have d2759 : (x 4 10).toNat = 1 := by
      have r2760 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2761 := hb (x (-1) 5)
      have b2762 := hb (x 4 10)
      have b2763 := hb (x 3 1 && x 3 11)
      have b2764 := hb (x 2 2 && x 2 12)
      have b2765 := hb (x 1 3 && x 1 13)
      have b2766 := hb (x 0 4 && x 0 14)
      clear * - r2760 b2761 b2762 b2763 b2764 b2765 b2766 d1493 d2720 d1453 d1405 d1777
      omega
    have d2767 : (x 6 8).toNat = 0 := by
      have r2768 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2769 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e2770 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e2771 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e2772 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e2773 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e2774 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b2775 := hb (x (-1) 7)
      have b2776 := hb (x 0 6)
      have b2777 := hb (x 1 5)
      have b2778 := hb (x 2 4)
      have b2779 := hb (x 3 11)
      have b2780 := hb (x 4 10)
      have b2781 := hb (x 5 9)
      have b2782 := hb (x 6 8)
      clear * - r2768 e2769 e2770 e2771 e2772 e2773 e2774 b2775 b2776 b2777 b2778 b2779 b2780 b2781 b2782 d1557 d2759 d1661 d2724 d1457
      omega
    have d2783 : (x 0 6).toNat = 0 := by
      have r2784 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2785 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e2786 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e2787 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e2788 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e2789 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e2790 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b2791 := hb (x (-1) 7)
      have b2792 := hb (x 0 6)
      have b2793 := hb (x 1 5)
      have b2794 := hb (x 2 4)
      have b2795 := hb (x 3 11)
      have b2796 := hb (x 4 10)
      have b2797 := hb (x 5 9)
      have b2798 := hb (x 6 8)
      clear * - r2784 e2785 e2786 e2787 e2788 e2789 e2790 b2791 b2792 b2793 b2794 b2795 b2796 b2797 b2798 d2767 d1557 d2759 d1661 d2724 d1457
      omega
    have d2799 : (x 0 6 && x 0 13).toNat = 0 := by
      have r2800 := hand1 (x 0 6) (x 0 13)
      have b2801 := hb (x 0 6)
      have b2802 := hb (x 0 6 && x 0 13)
      clear * - r2800 b2801 b2802 d2783
      omega
    have d2803 : (x 0 2 && x 0 6).toNat = 0 := by
      have r2804 := hand2 (x 0 2) (x 0 6)
      have b2805 := hb (x 0 6)
      have b2806 := hb (x 0 2 && x 0 6)
      clear * - r2804 b2805 b2806 d2783
      omega
    have d2807 : (x 2 8).toNat = 0 := by
      have r2808 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2809 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e2810 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e2811 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e2812 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e2813 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e2814 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b2815 := hb (x (-5) 7)
      have b2816 := hb (x (-4) 6)
      have b2817 := hb (x (-3) 5)
      have b2818 := hb (x (-2) 4)
      have b2819 := hb (x (-1) 11)
      have b2820 := hb (x 0 10)
      have b2821 := hb (x 1 9)
      have b2822 := hb (x 2 8)
      clear * - r2808 e2809 e2810 e2811 e2812 e2813 e2814 b2815 b2816 b2817 b2818 b2819 b2820 b2821 b2822 d1465 f2683 d1753 d1849
      omega
    have d2823 : (x 2 2 && x 2 8).toNat = 0 := by
      have r2824 := hand2 (x 2 2) (x 2 8)
      have b2825 := hb (x 2 8)
      have b2826 := hb (x 2 2 && x 2 8)
      clear * - r2824 b2825 b2826 d2807
      omega
    have d2827 : (x (-2) 4).toNat = 0 := by
      have r2828 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2829 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e2830 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e2831 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e2832 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e2833 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e2834 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b2835 := hb (x (-5) 7)
      have b2836 := hb (x (-4) 6)
      have b2837 := hb (x (-3) 5)
      have b2838 := hb (x (-2) 4)
      have b2839 := hb (x (-1) 11)
      have b2840 := hb (x 0 10)
      have b2841 := hb (x 1 9)
      have b2842 := hb (x 2 8)
      clear * - r2828 e2829 e2830 e2831 e2832 e2833 e2834 b2835 b2836 b2837 b2838 b2839 b2840 b2841 b2842 d2807 d1465 f2683 d1753 d1849
      omega
    have d2843 : (x (-2) 4 && x (-2) 8).toNat = 0 := by
      have r2844 := hand1 (x (-2) 4) (x (-2) 8)
      have b2845 := hb (x (-2) 4)
      have b2846 := hb (x (-2) 4 && x (-2) 8)
      clear * - r2844 b2845 b2846 d2827
      omega
    have d2847 : (x (-4) 6).toNat = 0 := by
      have r2848 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2849 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e2850 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e2851 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e2852 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e2853 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e2854 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b2855 := hb (x (-5) 7)
      have b2856 := hb (x (-4) 6)
      have b2857 := hb (x (-3) 5)
      have b2858 := hb (x (-2) 4)
      have b2859 := hb (x (-1) 11)
      have b2860 := hb (x 0 10)
      have b2861 := hb (x 1 9)
      have b2862 := hb (x 2 8)
      clear * - r2848 e2849 e2850 e2851 e2852 e2853 e2854 b2855 b2856 b2857 b2858 b2859 b2860 b2861 b2862 d2807 d1465 f2683 d1753 d2827 d1849
      omega
    have d2863 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
      have r2864 := hand1 (x (-4) 6) (x (-4) 10)
      have b2865 := hb (x (-4) 6)
      have b2866 := hb (x (-4) 6 && x (-4) 10)
      clear * - r2864 b2865 b2866 d2847
      omega
    have r2867 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2868 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2869 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2870 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2871 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
    have e2872 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
    have e2873 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
    have e2874 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
    have e2875 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
    have e2876 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
    have r2877 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2878 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e2879 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e2880 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e2881 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e2882 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e2883 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have r2884 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2885 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e2886 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e2887 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e2888 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e2889 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e2890 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have r2891 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2892 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
    have e2893 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
    have r2894 : 1 ≤ (x 8 5).toNat + (x 7 1 && x 7 6).toNat + (x 6 2 && x 6 7).toNat + (x 5 3 && x 5 8).toNat + (x 4 4 && x 4 9).toNat + (x 3 5 && x 3 10).toNat + (x 2 6 && x 2 11).toNat + (x 1 7 && x 1 12).toNat + (x 0 8 && x 0 13).toNat + (x (-1) 9 && x (-1) 14).toNat + (x (-2) 10).toNat := by have q := hcov5 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2895 : 1 ≤ (x 4 6).toNat + (x 3 1 && x 3 7).toNat + (x 2 2 && x 2 8).toNat + (x 1 3 && x 1 9).toNat + (x 0 4 && x 0 10).toNat + (x (-1) 5 && x (-1) 11).toNat + (x (-2) 6 && x (-2) 12).toNat + (x (-3) 7 && x (-3) 13).toNat + (x (-4) 8 && x (-4) 14).toNat + (x (-5) 9).toNat := by have q := hcov6 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2896 : 1 ≤ (x 6 7).toNat + (x 5 1 && x 5 8).toNat + (x 4 2 && x 4 9).toNat + (x 3 3 && x 3 10).toNat + (x 2 4 && x 2 11).toNat + (x 1 5 && x 1 12).toNat + (x 0 6 && x 0 13).toNat + (x (-1) 7 && x (-1) 14).toNat + (x (-2) 8).toNat := by have q := hcov7 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2897 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2898 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2899 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2900 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r2901 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
    have r2902 := hand1 (x (-6) 8) (x (-6) 12)
    have r2903 := hand1 (x 6 2) (x 6 7)
    have r2904 := hand1 (x 0 8) (x 0 13)
    have r2905 := hand2 (x (-2) 6) (x (-2) 12)
    have r2906 := hand1 (x (-4) 8) (x (-4) 14)
    have r2907 := hand2 (x (-8) 2) (x (-8) 12)
    have r2908 := hand1 (x (-10) 4) (x (-10) 14)
    have r2909 := hand2 (x (-4) 2) (x (-4) 12)
    have r2910 := hand1 (x (-6) 4) (x (-6) 14)
    have r2911 := hand1 (x 4 4) (x 4 14)
    have r2912 := hand1 (x 8 2) (x 8 13)
    have b2913 := hb (x (-13) 7)
    have b2914 := hb (x (-12) 6)
    have b2915 := hb (x (-11) 5)
    have b2916 := hb (x (-10) 4)
    have b2917 := hb (x (-10) 14)
    have b2918 := hb (x (-9) 7)
    have b2919 := hb (x (-9) 11)
    have b2920 := hb (x (-9) 13)
    have b2921 := hb (x (-8) 6)
    have b2922 := hb (x (-8) 10)
    have b2923 := hb (x (-8) 12)
    have b2924 := hb (x (-7) 5)
    have b2925 := hb (x (-7) 9)
    have b2926 := hb (x (-7) 11)
    have b2927 := hb (x (-6) 4)
    have b2928 := hb (x (-6) 8)
    have b2929 := hb (x (-6) 10)
    have b2930 := hb (x (-6) 14)
    have b2931 := hb (x (-5) 9)
    have b2932 := hb (x (-5) 11)
    have b2933 := hb (x (-5) 13)
    have b2934 := hb (x (-4) 8)
    have b2935 := hb (x (-4) 10)
    have b2936 := hb (x (-4) 12)
    have b2937 := hb (x (-4) 14)
    have b2938 := hb (x (-3) 7)
    have b2939 := hb (x (-3) 9)
    have b2940 := hb (x (-3) 11)
    have b2941 := hb (x (-3) 13)
    have b2942 := hb (x (-2) 6)
    have b2943 := hb (x (-2) 8)
    have b2944 := hb (x (-2) 10)
    have b2945 := hb (x (-2) 12)
    have b2946 := hb (x (-1) 5)
    have b2947 := hb (x (-1) 9)
    have b2948 := hb (x (-1) 11)
    have b2949 := hb (x 0 4)
    have b2950 := hb (x 0 8)
    have b2951 := hb (x 0 10)
    have b2952 := hb (x 1 3)
    have b2953 := hb (x 1 5)
    have b2954 := hb (x 1 7)
    have b2955 := hb (x 1 9)
    have b2956 := hb (x 2 2)
    have b2957 := hb (x 2 4)
    have b2958 := hb (x 2 6)
    have b2959 := hb (x 2 8)
    have b2960 := hb (x 3 1)
    have b2961 := hb (x 3 5)
    have b2962 := hb (x 3 7)
    have b2963 := hb (x 4 4)
    have b2964 := hb (x 4 6)
    have b2965 := hb (x 5 3)
    have b2966 := hb (x 5 5)
    have b2967 := hb (x 6 2)
    have b2968 := hb (x 6 4)
    have b2969 := hb (x 6 7)
    have b2970 := hb (x 7 1)
    have b2971 := hb (x 7 3)
    have b2972 := hb (x 7 6)
    have b2973 := hb (x 8 2)
    have b2974 := hb (x 8 5)
    have b2975 := hb (x 8 10)
    have b2976 := hb (x 9 1)
    have b2977 := hb (x 9 4)
    have b2978 := hb (x 10 11)
    have b2979 := hb (x 11 10)
    have b2980 := hb (x 12 9)
    have b2981 := hb (x 13 8)
    have b2982 := hb (x 0 2 && x 0 6)
    have b2983 := hb (x (-1) 3 && x (-1) 7)
    have b2984 := hb (x (-2) 4 && x (-2) 8)
    have b2985 := hb (x (-3) 5 && x (-3) 9)
    have b2986 := hb (x (-4) 6 && x (-4) 10)
    have b2987 := hb (x (-5) 7 && x (-5) 11)
    have b2988 := hb (x (-6) 8 && x (-6) 12)
    have b2989 := hb (x (-7) 9 && x (-7) 13)
    have b2990 := hb (x 7 1 && x 7 6)
    have b2991 := hb (x 6 2 && x 6 7)
    have b2992 := hb (x 5 3 && x 5 8)
    have b2993 := hb (x 4 4 && x 4 9)
    have b2994 := hb (x 3 5 && x 3 10)
    have b2995 := hb (x 2 6 && x 2 11)
    have b2996 := hb (x 1 7 && x 1 12)
    have b2997 := hb (x 0 8 && x 0 13)
    have b2998 := hb (x (-1) 9 && x (-1) 14)
    have b2999 := hb (x 3 1 && x 3 7)
    have b3000 := hb (x 2 2 && x 2 8)
    have b3001 := hb (x 1 3 && x 1 9)
    have b3002 := hb (x 0 4 && x 0 10)
    have b3003 := hb (x (-1) 5 && x (-1) 11)
    have b3004 := hb (x (-2) 6 && x (-2) 12)
    have b3005 := hb (x (-3) 7 && x (-3) 13)
    have b3006 := hb (x (-4) 8 && x (-4) 14)
    have b3007 := hb (x 5 1 && x 5 8)
    have b3008 := hb (x 4 2 && x 4 9)
    have b3009 := hb (x 3 3 && x 3 10)
    have b3010 := hb (x 2 4 && x 2 11)
    have b3011 := hb (x 1 5 && x 1 12)
    have b3012 := hb (x 0 6 && x 0 13)
    have b3013 := hb (x (-1) 7 && x (-1) 14)
    have b3014 := hb (x (-7) 1 && x (-7) 11)
    have b3015 := hb (x (-8) 2 && x (-8) 12)
    have b3016 := hb (x (-9) 3 && x (-9) 13)
    have b3017 := hb (x (-10) 4 && x (-10) 14)
    have b3018 := hb (x (-3) 1 && x (-3) 11)
    have b3019 := hb (x (-4) 2 && x (-4) 12)
    have b3020 := hb (x (-5) 3 && x (-5) 13)
    have b3021 := hb (x (-6) 4 && x (-6) 14)
    have b3022 := hb (x 7 1 && x 7 11)
    have b3023 := hb (x 6 2 && x 6 12)
    have b3024 := hb (x 5 3 && x 5 13)
    have b3025 := hb (x 4 4 && x 4 14)
    have b3026 := hb (x 9 1 && x 9 12)
    have b3027 := hb (x 8 2 && x 8 13)
    have b3028 := hb (x 7 3 && x 7 14)
    linarith only [r2867, r2868, r2869, r2870, e2871, e2872, e2873, e2874, e2875, e2876, r2877, e2878, e2879, e2880, e2881, e2882, e2883, r2884, e2885, e2886, e2887, e2888, e2889, e2890, r2891, e2892, e2893, r2894, r2895, r2896, r2897, r2898, r2899, r2900, r2901, r2902, r2903, r2904, r2905, r2906, r2907, r2908, r2909, r2910, r2911, r2912, b2913, b2914, b2915, b2916, b2917, b2918, b2919, b2920, b2921, b2922, b2923, b2924, b2925, b2926, b2927, b2928, b2929, b2930, b2931, b2932, b2933, b2934, b2935, b2936, b2937, b2938, b2939, b2940, b2941, b2942, b2943, b2944, b2945, b2946, b2947, b2948, b2949, b2950, b2951, b2952, b2953, b2954, b2955, b2956, b2957, b2958, b2959, b2960, b2961, b2962, b2963, b2964, b2965, b2966, b2967, b2968, b2969, b2970, b2971, b2972, b2973, b2974, b2975, b2976, b2977, b2978, b2979, b2980, b2981, b2982, b2983, b2984, b2985, b2986, b2987, b2988, b2989, b2990, b2991, b2992, b2993, b2994, b2995, b2996, b2997, b2998, b2999, b3000, b3001, b3002, b3003, b3004, b3005, b3006, b3007, b3008, b3009, b3010, b3011, b3012, b3013, b3014, b3015, b3016, b3017, b3018, b3019, b3020, b3021, b3022, b3023, b3024, b3025, b3026, b3027, b3028, d2065, d2041, d2045, d1997, d2001, d1977, d1945, d1937, d1913, d1925, d1865, d2278, d1857, d1833, d1837, d2209, d2117, d1777, d1781, d1753, g0, f2683, d1681, d1457, d1465, d2724, d2807, d1485, d1513, d1629, d1553, d2755, d1577, d1621, d1609, d1601, d2803, d1749, d2843, d1853, d2863, d1917, d1993, d1585, d1633, d2177, d1517, d2222, d2077, d1725, d1501, d2823, d1469, d1413, d1757, d1845, d1541, d2173, d1657, d2218, d1461, d2799, d1721, d1953, d2037, d1801, d1909, d1581, d2751, d1549, d1605, d1573]

theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v40_51 (x : ℤ → Fin 16 → Bool)
    (hcount : ∀ u : ℤ, (x (u - 1) 1).toNat + (x (u - 2) 2).toNat + (x (u - 3) 3).toNat + (x (u - 4) 4).toNat + (x (u - 5) 5).toNat + (x (u - 6) 6).toNat + (x (u - 7) 7).toNat + (x (u - 8) 8).toNat + (x (u - 9) 9).toNat + (x (u - 10) 10).toNat + (x (u - 11) 11).toNat + (x (u - 12) 12).toNat + (x (u - 13) 13).toNat + (x (u - 14) 14).toNat = 3)
    (hd14 : ∀ u : ℤ, (x u 14).toNat + (x (u - 1) 1).toNat = 1)
    (hd12 : ∀ u : ℤ, (x u 12).toNat + (x (u - 1) 1 && x (u - 1) 13).toNat + (x (u - 2) 2 && x (u - 2) 14).toNat + (x (u - 3) 3).toNat = 1)
    (hd8 : ∀ u : ℤ, (x u 8).toNat + (x (u - 1) 1 && x (u - 1) 9).toNat + (x (u - 2) 2 && x (u - 2) 10).toNat + (x (u - 3) 3 && x (u - 3) 11).toNat + (x (u - 4) 4 && x (u - 4) 12).toNat + (x (u - 5) 5 && x (u - 5) 13).toNat + (x (u - 6) 6 && x (u - 6) 14).toNat + (x (u - 7) 7).toNat = 1)
    (hcov1 : ∀ u : ℤ, 1 ≤ (x u 1).toNat + (x (u - 1) 1 && x (u - 1) 2).toNat + (x (u - 2) 2 && x (u - 2) 3).toNat + (x (u - 3) 3 && x (u - 3) 4).toNat + (x (u - 4) 4 && x (u - 4) 5).toNat + (x (u - 5) 5 && x (u - 5) 6).toNat + (x (u - 6) 6 && x (u - 6) 7).toNat + (x (u - 7) 7 && x (u - 7) 8).toNat + (x (u - 8) 8 && x (u - 8) 9).toNat + (x (u - 9) 9 && x (u - 9) 10).toNat + (x (u - 10) 10 && x (u - 10) 11).toNat + (x (u - 11) 11 && x (u - 11) 12).toNat + (x (u - 12) 12 && x (u - 12) 13).toNat + (x (u - 13) 13 && x (u - 13) 14).toNat + (x (u - 14) 14).toNat)
    (hcov2 : ∀ u : ℤ, 1 ≤ (x u 2).toNat + (x (u - 1) 1 && x (u - 1) 3).toNat + (x (u - 2) 2 && x (u - 2) 4).toNat + (x (u - 3) 3 && x (u - 3) 5).toNat + (x (u - 4) 4 && x (u - 4) 6).toNat + (x (u - 5) 5 && x (u - 5) 7).toNat + (x (u - 6) 6 && x (u - 6) 8).toNat + (x (u - 7) 7 && x (u - 7) 9).toNat + (x (u - 8) 8 && x (u - 8) 10).toNat + (x (u - 9) 9 && x (u - 9) 11).toNat + (x (u - 10) 10 && x (u - 10) 12).toNat + (x (u - 11) 11 && x (u - 11) 13).toNat + (x (u - 12) 12 && x (u - 12) 14).toNat + (x (u - 13) 13).toNat)
    (hcov3 : ∀ u : ℤ, 1 ≤ (x u 3).toNat + (x (u - 1) 1 && x (u - 1) 4).toNat + (x (u - 2) 2 && x (u - 2) 5).toNat + (x (u - 3) 3 && x (u - 3) 6).toNat + (x (u - 4) 4 && x (u - 4) 7).toNat + (x (u - 5) 5 && x (u - 5) 8).toNat + (x (u - 6) 6 && x (u - 6) 9).toNat + (x (u - 7) 7 && x (u - 7) 10).toNat + (x (u - 8) 8 && x (u - 8) 11).toNat + (x (u - 9) 9 && x (u - 9) 12).toNat + (x (u - 10) 10 && x (u - 10) 13).toNat + (x (u - 11) 11 && x (u - 11) 14).toNat + (x (u - 12) 12).toNat)
    (hcov4 : ∀ u : ℤ, 1 ≤ (x u 4).toNat + (x (u - 1) 1 && x (u - 1) 5).toNat + (x (u - 2) 2 && x (u - 2) 6).toNat + (x (u - 3) 3 && x (u - 3) 7).toNat + (x (u - 4) 4 && x (u - 4) 8).toNat + (x (u - 5) 5 && x (u - 5) 9).toNat + (x (u - 6) 6 && x (u - 6) 10).toNat + (x (u - 7) 7 && x (u - 7) 11).toNat + (x (u - 8) 8 && x (u - 8) 12).toNat + (x (u - 9) 9 && x (u - 9) 13).toNat + (x (u - 10) 10 && x (u - 10) 14).toNat + (x (u - 11) 11).toNat)
    (hcov5 : ∀ u : ℤ, 1 ≤ (x u 5).toNat + (x (u - 1) 1 && x (u - 1) 6).toNat + (x (u - 2) 2 && x (u - 2) 7).toNat + (x (u - 3) 3 && x (u - 3) 8).toNat + (x (u - 4) 4 && x (u - 4) 9).toNat + (x (u - 5) 5 && x (u - 5) 10).toNat + (x (u - 6) 6 && x (u - 6) 11).toNat + (x (u - 7) 7 && x (u - 7) 12).toNat + (x (u - 8) 8 && x (u - 8) 13).toNat + (x (u - 9) 9 && x (u - 9) 14).toNat + (x (u - 10) 10).toNat)
    (hcov6 : ∀ u : ℤ, 1 ≤ (x u 6).toNat + (x (u - 1) 1 && x (u - 1) 7).toNat + (x (u - 2) 2 && x (u - 2) 8).toNat + (x (u - 3) 3 && x (u - 3) 9).toNat + (x (u - 4) 4 && x (u - 4) 10).toNat + (x (u - 5) 5 && x (u - 5) 11).toNat + (x (u - 6) 6 && x (u - 6) 12).toNat + (x (u - 7) 7 && x (u - 7) 13).toNat + (x (u - 8) 8 && x (u - 8) 14).toNat + (x (u - 9) 9).toNat)
    (hcov7 : ∀ u : ℤ, 1 ≤ (x u 7).toNat + (x (u - 1) 1 && x (u - 1) 8).toNat + (x (u - 2) 2 && x (u - 2) 9).toNat + (x (u - 3) 3 && x (u - 3) 10).toNat + (x (u - 4) 4 && x (u - 4) 11).toNat + (x (u - 5) 5 && x (u - 5) 12).toNat + (x (u - 6) 6 && x (u - 6) 13).toNat + (x (u - 7) 7 && x (u - 7) 14).toNat + (x (u - 8) 8).toNat)
    (hcov9 : ∀ u : ℤ, 1 ≤ (x u 9).toNat + (x (u - 1) 1 && x (u - 1) 10).toNat + (x (u - 2) 2 && x (u - 2) 11).toNat + (x (u - 3) 3 && x (u - 3) 12).toNat + (x (u - 4) 4 && x (u - 4) 13).toNat + (x (u - 5) 5 && x (u - 5) 14).toNat + (x (u - 6) 6).toNat)
    (hcov10 : ∀ u : ℤ, 1 ≤ (x u 10).toNat + (x (u - 1) 1 && x (u - 1) 11).toNat + (x (u - 2) 2 && x (u - 2) 12).toNat + (x (u - 3) 3 && x (u - 3) 13).toNat + (x (u - 4) 4 && x (u - 4) 14).toNat + (x (u - 5) 5).toNat)
    (hcov11 : ∀ u : ℤ, 1 ≤ (x u 11).toNat + (x (u - 1) 1 && x (u - 1) 12).toNat + (x (u - 2) 2 && x (u - 2) 13).toNat + (x (u - 3) 3 && x (u - 3) 14).toNat + (x (u - 4) 4).toNat)
    (hcov13 : ∀ u : ℤ, 1 ≤ (x u 13).toNat + (x (u - 1) 1 && x (u - 1) 14).toNat + (x (u - 2) 2).toNat)
    (hp2 : ∀ p, x p 2 = true → x p 14 = true)
    (hp4 : ∀ p, x p 4 = true → x p 12 = true)
    (hp5 : ∀ p, x p 5 = true → x p 13 = true)
    (hp6 : ∀ p, x p 6 = true → x p 14 = true)
    (hp9 : ∀ p, x p 9 = true → x p 1 = true)
    (hp10 : ∀ p, x p 10 = true → x p 2 = true)
    (hp11 : ∀ p, x p 11 = true → x p 3 = true)
    (hp13 : ∀ p, x p 13 = true → x p 1 = true)
    (h114 : ∀ p, x p 1 = x p 14)
    (h23 : ∀ p, x p 2 = x p 3)
    (g0 : (x 0 4).toNat = 0) (g1 : (x 0 5).toNat = 1) : False := cycle_power_fifteen_tight_type_sequence_shape_rules_core_v40_51_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 h114 h23 g0 g1
