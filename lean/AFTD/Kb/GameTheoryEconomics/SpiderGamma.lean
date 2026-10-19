import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.SpiderRhoStar
import AFTD.Kb.GameTheoryEconomics.SpiderUpdateCentre
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd

/-!
# spider_gamma

Topic: combinatorial_games   Node: 2a81e5b53d86

Provenance: formalization of a published result. Source: scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md, Proposition 6.1

The function spider_gamma computes a natural number from a fuel parameter fuel : ℕ, a centre status s : CentreStatus, and a list of spider legs L : List (ℕ × SpiderLegEnd). It is defined by recursion on fuel: if fuel = 0, it returns 0. If fuel = fuel' + 1: if s = CentreStatus.free, it returns the bitwise XOR sum starting from 0 of spider_rho_star h phi for each (h, phi) in L. Otherwise, if L is empty, it returns 0; if L is a singleton [(h, phi)], it returns spider_rho h SpiderLegEnd.outward phi if s = CentreStatus.incoming, spider_rho h SpiderLegEnd.inward phi if s = CentreStatus.outgoing, and 0 if s = CentreStatus.none; if L has at least two elements, it returns nat_mex_list of options collected over each leg (h, phi) at index idx in L, with rest = L.eraseIdx idx, each integer j from 1 to h, and each direction delta in {SpiderLegEnd.inward, SpiderLegEnd.outward}: skipping when j = h, phi ≠ SpiderLegEnd.free, and delta ≠ phi; otherwise letting d = spider_rho (h - j) delta phi and taking d ^^^ spider_gamma fuel' s ((j - 1, delta) :: rest) if j ≥ 2, and d ^^^ spider_gamma fuel' (spider_update_centre s delta) rest if j = 1.
-/

/-- Grundy value Γ(s; L) of a spider state with centre status s and attached legs L. -/
def spider_gamma (fuel : ℕ) (s : CentreStatus) (L : List (ℕ × SpiderLegEnd)) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    match s with
    | .free => L.foldl (fun acc p => acc ^^^ spider_rho_star p.1 p.2) 0
    | _ =>
      match L with
      | [] => 0
      | [(h, phi)] =>
        match s with
        | .incoming => spider_rho h .outward phi
        | .outgoing => spider_rho h .inward phi
        | _ => 0
      | _ =>
        let options : List ℕ :=
          L.zipIdx.flatMap (fun ⟨⟨h, phi⟩, idx⟩ =>
            let rest := L.eraseIdx idx
            (List.range h).flatMap (fun j_zero =>
              let j := j_zero + 1
              [SpiderLegEnd.inward, SpiderLegEnd.outward].filterMap (fun delta =>
                if j == h ∧ phi ≠ .free ∧ delta ≠ phi then none
                else
                  let d := spider_rho (h - j) delta phi
                  if j ≥ 2 then
                    let new_L := (j - 1, delta) :: rest
                    some (d ^^^ spider_gamma fuel s new_L)
                  else
                    let new_s := spider_update_centre s delta
                    some (d ^^^ spider_gamma fuel new_s rest)
              )
            )
          )
        nat_mex_list options
