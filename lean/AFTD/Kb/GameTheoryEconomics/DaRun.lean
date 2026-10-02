import AFTD.Prelude

/-!
# da_run

Topic: matching_markets   Node: 48cc1eae1219

One run of men-proposing deferred acceptance with a step budget: each step the first free man with proposals left proposes to his next woman, who keeps whichever of him and her current man she ranks better.
-/

/-- One run of men-proposing deferred acceptance with a step budget. `rm m w` is the rank man `m` gives woman `w` and `rw w m` the rank woman `w` gives man `m` (0 = best). `hold w` is the man woman `w` currently holds and `nxt m` how many proposals man `m` has made. Each step, the first free man with proposals left proposes to the woman he ranks `nxt m`; she keeps whichever of him and her current man she ranks better. -/
def da_run {nm nw : ℕ} (rm : Fin nm → Fin nw → Fin nw) (rw : Fin nw → Fin nm → Fin nm)
    (fuel : ℕ) (hold : Fin nw → Option (Fin nm)) (nxt : Fin nm → ℕ) : Fin nw → Option (Fin nm) :=
  match fuel with
  | 0 => hold
  | fuel + 1 =>
    match (List.finRange nm).find? (fun m =>
        decide (nxt m < nw) && (List.finRange nw).all (fun w => hold w != some m)) with
    | none => hold
    | some m =>
      match (List.finRange nw).find? (fun w => ((rm m w : ℕ) == nxt m)) with
      | none => hold
      | some w =>
        let nxt' := Function.update nxt m (nxt m + 1)
        match hold w with
        | none => da_run rm rw fuel (Function.update hold w (some m)) nxt'
        | some m' =>
          if rw w m < rw w m' then da_run rm rw fuel (Function.update hold w (some m)) nxt'
          else da_run rm rw fuel hold nxt'
