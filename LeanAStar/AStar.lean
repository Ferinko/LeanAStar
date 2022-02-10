/-
Copyright (c) 2022 František Silváši. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši
-/

import Mathlib.Data.BinaryHeap
import Mathlib.Init.Algebra.Order
import Mathlib.Algebra.Group.Defs

import Std.Data.HashMap
import Std.Data.HashSet

import LeanAStar.Wheels

namespace AStar  

section AStar

variable {NodeT} 
variable [BEq NodeT] [Hashable NodeT] [LinearOrder NodeT]

variable {CostT}
variable [LT CostT] [∀ {x y : CostT}, Decidable <| LT.lt x y] [AddMonoid CostT]

/-- Mathlib.Data.BinaryHeap implements MaxHeap with custom ordering.
Using ≥ essentially turns it into a MinHeap as we want the least cost as the root. -/
abbrev NodeHeap := BinaryHeap NodeT (·≥·)

open Wheels

private partial def tracePathAux (preds : Std.HashMap NodeT NodeT)
                                 (result : Array NodeT)
                                 (node : NodeT) : Array NodeT :=
  let keys := preds.fold (init := #[]) λ st k _ => st.push k
  if h : ¬keys.contains node then result
  else option (preds.find? node) result <| tracePathAux preds <| result.push node

private def tracePath (preds : Std.HashMap NodeT NodeT) (node : NodeT) : Array NodeT :=
  tracePathAux preds #[] node

/-- Based on https://en.wikipedia.org/wiki/A*_search_algorithm -/
private partial def AStarAux (g : NodeT → Std.HashSet NodeT)
                             (Δ : NodeT → NodeT → CostT)
                             (ω : NodeT)
                             (h : NodeT → CostT)
                             (βs : @NodeHeap NodeT _)
                             (preds : Std.HashMap NodeT NodeT)
                             (gCost : Std.HashMap NodeT CostT)
                             (fCost : Std.HashMap NodeT CostT) : Array NodeT :=
  let ⟨β?, βs⟩ := βs.extractMax
  option β? #[] λ β =>
  if β = ω then tracePath preds β
  else let (preds', gCost', fCost', βs') :=
    (g β).fold (init := (preds, gCost, fCost, βs)) λ
      st@(preds, gCost, fCost, βs) neigh =>
      option (gCost.find? β) st (
        let newCost := · + Δ β neigh
        let st' := (preds.insert neigh β,
                    gCost.insert neigh newCost,
                    fCost.insert neigh <| newCost + h neigh,
                    if βs.arr.contains neigh then βs else βs.insert neigh)
        option (gCost.find? neigh) st' (if newCost < · then st' else st)
      )
    AStarAux g Δ ω h βs' preds' gCost' fCost'

open Std.HashMap in
/-- 
  g : NodeT → HashSet NodeT - the graph given as an adjacency function
  Δ : NodeT → NodeT → CostT - distance between two neighbours 
  α : NodeT                 - starting node
  ω : NodeT                 - finishing node
  h : NodeT → DistT         - function estimating the distance to goal from any node
-/
def AStar (g : NodeT → Std.HashSet NodeT) (Δ : NodeT → NodeT → CostT) (α ω : NodeT) (h : NodeT → CostT) : Array NodeT :=
  AStarAux g Δ ω h (BinaryHeap.empty (·≥·) |>.insert α) empty (empty.insert α 0) (empty.insert α <| h α)

end AStar

end AStar