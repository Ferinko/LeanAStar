/-
Copyright (c) 2022 František Silváši. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši
-/

import Std.Data.HashSet

import Mathlib.Data.BinaryHeap
import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Algebra.Order

import LeanAStar.Wheels
import LeanAStar.AStar

namespace ex 

structure point where
  data : Nat × Nat
deriving BEq, Hashable, Repr

private def point.toString : point → String
  | ⟨(x, y)⟩ => s!"({x}, {y})"

instance : ToString point := ⟨point.toString⟩

def graph : point → Std.HashSet point
  | p@⟨(x, y)⟩ =>
  Std.HashSet.empty.insertMany <| #[
    ⟨x + 1, y⟩, ⟨x - 1, y⟩,
    ⟨x, y + 1⟩, ⟨x, y - 1⟩
  ].filter (λ ⟨x, y⟩ => x ≤ 10 ∧ y ≤ 10 ∧ ¬p == ⟨(x, y)⟩)

def euclid : point → point → Float
  | ⟨(x₁, y₁)⟩, ⟨(x₂, y₂)⟩ =>
    let xΔ : Float := x₂.toFloat - x₁.toFloat
    let yΔ : Float := y₂.toFloat - y₁.toFloat
    (xΔ * xΔ + yΔ * yΔ).sqrt

instance : LinearOrder point := {
  le := λ ⟨(x₁, y₁)⟩ ⟨(x₂, y₂)⟩ => if x₁ < x₂ then True else if x₂ < x₁ then False else y₁ ≤ y₂
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_le := sorry
  le_antisymm := sorry
  le_total := sorry
  decidable_eq := λ ⟨(x₁, y₁)⟩ ⟨(x₂, y₂)⟩ => by simp; exact inferInstance
  decidable_le := λ ⟨(x₁, y₁)⟩ ⟨(x₂, y₂)⟩ => by simp [LE.le]; exact inferInstance
}

instance : AddMonoid Float := {
  add_assoc := sorry -- technically only true for ℝ and not Float but don't tell Lean
  add_zero := sorry
  zero_add := sorry
  nsmul_zero' := sorry
  nsmul_succ' := sorry
}

-- #eval AStar.AStar graph euclid ⟨(0, 0)⟩ ⟨(10, 10)⟩ (euclid ⟨(10, 10)⟩)
-- #[{ data := (10, 10) }, { data := (9, 10) }, { data := (8, 10) }, { data := (7, 10) }, { data := (6, 10) },
--   { data := (5, 10) }, { data := (4, 10) }, { data := (3, 10) }, { data := (2, 10) }, { data := (1, 10) },
--   { data := (0, 10) }, { data := (0, 9) }, { data := (0, 8) }, { data := (0, 7) }, { data := (0, 6) },
--   { data := (0, 5) }, { data := (0, 4) }, { data := (0, 3) }, { data := (0, 2) }, { data := (0, 1) }]

end ex