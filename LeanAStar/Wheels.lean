/-
Copyright (c) 2022 František Silváši. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši
-/

import Mathlib.Logic.Basic

import Std.Data.HashMap

namespace Wheels

def option {α} (self? : Option α) (default : β) (f : α → β) : β :=
  match self? with
    | none => default
    | some self => f self

end Wheels

def Std.HashSet.insertMany {α} [BEq α] [Hashable α] (self : Std.HashSet α) (arr : Array α) : Std.HashSet α :=
  arr.foldl (·.insert ·) self

def Std.HashMap.keys {α} [BEq α] [Hashable α] {β} (self : Std.HashMap α β) : Array α :=
  self.fold (init := #[]) λ st k _ => st.push k