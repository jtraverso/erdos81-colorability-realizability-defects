/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import BrooksLib.Brooks

/-!
# Brooks' theorem, cubic case

A finite simple graph with maximum degree at most `3` and no `4`-clique is `3`-colourable. This is
the case `k = 3` of Brooks' theorem in the registered entry `jtraverso/brooks`
(PALOMAR-2026-10-16-000003), which replaces the self-contained proof of the Paper V freeze.
-/

@[expose] public section

namespace PaperV.Brooks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Brooks' theorem, cubic case (B9).** A finite simple graph with maximum degree `≤ 3` and no
4-clique is 3-colourable. -/
theorem brooks_cubic (G : SimpleGraph V) [DecidableRel G.Adj]
    (hΔ : G.maxDegree ≤ 3) (hK4 : G.CliqueFree 4) : G.Colorable 3 :=
  BrooksTheorem.colorable_of_cliqueFree G 3 le_rfl hΔ hK4

end PaperV.Brooks
