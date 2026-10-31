/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — N1: copy triple bound.

Corollary of `copy_integral` (Thm 4.2) + `oct_le_third_of_cubic` (Brooks):
  ν₃(G_{v→u}) + ν₃(G_{u→v}) ≤ 3·ν₃(G),   tight at K₄ ⊔ K₄.

`copy_triple_bound_of` is the UNCONDITIONAL arithmetic core: given the witness multiset `T₂`
of `copy_integral` together with the structural Claim 4.1a/b for that specific `T₂` — its
conflict graph `H[T₂]` is subcubic (Δ ≤ 3) and K₄-free — the triple bound follows by
`oct_le_third_of_cubic` and integer arithmetic.  The structural facts for the `T₂` built inside
`copy_integral` are packaged in `copy_integral_struct`.
-/
module

public import PaperV.Copy
public import PaperV.BrooksOct

import Lean.Elab.Tactic.Omega

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **N1 arithmetic core (unconditional).** For an explicit witness multiset `T₂` with
`multSize = ν₃(G_{v→u}) + ν₃(G_{u→v})`, the transfer bound `S ≤ 2·ν₃G + oct(H[T₂])`, and the
structural facts that `H[T₂]` is subcubic and K₄-free, we get `S ≤ 3·ν₃G`. -/
theorem copy_triple_bound_of (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V)
    (T₂ : (triCS G).O → ℕ)
    (hsize : multSize (triCS G) T₂ = nu3 (copyGraph G v u) + nu3 (copyGraph G u v))
    (hbound : nu3 (copyGraph G v u) + nu3 (copyGraph G u v)
        ≤ 2 * nu3 G + oct (Hgraph (triCS G) T₂))
    (hΔ : (Hgraph (triCS G) T₂).maxDegree ≤ 3)
    (hK4 : (Hgraph (triCS G) T₂).CliqueFree 4) :
    nu3 (copyGraph G v u) + nu3 (copyGraph G u v) ≤ 3 * nu3 G := by
  have hoct := oct_le_third_of_cubic (Hgraph (triCS G) T₂) hΔ hK4
  rw [card_copies] at hoct
  rw [hsize] at hoct
  -- hbound : S ≤ 2·ν₃G + oct ;  hoct : oct ≤ S / 3 ;  goal : S ≤ 3·ν₃G
  omega

/-- **N1 (Corollary of Thm 4.2 + Brooks).** For any non-edge `u,v` of `G`,
`ν₃(G_{v→u}) + ν₃(G_{u→v}) ≤ 3·ν₃(G)`.  Tight at `K₄ ⊔ K₄`. -/
theorem copy_triple_bound (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V)
    (huv : ¬ G.Adj u v) :
    nu3 (copyGraph G v u) + nu3 (copyGraph G u v) ≤ 3 * nu3 G := by
  obtain ⟨T₂, hsize, hbound, hΔ, hK4⟩ := copy_integral_struct G v u huv
  exact copy_triple_bound_of G v u T₂ hsize hbound hΔ hK4

end PaperV
