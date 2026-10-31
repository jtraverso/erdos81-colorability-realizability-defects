/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Corollary 3.2a (private-witness cover defect), v0.9.15 candidate.

At the `H[X_C]` level (distinct private witnesses of an inclusion-minimal resource cover give
`|X_C| = |C|`, i.e. `card V = |C|`), the cover-versus-packing defect is bounded below by the
colourability defect. Immediate from Corollary 3.2 (`splitting_half`).
-/
module

public import PaperV.Core

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Corollary 3.2a.** `∃` feasible packing `S` with `|V| − 2|S| ≤ oct H`. In the triangle system
(resources = edges) with `card V = |C|` this is `τ₃(G) − 2ν₃(G) ≤ oct(H[X_C])`. -/
theorem cover_defect_lower (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∃ S : Finset V, Feasible H S ∧ Fintype.card V - 2 * S.card ≤ oct H := by
  obtain ⟨S, hS, hcard⟩ := splitting_half H
  exact ⟨S, hS, by omega⟩

/-- **Corollary 3.2b (rigidity at equality), core content.** If `q` feasible sets have sizes
summing to `q·ν`, where `ν` bounds every feasible set (the packing number), then all `q` sets are
maximum: `|Sᵢ| = ν`. Applied to the colour classes of a proper `q`-colouring of `H[X_C] − O` at the
equality `D_q = |C| − qν` (sizes summing to `|X_C| − |O| = qν`): every optimal deletion + colouring
splits the surviving witnesses into `q` maximum feasible packings. -/
theorem rigidity_at_equality (H : SimpleGraph V) [DecidableRel H.Adj]
    {ν q : ℕ} (hν : ∀ S : Finset V, Feasible H S → S.card ≤ ν)
    (S : Fin q → Finset V) (hfeas : ∀ i, Feasible H (S i))
    (hsum : (∑ i, (S i).card) = q * ν) :
    ∀ i, (S i).card = ν := by
  have hle : ∀ i, (S i).card ≤ ν := fun i => hν _ (hfeas i)
  have hconst : (∑ _i : Fin q, ν) = q * ν := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsum' : (∑ i, (S i).card) = (∑ _i : Fin q, ν) := by rw [hsum, hconst]
  have hpt := (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hsum'
  intro i; exact hpt i (Finset.mem_univ i)

end PaperV
