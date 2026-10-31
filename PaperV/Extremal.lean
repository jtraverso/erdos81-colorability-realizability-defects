/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Extremal characterisation of the splitting bound (v0.9.15 candidate).

The splitting principle gives a packing of size `≥ ⌈(|V| − D_q(H))/q⌉` (`SplittingQ.splitting_ceil`).
Dually, if `ν` bounds every feasible packing then `|V| − q·ν ≤ D_q(H)` (`Dq_ge_card_sub`): the defect
cannot be smaller than the deficit `|V| − q·ν`. These two bounds SANDWICH `D_q`, and the extremal
(tight) case `D_q(H) = |V| − q·ν` forces every optimal `q`-colouring of the surviving witnesses to
split them into `q` maximum feasible packings (`defect_tight_all_max`, via `rigidity_at_equality`).
-/
module

public import PaperV.Core
public import PaperV.SplittingQ
public import PaperV.CoverDefect

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Extremal lower bound on the defect.** If `ν` bounds every feasible packing, then
`|V| − q·ν ≤ D_q(H)`. Dual to the splitting upper bound `ν ≥ ⌈(|V|−D_q)/q⌉`; the `q` colour classes
of an optimal colouring cover `|V| − D_q` witnesses with `q` sets each of size `≤ ν`. -/
theorem Dq_ge_card_sub (H : SimpleGraph V) [DecidableRel H.Adj] {ν q : ℕ} (hq : 1 ≤ q)
    (hν : ∀ S : Finset V, Feasible H S → S.card ≤ ν) :
    Fintype.card V - q * ν ≤ Dq H q := by
  obtain ⟨S, hfeas, _hdisj, hcard⟩ := SplittingQ.splitting_q H q hq
  have hsum_le : ∑ i, (S i).card ≤ q * ν := by
    calc ∑ i, (S i).card ≤ ∑ _i : Fin q, ν := Finset.sum_le_sum (fun i _ => hν _ (hfeas i))
      _ = q * ν := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- **Extremal equality characterisation.** When the defect saturates its lower bound,
`D_q(H) = |V| − q·ν` (with `q·ν ≤ |V|`), every optimal `q`-colouring of `H − O` splits the surviving
witnesses into `q` pairwise-disjoint feasible packings **all of maximum size `ν`**. Combines the
`SplittingQ.splitting_q` partition with `rigidity_at_equality`. -/
theorem defect_tight_all_max (H : SimpleGraph V) [DecidableRel H.Adj] {ν q : ℕ} (hq : 1 ≤ q)
    (hν : ∀ S : Finset V, Feasible H S → S.card ≤ ν) (hle : q * ν ≤ Fintype.card V)
    (htight : Dq H q = Fintype.card V - q * ν) :
    ∃ S : Fin q → Finset V, (∀ i, Feasible H (S i)) ∧
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧ (∀ i, (S i).card = ν) := by
  obtain ⟨S, hfeas, hdisj, hcard⟩ := SplittingQ.splitting_q H q hq
  have hsum_le : ∑ i, (S i).card ≤ q * ν := by
    calc ∑ i, (S i).card ≤ ∑ _i : Fin q, ν := Finset.sum_le_sum (fun i _ => hν _ (hfeas i))
      _ = q * ν := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsum_eq : ∑ i, (S i).card = q * ν := by omega
  exact ⟨S, hfeas, hdisj, rigidity_at_equality H hν S hfeas hsum_eq⟩

/-- **Extremal equality, reverse direction.** If some defect set `O` leaves exactly `q·ν` survivors,
the defect saturates its lower bound: `D_q(H) = |V| − q·ν`. Together with `defect_tight_all_max` this
closes the characterisation: the bound is tight iff an optimal deletion leaves `q` maximum classes. -/
theorem defect_eq_of_survivors (H : SimpleGraph V) [DecidableRel H.Adj] {ν q : ℕ} (hq : 1 ≤ q)
    (hν : ∀ S : Finset V, Feasible H S → S.card ≤ ν)
    (O : Finset V) (hO : IsDefectSet H q O) (hsurv : Fintype.card V - O.card = q * ν) :
    Dq H q = Fintype.card V - q * ν := by
  have hge := Dq_ge_card_sub H hq hν
  have hle : Dq H q ≤ O.card := Nat.sInf_le ⟨O, hO, rfl⟩
  have hOle : O.card ≤ Fintype.card V := Finset.card_le_univ O
  omega

end PaperV
