/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Proposition 6.2, combinatorial content (termination count of improving repairs).

  * pair uniqueness ⇒ `Assign.ends` is injective on a feasible packing, hence
    `|R| ≤ |cov|` whenever every used pair is coverable (`card_le_cov`);
  * an accepted repair strictly increases `|R|` and lands on a feasible, coverable packing
    (`AcceptedRepair`);
  * therefore any chain of `k` accepted repairs has `k ≤ |cov|` (`accepted_repairs_le_cov`).

The polynomial running time of the scan between repairs is an implementation statement and is
deliberately NOT formalized (manuscript only), as the paper states.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.Seal

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Set

public import Mathlib.Data.Finset.Card

@[expose] public section

open Finset

namespace PaperV

variable {J W : Type*} [DecidableEq J] [DecidableEq W]

/-- On a feasible packing, the pair map `ends` is injective (pair uniqueness + per-host matching). -/
theorem ends_injOn_of_feasible {R : Finset (Assign J W)} (hR : SealFeasible R) :
    Set.InjOn Assign.ends (R : Set (Assign J W)) := by
  intro x hx y hy hxy
  by_contra hne
  have hhost := hR.2 x hx y hy hxy
  have hdis := hR.1 x hx y hy hne hhost
  have hmem : x.a ∈ x.ends ∩ y.ends := by
    rw [Finset.mem_inter]
    refine ⟨by simp [Assign.ends], ?_⟩
    rw [← hxy]; simp [Assign.ends]
  rw [hdis] at hmem
  exact Finset.notMem_empty _ hmem

/-- **Pair-uniqueness bound.** A feasible packing whose pairs all lie in the coverable set `cov`
has at most `|cov|` assignments. -/
theorem card_le_cov {R : Finset (Assign J W)} (hR : SealFeasible R) (cov : Finset (Finset W))
    (hcov : ∀ x ∈ R, x.ends ∈ cov) : R.card ≤ cov.card := by
  rw [← Finset.card_image_of_injOn (ends_injOn_of_feasible hR)]
  apply Finset.card_le_card
  intro e he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  exact hcov x hx

/-- An **accepted repair** from `R` to `R'`: the result is feasible, uses only coverable pairs, and
strictly increases the cardinality (the acceptance rule of Phase 3). -/
def AcceptedRepair (cov : Finset (Finset W)) (R R' : Finset (Assign J W)) : Prop :=
  SealFeasible R' ∧ (∀ x ∈ R', x.ends ∈ cov) ∧ R.card < R'.card

/-- Along a chain of accepted repairs the cardinality grows at least linearly. -/
theorem card_chain (cov : Finset (Finset W)) (R : ℕ → Finset (Assign J W)) (k : ℕ)
    (h : ∀ i < k, AcceptedRepair cov (R i) (R (i + 1))) :
    ∀ n ≤ k, (R 0).card + n ≤ (R n).card := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h1 := ih (Nat.le_of_succ_le hm)
    have h2 := (h m hm).2.2
    omega

/-- **Proposition 6.2 (combinatorial content).** A chain of `k` accepted repairs has `k ≤ |cov|`. -/
theorem accepted_repairs_le_cov (cov : Finset (Finset W)) (R : ℕ → Finset (Assign J W)) (k : ℕ)
    (h : ∀ i < k, AcceptedRepair cov (R i) (R (i + 1))) : k ≤ cov.card := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Nat.zero_le _
  · have hlast := card_chain cov R k h k le_rfl
    have hstep := h (k - 1) (by omega)
    have hk' : k - 1 + 1 = k := by omega
    rw [hk'] at hstep
    have hbound := card_le_cov hstep.1 cov hstep.2.1
    omega

/-- Sharper form: `|R 0| + k ≤ |cov|`, i.e. `k ≤ u` for the audit quantity `u = |cov| − |R|` of the
manuscript (the start packing is assumed feasible and coverable, as produced by Phases 1–2). -/
theorem accepted_repairs_le_audit (cov : Finset (Finset W)) (R : ℕ → Finset (Assign J W)) (k : ℕ)
    (hR0 : SealFeasible (R 0)) (hcov0 : ∀ x ∈ R 0, x.ends ∈ cov)
    (h : ∀ i < k, AcceptedRepair cov (R i) (R (i + 1))) : (R 0).card + k ≤ cov.card := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using card_le_cov hR0 cov hcov0
  · have hlast := card_chain cov R k h k le_rfl
    have hstep := h (k - 1) (by omega)
    have hk' : k - 1 + 1 = k := by omega
    rw [hk'] at hstep
    have hbound := card_le_cov hstep.1 cov hstep.2.1
    omega

end PaperV
