/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V v1.8: explicit manuscript interfaces beyond the numerical core.
An optimum is a feasible point with its maximality property; no conclusion of
the transfer theorem is assumed in this interface.
-/
module

public import PaperV.ConflictGraph
public import PaperV.CoverDefect

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Set

public import Mathlib.Basic.Real.Basic

@[expose] public section

open Finset SimpleGraph

namespace PaperV
namespace Manuscript

variable (C : ConflictSystem)

/-- Data and hypotheses of a resource-dominated relaxation. The feasible set may
in particular be any polytope satisfying Definition 2.5. Convexity is not used. -/
structure ResourceRelaxation where
  Resource : Type
  [finiteResource : Fintype Resource]
  [decResource : DecidableEq Resource]
  resources : C.O → Finset Resource
  conflicts : ∀ a b, C.K a b ↔ a ≠ b ∧ ¬ Disjoint (resources a) (resources b)
  feasible : Set (C.O → ℝ)
  nonneg : ∀ x ∈ feasible, ∀ o, 0 ≤ x o
  capacity : ∀ x ∈ feasible, ∀ e,
    ∑ o ∈ Finset.univ.filter (fun o => e ∈ resources o), x o ≤ 1
  integral_iff : ∀ S : Finset C.O,
    (fun o => if o ∈ S then (1 : ℝ) else 0) ∈ feasible ↔ CSFeasible C S

attribute [instance] ResourceRelaxation.finiteResource ResourceRelaxation.decResource

variable {C}

/-- The actual maximizing point, rather than an unexplained scalar optimum. -/
structure ResourceRelaxation.Optimum (P : ResourceRelaxation C) where
  point : C.O → ℝ
  feasible : point ∈ P.feasible
  maximal : ∀ y ∈ P.feasible, ∑ o, y o ≤ ∑ o, point o

def ResourceRelaxation.Optimum.value {P : ResourceRelaxation C} (x : P.Optimum) : ℝ :=
  ∑ o, x.point o

theorem ResourceRelaxation.point_le_one (P : ResourceRelaxation C)
    {x : C.O → ℝ} (hx : x ∈ P.feasible) (o : C.O)
    (ho : (P.resources o).Nonempty) : x o ≤ 1 := by
  obtain ⟨e, he⟩ := ho
  have hm : o ∈ Finset.univ.filter (fun a => e ∈ P.resources a) := by simp [he]
  exact (Finset.single_le_sum (fun a _ => P.nonneg x hx a) hm).trans (P.capacity x hx e)

/-- Theorem 3.4 with an explicit relaxation, optimizing point and q-integral copy map. -/
theorem resource_integral_transfer (P : ResourceRelaxation C) (x : P.Optimum)
    {q : ℕ} (hq : 0 < q) {X : C.O → ℕ}
    (hX : ∀ o, (q : ℝ) * x.point o = (X o : ℝ)) (hbounded : ∀ o, x.point o ≤ 1) :
    IsQMultiset C X q ∧
      x.value - (nu C : ℝ) ≤ (Dq (Hgraph C X) q : ℝ) / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcopies : IsQMultiset C X q := by
    intro o
    have ho : (X o : ℝ) ≤ q := by
      rw [← hX o]
      nlinarith [hbounded o]
    exact_mod_cast ho
  have hsize : (multSize C X : ℝ) = (q : ℝ) * ∑ o, x.point o := by
    unfold multSize
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun o _ => (hX o).symm)
  have ht := transfer_q C X q hq hcopies
  have htR : (multSize C X : ℝ) ≤ (q : ℝ) * (nu C : ℝ) + (Dq (Hgraph C X) q : ℝ) := by
    exact_mod_cast ht
  rw [hsize] at htR
  refine ⟨hcopies, ?_⟩
  change (∑ o, x.point o) - (nu C : ℝ) ≤ _
  have hcancel : (Dq (Hgraph C X) q : ℝ) / q * (q : ℝ) = (Dq (Hgraph C X) q : ℝ) :=
    div_mul_cancel₀ _ hqR.ne'
  nlinarith

/-- Theorem 3.3 is the q=2 specialization for the same actual relaxation. -/
theorem resource_half_integral_transfer (P : ResourceRelaxation C) (x : P.Optimum)
    {X : C.O → ℕ} (hX : ∀ o, (2 : ℝ) * x.point o = (X o : ℝ))
    (hbounded : ∀ o, x.point o ≤ 1) :
    IsQMultiset C X 2 ∧ x.value - (nu C : ℝ) ≤ (oct (Hgraph C X) : ℝ) / 2 := by
  simpa [oct] using resource_integral_transfer P x (by norm_num : 0 < 2) hX hbounded

section Rigidity

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

def remainingClass (Z : Finset V) {q : ℕ} (c : V → Fin q) (i : Fin q) : Finset V :=
  Finset.univ.filter (fun v => v ∉ Z ∧ c v = i)

theorem remainingClass_partition (Z : Finset V) {q : ℕ} (c : V → Fin q) :
    ∑ i, (remainingClass Z c i).card = (Finset.univ \ Z).card := by
  classical
  rw [← Finset.card_biUnion]
  · congr 1
    ext v
    simp [remainingClass]
  · intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, remainingClass, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro v hi hj
    exact hij (hi.2.symm.trans hj.2)

/-- Corollary 3.2b, for every chosen minimum deletion set and every proper
coloring of its complement. The converse is included in the same equivalence.
The additive equality is the integer-safe form of D_q = |V| - q*nu. -/
theorem minimum_coloring_rigidity_iff
    {q ν : ℕ} (hν : ∀ S : Finset V, Feasible H S → S.card ≤ ν)
    (Z : Finset V) (hmin : Z.card = Dq H q) (c : V → Fin q)
    (hc : ∀ a ∉ Z, ∀ b ∉ Z, H.Adj a b → c a ≠ c b) :
    Dq H q + q * ν = Fintype.card V ↔
      ∀ i, (remainingClass Z c i).card = ν := by
  classical
  have hfeas : ∀ i, Feasible H (remainingClass Z c i) := by
    intro i a ha b hb hab
    simp only [remainingClass, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact hc a ha.1 b hb.1 hab (ha.2.trans hb.2.symm)
  have hsplit : (∑ i, (remainingClass Z c i).card) + Z.card = Fintype.card V := by
    rw [remainingClass_partition]
    simpa only [Finset.card_univ] using
      (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Z))
  constructor
  · intro heq
    apply rigidity_at_equality H hν (remainingClass Z c) hfeas
    omega
  · intro hclasses
    have hs : (∑ i, (remainingClass Z c i).card) = q * ν := by simp [hclasses]
    omega

end Rigidity
end Manuscript
end PaperV
