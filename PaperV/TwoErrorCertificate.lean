/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V v1.8, Corollary 4.6: rational resource LP and physical realization.
The certificate partitions occurrence multiplicities, not merely total values.
The output is a genuinely resource-disjoint packing in the same resource system.
-/
module

public import PaperV.RationalLP
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.NormCast

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

open Finset

namespace PaperV
namespace ResourceCertificate

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

/-- A finite physical resource system; each object consumes a nonempty set. -/
structure System (I E : Type*) [Fintype I] [Fintype E] [DecidableEq E] where
  resources : I → Finset E
  nonempty : ∀ o, (resources o).Nonempty

namespace System

variable (R : System I E)

def incidence (o : I) (e : E) : ℚ := if e ∈ R.resources o then 1 else 0

/-- Distinct selected objects consume disjoint physical resources. -/
def Packing (S : Finset I) : Prop :=
  ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ S → a ≠ b → Disjoint (R.resources a) (R.resources b)

def gain (_R : System I E) (w : I → ℚ) (S : Finset I) : ℚ := ∑ o ∈ S, w o

def mass (_R : System I E) (w : I → ℚ) (X : I → ℕ) : ℚ := ∑ o, w o * X o

/-- The incidence-vector primal associated to a physical packing. -/
def packingPrimal (S : Finset I) (hS : R.Packing S) :
    FiniteLP.PrimalFeasible R.incidence where
  weight o := if o ∈ S then 1 else 0
  weight_nonneg o := by split <;> norm_num
  capacity e := by
    classical
    let T := S.filter (fun o => e ∈ R.resources o)
    have hT : T.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      by_contra hab
      exact Finset.disjoint_left.mp (hS ha'.1 hb'.1 hab) ha'.2 hb'.2
    have heq : (∑ o, R.incidence o e * (if o ∈ S then (1 : ℚ) else 0)) = T.card := by
      simp [incidence, T, Finset.sum_filter, Finset.sum_ite_mem, mul_ite, ite_mul]
    rw [heq]
    exact_mod_cast hT

theorem packingPrimal_value (w : I → ℚ) (S : Finset I) (hS : R.Packing S) :
    FiniteLP.primalValue w (R.packingPrimal S hS) = R.gain w S := by
  classical
  simp [FiniteLP.primalValue, packingPrimal, gain, Finset.sum_ite_mem]

end System

open System
variable (R : System I E)

/-- Multiplicity form of a labeled occurrence partition and its physical realizers.
`split` asserts the partition separately for every object, rather than only its weight. -/
structure Realization (w : I → ℚ) (X : I → ℕ) (q : ℕ) where
  deleted : I → ℕ
  classes : Fin q → I → ℕ
  split : ∀ o, deleted o + ∑ i, classes i o = X o
  out : Fin q → Finset I
  feasible : ∀ i, R.Packing (out i)
  loss : Fin q → ℚ
  loss_nonneg : ∀ i, 0 ≤ loss i
  bound : ∀ i, R.mass w (classes i) ≤ R.gain w (out i) + loss i

variable {R}

def Realization.cost {w : I → ℚ} {X : I → ℕ} {q : ℕ}
    (c : Realization R w X q) : ℚ := R.mass w c.deleted + ∑ i, c.loss i

theorem Realization.cost_nonneg {w : I → ℚ} {X : I → ℕ} {q : ℕ}
    (c : Realization R w X q) (hw : ∀ o, 0 ≤ w o) : 0 ≤ c.cost := by
  unfold Realization.cost mass
  exact add_nonneg
    (Finset.sum_nonneg (fun o _ => mul_nonneg (hw o) (Nat.cast_nonneg _)))
    (Finset.sum_nonneg (fun i _ => c.loss_nonneg i))

/-- The two-error certificate retains the exact primal-dual slack decomposition. -/
theorem resource_gap_identity (w : I → ℚ)
    (p : FiniteLP.PrimalFeasible R.incidence)
    (d : FiniteLP.DualFeasible R.incidence w) :
    FiniteLP.dualValue d - FiniteLP.primalValue w p =
      (∑ e, d.price e * (1 - ∑ o, R.incidence o e * p.weight o)) +
      ∑ o, p.weight o * ((∑ e, R.incidence o e * d.price e) - w o) :=
  FiniteLP.gap_identity p d

theorem Realization.mass_split {w : I → ℚ} {X : I → ℕ} {q : ℕ}
    (c : Realization R w X q) :
    R.mass w X = R.mass w c.deleted + ∑ i, R.mass w (c.classes i) := by
  unfold mass
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro o _
  rw [← c.split o]
  push_cast
  rw [mul_add, Finset.mul_sum]

/-- Corollary 4.6, without presupposing optimality of either input certificate.
The bound holds against every feasible primal point, including an optimum. -/
theorem two_error_certificate
    (w : I → ℚ) (p : FiniteLP.PrimalFeasible R.incidence)
    (d : FiniteLP.DualFeasible R.incidence w)
    {q : ℕ} (hq : 0 < q) {X : I → ℕ}
    (hX : ∀ o, (q : ℚ) * p.weight o = X o)
    (c : Realization R w X q) :
    ∃ i : Fin q,
      R.Packing (c.out i) ∧
      FiniteLP.primalValue w p - c.cost / q ≤ R.gain w (c.out i) ∧
      (∀ z : FiniteLP.PrimalFeasible R.incidence,
        FiniteLP.primalValue w z - R.gain w (c.out i) ≤
          FiniteLP.dualValue d - FiniteLP.primalValue w p + c.cost / q) := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin q))
    (fun i => R.gain w (c.out i)) ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hmass : R.mass w X = (q : ℚ) * FiniteLP.primalValue w p := by
    unfold mass FiniteLP.primalValue
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o _
    rw [← hX o]
    ring
  have hbound : R.mass w X ≤ c.cost + (q : ℚ) * R.gain w (c.out i) := by
    rw [c.mass_split]
    have hb := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) => c.bound j)
    have hm : (∑ j : Fin q, R.gain w (c.out j)) ≤ (q : ℚ) * R.gain w (c.out i) := by
      calc
        _ ≤ ∑ _j : Fin q, R.gain w (c.out i) :=
          Finset.sum_le_sum (fun j _ => hi j (Finset.mem_univ _))
        _ = _ := by simp
    rw [Finset.sum_add_distrib] at hb
    unfold Realization.cost
    linarith
  have hlower : FiniteLP.primalValue w p - c.cost / q ≤ R.gain w (c.out i) := by
    rw [hmass] at hbound
    have hc : c.cost / q * (q : ℚ) = c.cost := div_mul_cancel₀ _ hqQ.ne'
    nlinarith
  refine ⟨i, c.feasible i, hlower, ?_⟩
  intro z
  have hz := FiniteLP.weak_duality z d
  linarith

/-- Optimal specialization, including the nonnegative gap and exact slack identity. -/
theorem two_error_optimum
    (w : I → ℚ) (p : FiniteLP.PrimalFeasible R.incidence)
    (d : FiniteLP.DualFeasible R.incidence w)
    (pstar : FiniteLP.PrimalFeasible R.incidence)
    (hopt : ∀ z : FiniteLP.PrimalFeasible R.incidence,
      FiniteLP.primalValue w z ≤ FiniteLP.primalValue w pstar)
    {q : ℕ} (hq : 0 < q) {X : I → ℕ}
    (hX : ∀ o, (q : ℚ) * p.weight o = X o)
    (c : Realization R w X q) :
    ∃ i : Fin q,
      R.Packing (c.out i) ∧
      FiniteLP.primalValue w p - c.cost / q ≤ R.gain w (c.out i) ∧
      0 ≤ FiniteLP.primalValue w pstar - R.gain w (c.out i) ∧
      FiniteLP.primalValue w pstar - R.gain w (c.out i) ≤
        FiniteLP.dualValue d - FiniteLP.primalValue w p + c.cost / q := by
  obtain ⟨i, hi, hl, hb⟩ := two_error_certificate w p d hq hX c
  refine ⟨i, hi, hl, ?_, hb pstar⟩
  have h := hopt (R.packingPrimal (c.out i) hi)
  rw [packingPrimal_value] at h
  exact sub_nonneg.mpr h

end ResourceCertificate
end PaperV
