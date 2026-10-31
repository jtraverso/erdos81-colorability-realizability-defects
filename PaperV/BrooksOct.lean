/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Shared tool for N1/N2: a subcubic K₄-free graph has oct ≤ ⌊n/3⌋ (3-colour via Brooks, delete the
smallest colour class to make it bipartite).
-/
module

public import PaperV.Core
public import PaperV.BrooksMain

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Relabel `Fin 3` into `Fin 2`, injectively away from a chosen colour `i` (drops `i`). -/
def dropColor (i j : Fin 3) : Fin 2 :=
  ⟨(if j.val < i.val then j.val else j.val - 1) % 2, Nat.mod_lt _ (by norm_num)⟩

theorem dropColor_inj (i j k : Fin 3) (hj : j ≠ i) (hk : k ≠ i)
    (h : dropColor i j = dropColor i k) : j = k := by
  revert h; revert hj hk; revert i j k; decide

/-- **oct ≤ ⌊n/3⌋ for subcubic K₄-free graphs.** -/
theorem oct_le_third_of_cubic (H : SimpleGraph V) [DecidableRel H.Adj]
    (hΔ : H.maxDegree ≤ 3) (hK4 : H.CliqueFree 4) :
    oct H ≤ Fintype.card V / 3 := by
  classical
  obtain ⟨c⟩ := Brooks.brooks_cubic H hΔ hK4
  set cls : Fin 3 → Finset V := fun i => univ.filter (fun v => c v = i) with hcls
  have hdisj : (↑(univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint cls := by
    intro i _ j _ hij
    show Disjoint (cls i) (cls j)
    rw [Finset.disjoint_left]; intro v hi hj
    simp only [hcls, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact hij (hi.symm.trans hj)
  have hsum : ∑ i, (cls i).card = Fintype.card V := by
    rw [← Finset.card_biUnion hdisj]
    have huniv : (univ : Finset (Fin 3)).biUnion cls = (univ : Finset V) := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true, hcls, Finset.mem_filter, true_and]
      exact ⟨c v, rfl⟩
    rw [huniv, Finset.card_univ]
  have hsmall : ∃ i, (cls i).card ≤ Fintype.card V / 3 := by
    by_contra h; push_neg at h
    have h3 : ∑ _i : Fin 3, (Fintype.card V / 3 + 1) ≤ ∑ i, (cls i).card :=
      Finset.sum_le_sum (fun i _ => h i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
    rw [hsum] at h3
    omega
  obtain ⟨i, hi⟩ := hsmall
  have hdef : IsDefectSet H 2 (cls i) := by
    refine ⟨⟨fun v => dropColor i (c v.1), ?_⟩⟩
    intro u v huv
    have hadj : H.Adj u.1 v.1 := huv
    have hcuv : c u.1 ≠ c v.1 := c.valid hadj
    have hcu : c u.1 ≠ i := by
      have hu := u.2
      simp only [Set.mem_compl_iff, Finset.mem_coe, hcls, Finset.mem_filter,
        Finset.mem_univ, true_and] at hu
      exact hu
    have hcv : c v.1 ≠ i := by
      have hv := v.2
      simp only [Set.mem_compl_iff, Finset.mem_coe, hcls, Finset.mem_filter,
        Finset.mem_univ, true_and] at hv
      exact hv
    intro hcol
    exact hcuv (dropColor_inj i (c u.1) (c v.1) hcu hcv hcol)
  calc oct H = Dq H 2 := rfl
    _ ≤ (cls i).card := Nat.sInf_le ⟨cls i, hdef, rfl⟩
    _ ≤ Fintype.card V / 3 := hi

end PaperV
