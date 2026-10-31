/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — S1: q-splitting (generalises Lemma 3.1 / Cor 3.2 to arbitrary q).

Improvement S1 (2026-07-26 handoff, FULL option). The delete-and-colour mechanism is written once
for general `q`; the paper's Theorem 3.4 then follows in three lines, and Theorem 3.3 becomes the
`q = 2` specialisation (`D_2 = oct`). We also keep the CEILING form of the corollary — strictly
stronger than `D_q/q` because `ν` is an integer — which the current §3 loses when going from
Cor 3.2 to Thm 3.3/3.4.

Brooks-independent: this only reorders/generalises the existing `PaperV.splitting` argument.
-/
module

public import PaperV.Core

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set
import Mathlib.Tactic.SimpRw

@[expose] public section

open SimpleGraph Finset

namespace PaperV.SplittingQ

open PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Lemma 3.1′ (q-splitting).** For every finite graph `H` and every `q ≥ 1` there are `q`
pairwise-disjoint feasible (independent) sets `S₀,…,S_{q-1}` with
`∑ᵢ |Sᵢ| ≥ |V| − D_q(H)`. The `q = 2` case is `PaperV.splitting` (`D_2 = oct`). -/
theorem splitting_q (H : SimpleGraph V) [DecidableRel H.Adj] (q : ℕ) (hq : 1 ≤ q) :
    ∃ S : Fin q → Finset V,
      (∀ i, Feasible H (S i)) ∧
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
      Fintype.card V - Dq H q ≤ ∑ i, (S i).card := by
  have hne := defectSet_nonempty H hq
  have hmin : ∃ O : Finset V, IsDefectSet H q O ∧ O.card = Dq H q := by
    exact Nat.sInf_mem hne
  obtain ⟨O, hO, hOcard⟩ := hmin
  rw [IsDefectSet] at hO
  obtain ⟨col, hcol⟩ := hO
  let W := {v : V // v ∉ O}
  let C : Fin q → Finset W := fun i => Finset.univ.filter (fun v => col v = i)
  let S : Fin q → Finset V := fun i => (C i).image Subtype.val
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i a ha b hb hab
    simp only [S, Finset.mem_image] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at ha' hb'
    have hadj : (H.induce (↑O)ᶜ).Adj a' b' := hab
    have hne := SimpleGraph.Adj.ne (hcol hadj)
    rw [ha', hb'] at hne
    exact hne rfl
  · intro i j hij
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    simp only [S, Finset.mem_image] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at ha' hb'
    have hab' : a' = b' := Subtype.val_injective hab
    subst b'
    rw [ha'] at hb'
    exact hij hb'
  · have hcardC : ∑ i, (C i).card = Fintype.card W := by
      have hx := Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset W) (Finset.univ : Finset (Fin q)) col
      rw [Finset.filter_true_of_mem (fun _ _ => by simp)] at hx
      simpa only [C, Finset.card_univ] using hx
    have hcardS : ∀ i, (S i).card = (C i).card := by
      intro i
      exact Finset.card_image_of_injective _ Subtype.val_injective
    simp_rw [hcardS, hcardC]
    have hcardO : Fintype.card {x // x ∈ O} = O.card :=
      Fintype.card_ofFinset O (fun x => Iff.rfl)
    have hW : Fintype.card W = Fintype.card V - O.card := by
      rw [Fintype.card_subtype_compl, hcardO]
    rw [hW, hOcard]

/-- **Corollary 3.2′ (ceiling form).** Some feasible set has cardinality at least
`⌈(|V| − D_q(H)) / q⌉` (here as the ℕ expression `(|V| − D_q + q − 1)/q`). Pigeonhole over the `q`
classes of `splitting_q`. This is the source of `ν ≥ ⌈(|X| − D_q(H[X]))/q⌉` after instantiation. -/
theorem splitting_ceil (H : SimpleGraph V) [DecidableRel H.Adj] (q : ℕ) (hq : 1 ≤ q) :
    ∃ S : Finset V, Feasible H S ∧
      (Fintype.card V - Dq H q + (q - 1)) / q ≤ S.card := by
  obtain ⟨S, hfeas, _, hsum⟩ := splitting_q H q hq
  let k := (Fintype.card V - Dq H q + (q - 1)) / q
  by_contra hn
  push_neg at hn
  have hall : ∀ i, (S i).card ≤ k - 1 := by
    intro i
    exact Nat.le_sub_one_of_lt (hn (S i) (hfeas i))
  have hsum' : ∑ i, (S i).card ≤ q * (k - 1) := by
    calc
      ∑ i, (S i).card ≤ ∑ _i : Fin q, (k - 1) :=
        Finset.sum_le_sum (fun i _ => hall i)
      _ = q * (k - 1) := by simp
  have hkpos : 0 < k := by
    by_contra hk
    simp only [Nat.not_lt, Nat.le_zero] at hk
    have hz : k = 0 := hk
    have := hn (S ⟨0, hq⟩) (hfeas ⟨0, hq⟩)
    omega
  have hqpos : 0 < q := by omega
  have hmul : k * q ≤ Fintype.card V - Dq H q + (q - 1) := by
    dsimp [k]
    exact (Nat.le_div_iff_mul_le hqpos).mp (le_refl _)
  have hk1 : 1 ≤ k := hkpos
  have hqle : q ≤ q * k := by
    simpa using Nat.mul_le_mul_left q hk1
  have heq : q * (k - 1) + q = q * k := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.sub_add_cancel hqle]
  have hstrict : q * (k - 1) < Fintype.card V - Dq H q := by
    rw [Nat.mul_comm k q] at hmul
    omega
  omega

end PaperV.SplittingQ
