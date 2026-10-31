/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Weighted transfer (DV26 abstract kernel).

Generalises `transfer_q` (Thm 3.4) from unit weights to an arbitrary object weight `w : O → ℕ`.
  weighted size     |X|_w   = Σ_o w(o)·X(o)
  weighted packing  ν_w(C)  = max Σ_{o∈S} w(o) over feasible S
  weighted defect   D_q^w(H[X]) = min Σ_{c∈Z} w(obj c) over Z with H[X] − Z q-colourable
Theorem: |X|_w ≤ q · ν_w(C) + D_q^w(H[X]).   (`transfer_q` is the case w ≡ 1.)

The clique-partition instantiation (w(Q) = C(|Q|,2) − 1, cp(G) ≤ c(x) + D_r^w/r) lives in Paper V.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.ConflictGraph

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable (C : ConflictSystem)

/-- Weighted size of a multiset: `Σ_o w(o) · X(o)`. -/
def wMultSize (w : C.O → ℕ) (X : C.O → ℕ) : ℕ := ∑ o : C.O, w o * X o

open Classical in
/-- Weighted packing number `ν_w(C)`: maximum total weight of a feasible object set. -/
noncomputable def wNu (w : C.O → ℕ) : ℕ :=
  (univ.filter (fun S : Finset C.O => CSFeasible C S)).sup (fun S => ∑ o ∈ S, w o)

/-- Weight of a copy = weight of its underlying object. -/
def copyWeight (w : C.O → ℕ) {X : C.O → ℕ} (c : Copies C X) : ℕ := w c.1

/-- Weighted colourability defect of `H[X]`: minimum total weight of a set of copies whose deletion
leaves `H[X]` `q`-colourable. -/
noncomputable def wDq (w : C.O → ℕ) (X : C.O → ℕ) (q : ℕ) : ℕ :=
  sInf { n | ∃ Z : Finset (Copies C X), IsDefectSet (Hgraph C X) q Z ∧
    ∑ c ∈ Z, copyWeight C w c = n }

theorem wDq_values_nonempty (w : C.O → ℕ) (X : C.O → ℕ) (q : ℕ) :
    { n | ∃ Z : Finset (Copies C X), IsDefectSet (Hgraph C X) q Z ∧
      ∑ c ∈ Z, copyWeight C w c = n }.Nonempty := by
  classical
  refine ⟨_, Finset.univ, ?_, rfl⟩
  unfold IsDefectSet
  letI : IsEmpty ↥(((Finset.univ : Finset (Copies C X)) : Set (Copies C X))ᶜ) :=
    ⟨fun v => by have := v.property; simp at this⟩
  exact SimpleGraph.Colorable.of_isEmpty q

/-- Unit weights recover the unweighted defect. -/
theorem wDq_one (X : C.O → ℕ) (q : ℕ) : wDq C (fun _ => 1) X q = Dq (Hgraph C X) q := by
  unfold wDq Dq; congr 1; ext n; simp [copyWeight]

/-- Unit weights recover the unweighted size. -/
theorem wMultSize_one (X : C.O → ℕ) : wMultSize C (fun _ => 1) X = multSize C X := by
  simp [wMultSize, multSize]

/-- Weighted version of `indep_le_nu`: an independent set of `H[X]` has total copy-weight ≤ `ν_w`. -/
theorem wIndep_le_wNu (w : C.O → ℕ) (X : C.O → ℕ) (S : Finset (Copies C X))
    (hS : Feasible (Hgraph C X) S) : ∑ c ∈ S, copyWeight C w c ≤ wNu C w := by
  classical
  let T : Finset C.O := S.image (objOf (C := C) (X := X))
  have hinj : Set.InjOn (objOf (C := C) (X := X)) S := by
    intro a ha b hb hab
    by_contra hne
    exact hS ha hb ⟨hne, Or.inl hab⟩
  have hsum : ∑ c ∈ S, copyWeight C w c = ∑ o ∈ T, w o := by
    rw [Finset.sum_image hinj]; rfl
  have hT : CSFeasible C T := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := by
      intro heq; subst b; exact C.Kirrefl a.1 hxy
    exact hS ha hb ⟨hab, Or.inr hxy⟩
  rw [hsum]
  exact Finset.le_sup (f := fun S => ∑ o ∈ S, w o) (by simp [hT])

/-- Pigeonhole with weights: some colour class carries at least `1/q` of the total weight. -/
lemma exists_heavy_color_class {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (hq : 1 ≤ q) (c : V → Fin q) (f : V → ℕ) :
    ∃ i : Fin q, ∑ v, f v ≤ q * ∑ v ∈ Finset.univ.filter (fun v => c v = i), f v := by
  by_contra h
  push_neg at h
  have hsum : ∑ i : Fin q, ∑ v ∈ Finset.univ.filter (fun v => c v = i), f v = ∑ v, f v := by
    rw [← Finset.sum_biUnion]
    · congr 1; ext v; simp [Finset.mem_biUnion, Finset.mem_filter]
    · intro i _ j _ hij
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      intro x hi hj; rw [hi] at hj; exact hij hj
  have hlt : ∑ i : Fin q, q * ∑ v ∈ Finset.univ.filter (fun v => c v = i), f v
      < ∑ _i : Fin q, ∑ v, f v := by
    apply Finset.sum_lt_sum_of_nonempty ⟨⟨0, hq⟩, Finset.mem_univ _⟩
    intro i _; exact h i
  rw [← Finset.mul_sum, hsum] at hlt
  simp at hlt

/-- From a `q`-colouring of the complement of `Z` extract a feasible set of weight ≥ (total − w(Z))/q. -/
theorem exists_heavy_feasible {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (q : ℕ) (hq : 1 ≤ q) (Z : Finset V) (f : V → ℕ)
    (hc : (H.induce ((Z : Set V)ᶜ)).Colorable q) :
    ∃ S : Finset V, Feasible H S ∧ ∑ v, f v ≤ q * ∑ v ∈ S, f v + ∑ v ∈ Z, f v := by
  classical
  let col := hc.some
  obtain ⟨i, hi⟩ := exists_heavy_color_class q hq col (fun v => f v.1)
  let S' : Finset ↥((Z : Set V)ᶜ) := Finset.univ.filter fun v => col v = i
  let S : Finset V := S'.image Subtype.val
  refine ⟨S, ?_, ?_⟩
  · intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    have hca : col a' = i := (Finset.mem_filter.mp ha').2
    have hcb : col b' = i := (Finset.mem_filter.mp hb').2
    exact col.valid (SimpleGraph.induce_adj.mpr hab) (hca.trans hcb.symm)
  · have hS : ∑ v ∈ S, f v = ∑ v ∈ S', f v.1 :=
      Finset.sum_image (fun a _ b _ h => Subtype.val_injective h)
    -- total over the complement of Z as a subtype sum
    have hcompl : ∑ v : ↥((Z : Set V)ᶜ), f v.1 = ∑ v ∈ Finset.univ \ Z, f v := by
      rw [← Finset.sum_subtype (Finset.univ \ Z) (p := fun v => v ∈ ((Z : Set V)ᶜ))]
      intro v; simp
    have hsplit : ∑ v, f v = ∑ v ∈ Finset.univ \ Z, f v + ∑ v ∈ Z, f v := by
      rw [Finset.sum_sdiff (Finset.subset_univ Z)]
    calc ∑ v, f v = ∑ v ∈ Finset.univ \ Z, f v + ∑ v ∈ Z, f v := hsplit
      _ = ∑ v : ↥((Z : Set V)ᶜ), f v.1 + ∑ v ∈ Z, f v := by rw [hcompl]
      _ ≤ q * ∑ v ∈ S', f v.1 + ∑ v ∈ Z, f v := Nat.add_le_add_right hi _
      _ = q * ∑ v ∈ S, f v + ∑ v ∈ Z, f v := by rw [hS]

/-- **Weighted transfer (DV26 kernel).** `|X|_w ≤ q · ν_w(C) + D_q^w(H[X])`. -/
theorem transfer_q_weighted (w : C.O → ℕ) (X : C.O → ℕ) (q : ℕ) (hq : 1 ≤ q) :
    wMultSize C w X ≤ q * wNu C w + wDq C w X q := by
  classical
  let H := Hgraph C X
  have hmem := Nat.sInf_mem (wDq_values_nonempty C w X q)
  change wDq C w X q ∈ {n | ∃ Z : Finset (Copies C X),
    IsDefectSet H q Z ∧ ∑ c ∈ Z, copyWeight C w c = n} at hmem
  obtain ⟨Z, hZ, hZw⟩ := hmem
  obtain ⟨S, hS, hlarge⟩ := exists_heavy_feasible H q hq Z (copyWeight C w) hZ
  have hSnu : ∑ c ∈ S, copyWeight C w c ≤ wNu C w := wIndep_le_wNu C w X S hS
  have htot : ∑ c : Copies C X, copyWeight C w c = wMultSize C w X := by
    unfold wMultSize copyWeight Copies
    rw [Fintype.sum_sigma]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  have hmul : q * ∑ c ∈ S, copyWeight C w c ≤ q * wNu C w := Nat.mul_le_mul_left q hSnu
  change ∑ c ∈ Z, copyWeight C w c = wDq C w X q at hZw
  omega

/-- **Certificate form of the weighted transfer.** For ANY deletion set `Z` whose removal leaves `H[X]`
`q`-colourable (not necessarily of minimum weight): `|X|_w ≤ q · ν_w + w(Z)`. This is the checkable
version: the certificate is `(Z, colouring)`, no optimisation is required to verify it. -/
theorem transfer_q_weighted_cert (w : C.O → ℕ) (X : C.O → ℕ) (q : ℕ) (hq : 1 ≤ q)
    (Z : Finset (Copies C X)) (hZ : IsDefectSet (Hgraph C X) q Z) :
    wMultSize C w X ≤ q * wNu C w + ∑ c ∈ Z, copyWeight C w c := by
  classical
  obtain ⟨S, hS, hlarge⟩ := exists_heavy_feasible (Hgraph C X) q hq Z (copyWeight C w) hZ
  have hSnu : ∑ c ∈ S, copyWeight C w c ≤ wNu C w := wIndep_le_wNu C w X S hS
  have htot : ∑ c : Copies C X, copyWeight C w c = wMultSize C w X := by
    unfold wMultSize copyWeight Copies
    rw [Fintype.sum_sigma]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  have hmul : q * ∑ c ∈ S, copyWeight C w c ≤ q * wNu C w := Nat.mul_le_mul_left q hSnu
  omega

/-- Sanity: the weighted theorem specialises to `transfer_q` under unit weights. -/
theorem transfer_q_weighted_one (X : C.O → ℕ) (q : ℕ) (hq : 1 ≤ q) :
    multSize C X ≤ q * wNu C (fun _ => 1) + Dq (Hgraph C X) q := by
  have := transfer_q_weighted C (fun _ => 1) X q hq
  rwa [wMultSize_one, wDq_one] at this

/-- `ν_w` with unit weights is `ν`. -/
theorem wNu_one : wNu C (fun _ => 1) = nu C := by
  unfold wNu nu; simp

end PaperV
