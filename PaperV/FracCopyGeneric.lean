/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Generic fractional copy inequality (shared core of `CopyFrac.lean` and `MixedCopyFrac.lean`).

Objects are subsets of `V` satisfying a predicate `P` (a family of cliques); a fractional packing is a nonnegative
weighting with edge-load ≤ 1 on every pair; the value uses an object weight `wt`. For three predicates
`P₁, P₂, PG` (for `G_{v→u}`, `G_{u→v}`, `G`) such that the copy relabellings send `P₁`/`P₂`-objects to `PG`-objects
and preserve `wt`, and `PG`-objects have at least two vertices,

  `W*(P₁) + W*(P₂) ≤ 2 · W*(PG)`.

The proof is the total-map edge-load argument: a pushed load is ≤ 1 away from the image vertex, ≤ 2 at it and
`0` at the source vertex, so the two pushed packings have combined load ≤ 2 and their average is feasible. The
triangle case (`copy_fractional`, unit weights) and the mixed {K₃, K₄} case (`mixed_copy_fractional`, size gains)
are instances (`P := (· ∈ G.cliqueFinset 3)`, resp. the disjunction of sizes 3 and 4).

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.CopyCore

import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.Tauto

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

open SimpleGraph Finset

namespace PaperV
namespace FracCopy

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Objects of a family: subsets satisfying `P`. -/
abbrev Obj (P : Finset V → Prop) := {t : Finset V // P t}

variable {P : Finset V → Prop} [DecidablePred P]

/-- Edge-load of a weighting at the pair `{a, b}`. -/
noncomputable def edgeLoad (y : Obj P → ℝ) (a b : V) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t : Obj P => a ∈ t.1 ∧ b ∈ t.1), y t

/-- Fractional packing: nonnegative, edge-load ≤ 1 on every pair. -/
def IsFracPacking (y : Obj P → ℝ) : Prop :=
  (∀ t, 0 ≤ y t) ∧ (∀ a b : V, a ≠ b → edgeLoad y a b ≤ 1)

/-- Fractional weighted packing number of the family. -/
noncomputable def Wstar (P : Finset V → Prop) [DecidablePred P] (wt : Finset V → ℝ) : ℝ :=
  sSup { s : ℝ | ∃ y : Obj P → ℝ, IsFracPacking y ∧ s = ∑ t, wt t.1 * y t }

theorem edgeLoad_comm (y : Obj P → ℝ) (a b : V) : edgeLoad y a b = edgeLoad y b a := by
  unfold edgeLoad
  congr 1
  ext t
  simp only [Finset.mem_filter]
  tauto

omit [Fintype V] in
/-- Membership in the copy relabelling. -/
theorem mem_copyMap_iff (v u : V) (t : Finset V) (w : V) :
    w ∈ copyMap v u t ↔ (w ∈ t ∧ w ≠ v) ∨ (w = u ∧ v ∈ t) := by
  unfold copyMap
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hgx⟩
    by_cases hxv : x = v
    · subst hxv
      simp only [if_true] at hgx
      exact Or.inr ⟨hgx.symm, hx⟩
    · rw [if_neg hxv] at hgx
      subst hgx
      exact Or.inl ⟨hx, hxv⟩
  · rintro (⟨hwt, hwv⟩ | ⟨hwu, hvt⟩)
    · exact ⟨w, hwt, by rw [if_neg hwv]⟩
    · exact ⟨v, hvt, by rw [if_pos rfl]; exact hwu.symm⟩

section Push

variable {P₁ PG : Finset V → Prop} [DecidablePred P₁] [DecidablePred PG]
variable (v u : V) (hcl : ∀ t, P₁ t → PG (copyMap v u t))

/-- Image object. -/
def img (t : Obj P₁) : Obj PG := ⟨copyMap v u t.1, hcl t.1 t.2⟩

/-- Pushed weighting: total weight of the sources of each target. -/
noncomputable def push (y : Obj P₁ → ℝ) : Obj PG → ℝ :=
  fun s => ∑ t, if copyMap v u t.1 = s.1 then y t else 0

theorem push_nonneg (y : Obj P₁ → ℝ) (hy : ∀ t, 0 ≤ y t) (s : Obj PG) : 0 ≤ push v u (PG := PG) y s := by
  unfold push
  apply Finset.sum_nonneg
  intro t _
  split_ifs <;> [exact hy t; exact le_rfl]

include hcl in
/-- The pushed value equals the source value when `wt` is preserved by the copy relabelling. -/
theorem sum_push (wt : Finset V → ℝ) (hwt : ∀ t, P₁ t → wt (copyMap v u t) = wt t) (y : Obj P₁ → ℝ) :
    ∑ s, wt s.1 * push v u (PG := PG) y s = ∑ t, wt t.1 * y t := by
  classical
  let f : Obj P₁ → Obj PG := img v u hcl
  have hfib : ∀ s, wt s.1 * push v u (PG := PG) y s =
      ∑ t ∈ Finset.univ.filter (fun t => f t = s), wt t.1 * y t := by
    intro s
    rw [Finset.sum_filter]
    unfold push
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : f t = s
    · have hv : copyMap v u t.1 = s.1 := congrArg Subtype.val h
      have hw : wt s.1 = wt t.1 := by rw [← hv]; exact hwt t.1 t.2
      simp [h, hv, hw]
    · have hv : copyMap v u t.1 ≠ s.1 := by
        intro heq; apply h; exact Subtype.ext heq
      simp [h, hv]
  calc ∑ s, wt s.1 * push v u (PG := PG) y s
      = ∑ s, ∑ t ∈ Finset.univ.filter (fun t => f t = s), wt t.1 * y t :=
        Finset.sum_congr rfl (fun s _ => hfib s)
    _ = ∑ t, wt t.1 * y t := Finset.sum_fiberwise Finset.univ f (fun t => wt t.1 * y t)

include hcl in
/-- Reindexing the pushed edge-load onto the source objects. -/
theorem push_edgeLoad_eq (y : Obj P₁ → ℝ) (a b : V) :
    edgeLoad (push v u (PG := PG) y) a b =
      ∑ t ∈ Finset.univ.filter (fun t : Obj P₁ => a ∈ copyMap v u t.1 ∧ b ∈ copyMap v u t.1), y t := by
  classical
  let f : Obj P₁ → Obj PG := img v u hcl
  unfold edgeLoad push
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : a ∈ copyMap v u t.1 ∧ b ∈ copyMap v u t.1
  · rw [if_pos h]
    rw [Finset.sum_eq_single_of_mem (f t)]
    · simp [f, img]
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h.1, h.2⟩
    · intro s _ hsf
      rw [if_neg]
      intro heq
      exact hsf (Subtype.ext heq.symm)
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro s hs
    rw [if_neg]
    intro heq
    rw [Finset.mem_filter] at hs
    rw [← heq] at hs
    exact h ⟨hs.2.1, hs.2.2⟩

include hcl in
/-- Away from the image vertex the pushed load is at most the source load. -/
theorem push_edgeLoad_le_one_of_away (y : Obj P₁ → ℝ) (hy : IsFracPacking y)
    (a b : V) (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u) :
    edgeLoad (push v u (PG := PG) y) a b ≤ 1 := by
  rw [push_edgeLoad_eq v u hcl y a b]
  have hsub : (Finset.univ.filter (fun t : Obj P₁ => a ∈ copyMap v u t.1 ∧ b ∈ copyMap v u t.1)) ⊆
      (Finset.univ.filter (fun t : Obj P₁ => a ∈ t.1 ∧ b ∈ t.1)) := by
    intro t ht
    rw [Finset.mem_filter] at ht ⊢
    refine ⟨ht.1, ?_, ?_⟩
    · rcases (mem_copyMap_iff v u t.1 a).mp ht.2.1 with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h hau
    · rcases (mem_copyMap_iff v u t.1 b).mp ht.2.2 with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h hbu
  calc ∑ t ∈ _, y t
        ≤ ∑ t ∈ Finset.univ.filter (fun t : Obj P₁ => a ∈ t.1 ∧ b ∈ t.1), y t :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hy.1 i)
    _ = edgeLoad y a b := rfl
    _ ≤ 1 := hy.2 a b hab

include hcl in
/-- Any pushed edge-load is at most two. -/
theorem push_edgeLoad_le_two (y : Obj P₁ → ℝ) (hy : IsFracPacking y) (a b : V) (hab : a ≠ b) :
    edgeLoad (push v u (PG := PG) y) a b ≤ 2 := by
  classical
  have key : ∀ p q : V, p ≠ q → p ≠ u → edgeLoad (push v u (PG := PG) y) p q ≤ 2 := by
    intro p q hpq hpu
    rw [push_edgeLoad_eq v u hcl y p q]
    by_cases hpv : p = v
    · have hempty : (Finset.univ.filter (fun t : Obj P₁ =>
          p ∈ copyMap v u t.1 ∧ q ∈ copyMap v u t.1)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro t _
        rintro ⟨hp, _⟩
        rcases (mem_copyMap_iff v u t.1 p).mp hp with ⟨_, hne⟩ | ⟨heq, _⟩
        · exact hne hpv
        · exact hpu heq
      rw [hempty, Finset.sum_empty]
      norm_num
    · set A := Finset.univ.filter (fun t : Obj P₁ => p ∈ t.1 ∧ q ∈ t.1) with hA
      set B := Finset.univ.filter (fun t : Obj P₁ => p ∈ t.1 ∧ v ∈ t.1) with hB
      have hsub : (Finset.univ.filter (fun t : Obj P₁ =>
          p ∈ copyMap v u t.1 ∧ q ∈ copyMap v u t.1)) ⊆ A ∪ B := by
        intro t ht
        rw [Finset.mem_filter] at ht
        have hp : p ∈ t.1 := by
          rcases (mem_copyMap_iff v u t.1 p).mp ht.2.1 with ⟨h, _⟩ | ⟨h, _⟩
          · exact h
          · exact absurd h hpu
        rcases (mem_copyMap_iff v u t.1 q).mp ht.2.2 with ⟨hq, _⟩ | ⟨_, hvt⟩
        · exact Finset.mem_union.mpr (Or.inl (by rw [hA, Finset.mem_filter]; exact ⟨ht.1, hp, hq⟩))
        · exact Finset.mem_union.mpr (Or.inr (by rw [hB, Finset.mem_filter]; exact ⟨ht.1, hp, hvt⟩))
      have hle1 : ∑ t ∈ A, y t ≤ 1 := hy.2 p q hpq
      have hle2 : ∑ t ∈ B, y t ≤ 1 := hy.2 p v hpv
      have hunion : ∑ t ∈ A ∪ B, y t ≤ ∑ t ∈ A, y t + ∑ t ∈ B, y t := by
        have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := y)
        have hi : 0 ≤ ∑ t ∈ A ∩ B, y t := Finset.sum_nonneg (fun i _ => hy.1 i)
        linarith
      have hsum : ∑ t ∈ Finset.univ.filter (fun t : Obj P₁ =>
          p ∈ copyMap v u t.1 ∧ q ∈ copyMap v u t.1), y t ≤ ∑ t ∈ A ∪ B, y t :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hy.1 i)
      linarith
  by_cases hau : a = u
  · have hbu : b ≠ u := fun h => hab (hau.trans h.symm)
    have hkey := key b a (Ne.symm hab) hbu
    rw [edgeLoad_comm]
    exact hkey
  · exact key a b hab hau

/-- The pushed load vanishes at the source vertex `v` (when `v ≠ u`). -/
theorem push_edgeLoad_eq_zero_at_source (hvu : v ≠ u) (y : Obj P₁ → ℝ) (b : V) :
    edgeLoad (push v u (PG := PG) y) v b = 0 := by
  unfold edgeLoad
  rw [Finset.sum_eq_zero]
  intro s hs
  unfold push
  rw [Finset.sum_eq_zero]
  intro t _
  split_ifs with h
  · have hs_v : v ∈ s.1 := (Finset.mem_filter.mp hs).2.1
    have hcopy_no_v : v ∉ copyMap v u t.1 := by
      rw [mem_copyMap_iff]
      rintro (⟨_, hne⟩ | ⟨heq, _⟩)
      · exact hne rfl
      · exact hvu heq
    exact False.elim (hcopy_no_v (h ▸ hs_v))
  · rfl

include hcl in
/-- When `v = u` the copy map is the identity and the pushed load is a source load. -/
theorem push_edgeLoad_le_one_eq (hvu : v = u) (y : Obj P₁ → ℝ) (hy : IsFracPacking y)
    (a b : V) (hab : a ≠ b) : edgeLoad (push v u (PG := PG) y) a b ≤ 1 := by
  have hid : ∀ t : Finset V, copyMap v u t = t := by
    intro t
    ext w
    rw [mem_copyMap_iff]
    subst hvu
    constructor
    · rintro (⟨h, _⟩ | ⟨rfl, h⟩)
      · exact h
      · exact h
    · intro hw
      by_cases hwv : w = v
      · exact Or.inr ⟨hwv, hwv ▸ hw⟩
      · exact Or.inl ⟨hw, hwv⟩
  rw [push_edgeLoad_eq v u hcl y a b]
  have heq : (Finset.univ.filter (fun t : Obj P₁ => a ∈ copyMap v u t.1 ∧ b ∈ copyMap v u t.1))
      = (Finset.univ.filter (fun t : Obj P₁ => a ∈ t.1 ∧ b ∈ t.1)) := by
    apply Finset.filter_congr
    intro t _
    rw [hid t.1]
  rw [heq]
  exact hy.2 a b hab

end Push

section Main

variable {P₁ P₂ PG : Finset V → Prop} [DecidablePred P₁] [DecidablePred P₂] [DecidablePred PG]

/-- Combined pushed load is at most two everywhere. -/
theorem pushed_combined_edgeLoad_le_two (v u : V)
    (hcl₁ : ∀ t, P₁ t → PG (copyMap v u t)) (hcl₂ : ∀ t, P₂ t → PG (copyMap u v t))
    (y₁ : Obj P₁ → ℝ) (y₂ : Obj P₂ → ℝ) (hy₁ : IsFracPacking y₁) (hy₂ : IsFracPacking y₂) :
    ∀ a b : V, a ≠ b →
      edgeLoad (fun s => push v u (PG := PG) y₁ s + push u v (PG := PG) y₂ s) a b ≤ 2 := by
  intro a b hab
  have hadd : edgeLoad (fun s => push v u (PG := PG) y₁ s + push u v (PG := PG) y₂ s) a b
      = edgeLoad (push v u (PG := PG) y₁) a b + edgeLoad (push u v (PG := PG) y₂) a b := by
    unfold edgeLoad
    rw [← Finset.sum_add_distrib]
  rw [hadd]
  set L₁ := edgeLoad (push v u (PG := PG) y₁) a b with hL1
  set L₂ := edgeLoad (push u v (PG := PG) y₂) a b with hL2
  by_cases hveq : v = u
  · have h1 : L₁ ≤ 1 := push_edgeLoad_le_one_eq v u hcl₁ hveq y₁ hy₁ a b hab
    have h2 : L₂ ≤ 1 := push_edgeLoad_le_one_eq u v hcl₂ hveq.symm y₂ hy₂ a b hab
    linarith
  · by_cases hau : a = u
    · have h2 : L₂ = 0 := by
        rw [hL2, hau]
        exact push_edgeLoad_eq_zero_at_source u v (fun h => hveq h.symm) y₂ b
      have h1 : L₁ ≤ 2 := push_edgeLoad_le_two v u hcl₁ y₁ hy₁ a b hab
      linarith
    · by_cases hbu : b = u
      · have h2 : L₂ = 0 := by
          rw [hL2, edgeLoad_comm, hbu]
          exact push_edgeLoad_eq_zero_at_source u v (fun h => hveq h.symm) y₂ a
        have h1 : L₁ ≤ 2 := push_edgeLoad_le_two v u hcl₁ y₁ hy₁ a b hab
        linarith
      · by_cases hav : a = v
        · have h1 : L₁ = 0 := by
            rw [hL1, hav]
            exact push_edgeLoad_eq_zero_at_source v u hveq y₁ b
          have h2 : L₂ ≤ 2 := push_edgeLoad_le_two u v hcl₂ y₂ hy₂ a b hab
          linarith
        · by_cases hbv : b = v
          · have h1 : L₁ = 0 := by
              rw [hL1, edgeLoad_comm, hbv]
              exact push_edgeLoad_eq_zero_at_source v u hveq y₁ a
            have h2 : L₂ ≤ 2 := push_edgeLoad_le_two u v hcl₂ y₂ hy₂ a b hab
            linarith
          · have h1 : L₁ ≤ 1 := push_edgeLoad_le_one_of_away v u hcl₁ y₁ hy₁ a b hab hau hbu
            have h2 : L₂ ≤ 1 := push_edgeLoad_le_one_of_away u v hcl₂ y₂ hy₂ a b hab hav hbv
            linarith

/-- Boundedness: objects with ≥ 2 vertices have weight ≤ 1 in a fractional packing. -/
theorem fracPacking_total_bdd (wt : Finset V → ℝ) (hw : ∀ t, 0 ≤ wt t) (hcard : ∀ t, PG t → 2 ≤ t.card)
    (y : Obj PG → ℝ) (hy : IsFracPacking y) :
    ∑ t, wt t.1 * y t ≤ ∑ t : Obj PG, wt t.1 := by
  have h1 : ∀ t, y t ≤ 1 := by
    intro t
    obtain ⟨verts, hverts⟩ := t
    have hcard' : 1 < verts.card := hcard verts hverts
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard'
    have hload := hy.2 a b hab
    have hyt_le : y ⟨verts, hverts⟩ ≤ edgeLoad y a b := by
      simp only [edgeLoad]
      apply Finset.single_le_sum (fun s _ => hy.1 s)
      simp [ha, hb]
    linarith
  apply Finset.sum_le_sum
  intro t _
  calc wt t.1 * y t ≤ wt t.1 * 1 := mul_le_mul_of_nonneg_left (h1 t) (hw t.1)
    _ = wt t.1 := mul_one _

theorem total_le_Wstar (wt : Finset V → ℝ) (hw : ∀ t, 0 ≤ wt t) (hcard : ∀ t, PG t → 2 ≤ t.card)
    (y : Obj PG → ℝ) (hy : IsFracPacking y) :
    ∑ t, wt t.1 * y t ≤ Wstar PG wt := by
  apply le_csSup
  · use ∑ t : Obj PG, wt t.1
    rintro s ⟨y', hy', rfl⟩
    exact fracPacking_total_bdd wt hw hcard y' hy'
  · exact ⟨y, hy, rfl⟩

/-- **Generic fractional copy inequality.** -/
theorem copy_fractional_generic (v u : V) (wt : Finset V → ℝ) (hw : ∀ t, 0 ≤ wt t)
    (hcl₁ : ∀ t, P₁ t → PG (copyMap v u t)) (hcl₂ : ∀ t, P₂ t → PG (copyMap u v t))
    (hwt₁ : ∀ t, P₁ t → wt (copyMap v u t) = wt t) (hwt₂ : ∀ t, P₂ t → wt (copyMap u v t) = wt t)
    (hcard : ∀ t, PG t → 2 ≤ t.card) :
    Wstar P₁ wt + Wstar P₂ wt ≤ 2 * Wstar PG wt := by
  classical
  let A : Set ℝ := {s | ∃ y : Obj P₁ → ℝ, IsFracPacking y ∧ s = ∑ t, wt t.1 * y t}
  let B : Set ℝ := {s | ∃ y : Obj P₂ → ℝ, IsFracPacking y ∧ s = ∑ t, wt t.1 * y t}
  have hA0 : (0 : ℝ) ∈ A := by
    refine ⟨fun _ => 0, ?_, by simp⟩
    constructor
    · simp
    · intro a b hab
      simp [edgeLoad]
  have hB0 : (0 : ℝ) ∈ B := by
    refine ⟨fun _ => 0, ?_, by simp⟩
    constructor
    · simp
    · intro a b hab
      simp [edgeLoad]
  have hbound (a b : ℝ) (ha : a ∈ A) (hb : b ∈ B) : a + b ≤ 2 * Wstar PG wt := by
    obtain ⟨y₁, hy₁, rfl⟩ := ha
    obtain ⟨y₂, hy₂, rfl⟩ := hb
    let z : Obj PG → ℝ := fun s => (1 / 2 : ℝ) * (push v u (PG := PG) y₁ s + push u v (PG := PG) y₂ s)
    have hz : IsFracPacking z := by
      constructor
      · intro s
        exact mul_nonneg (by norm_num)
          (add_nonneg (push_nonneg v u y₁ hy₁.1 s) (push_nonneg u v y₂ hy₂.1 s))
      · intro x y hxy
        have hload := pushed_combined_edgeLoad_le_two v u hcl₁ hcl₂ y₁ y₂ hy₁ hy₂ x y hxy
        unfold edgeLoad at hload ⊢
        dsimp [z]
        rw [← Finset.mul_sum]
        norm_num at hload ⊢
        linarith
    have hzbound := total_le_Wstar wt hw hcard z hz
    have hsum : ∑ s, wt s.1 * z s =
        (1 / 2 : ℝ) * ((∑ t, wt t.1 * y₁ t) + ∑ t, wt t.1 * y₂ t) := by
      dsimp [z]
      rw [← sum_push v u hcl₁ wt hwt₁ y₁, ← sum_push u v hcl₂ wt hwt₂ y₂,
        ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _; ring
    rw [hsum] at hzbound
    linarith
  rw [show Wstar P₁ wt = sSup A by rfl, show Wstar P₂ wt = sSup B by rfl]
  have ha_bound (a : ℝ) (ha : a ∈ A) : a + sSup B ≤ 2 * Wstar PG wt := by
    have hs : sSup B ≤ 2 * Wstar PG wt - a := by
      apply csSup_le (s := B) ⟨0, hB0⟩
      intro b hb
      have := hbound a b ha hb
      linarith
    linarith
  have hsupA : sSup A ≤ 2 * Wstar PG wt - sSup B := by
    apply csSup_le (s := A) ⟨0, hA0⟩
    intro a ha
    have := ha_bound a ha
    linarith
  linarith

end Main

end FracCopy
end PaperV
