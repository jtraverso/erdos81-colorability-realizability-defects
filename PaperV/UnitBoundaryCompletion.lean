/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Unit-boundary completion and endpoint repacking (AV5441 Lemmas A / B, abstract).

Resource model. Objects `α` carry resources `res : α → Finset R`; a family is feasible when its
resource sets are pairwise disjoint (this is the conflict system "K a b ↔ a ≠ b ∧ res a ∩ res b ≠ ∅").
Setting (cardinality only — no weights):
  * `SR`      shared resources;
  * `Q`       outer objects: any two distinct outer objects can only meet inside `SR`
              (`hQ`), and each outer object uses at most ONE shared resource (`hunit`);
  * `D`       central objects, `res d ⊆ SR`, labels disjoint from `Q`.
Derived data:  `Z Q SR` = outer objects with no shared resource, `z = |Z|`;
               `B Q SR` = shared resources occupied by the other outer objects;
               `nuAvoid D B` = max feasible subfamily of `D` avoiding `B`.

Lemma A (`unitBoundary_completion_optimal`): the packing optimum of `Q ∪ D` is exactly
  `z + |B| + ν_D(B)`, attained by keeping all of `Z`, one representative per resource of `B`, and a
  maximum central packing avoiding `B`.
Lemma B (`endpoint_repacking_card_bound`): for two outer families `Q₀, Q₁` on the same central `D`
  and shared `SR`, and any central packing `C₀` avoiding `B₀`, the transported packing
  `P₁ = Z₁ ∪ reps₁ ∪ {c ∈ C₀ | res c avoids B₁}` is feasible and
  `|P₀| + z₁ ≤ |P₁| + z₀ + |B₀ \ B₁|`, with `h := |C₀| − |C₀'| ≤ |B₁ \ B₀|`.

Limits (must stay explicit, cf. AV5441 §5): cardinality only; `≤ 1` shared resource per outer object;
private independence is a hypothesis (`hQ`); no chordality / efficiency claim.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Set
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

@[expose] public section

open Finset Classical

namespace PaperV

namespace UnitBoundary

variable {α R : Type*} [DecidableEq α] [DecidableEq R]

/-- Feasible family: pairwise disjoint resource sets (distinct members). -/
def ResFeasible (res : α → Finset R) (P : Finset α) : Prop :=
  ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → Disjoint (res a) (res b)

/-- Packing optimum inside a universe `U`. -/
noncomputable def packOpt (res : α → Finset R) (U : Finset α) : ℕ :=
  (U.powerset.filter (fun P => ResFeasible res P)).sup Finset.card

theorem le_packOpt (res : α → Finset R) {U P : Finset α} (hP : P ⊆ U) (hf : ResFeasible res P) :
    P.card ≤ packOpt res U := by
  unfold packOpt
  exact Finset.le_sup (f := Finset.card)
    (by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hP, hf⟩)

theorem packOpt_le (res : α → Finset R) {U : Finset α} {n : ℕ}
    (h : ∀ P ⊆ U, ResFeasible res P → P.card ≤ n) : packOpt res U ≤ n := by
  unfold packOpt
  apply Finset.sup_le
  intro P hP
  rw [Finset.mem_filter, Finset.mem_powerset] at hP
  exact h P hP.1 hP.2

/-- Outer objects with no shared resource. -/
def Z (res : α → Finset R) (Q : Finset α) (SR : Finset R) : Finset α :=
  Q.filter (fun o => res o ∩ SR = ∅)

/-- Shared resources occupied by the outer objects (those outside `Z`). -/
def B (res : α → Finset R) (Q : Finset α) (SR : Finset R) : Finset R :=
  (Q \ Z res Q SR).biUnion (fun o => res o ∩ SR)

/-- Maximum feasible central subfamily avoiding the resources in `Bd`. -/
noncomputable def nuAvoid (res : α → Finset R) (D : Finset α) (Bd : Finset R) : ℕ :=
  (D.powerset.filter (fun T => ResFeasible res T ∧ ∀ d ∈ T, Disjoint (res d) Bd)).sup
    Finset.card

theorem le_nuAvoid (res : α → Finset R) {D T : Finset α} {Bd : Finset R} (hT : T ⊆ D)
    (hf : ResFeasible res T) (hav : ∀ d ∈ T, Disjoint (res d) Bd) : T.card ≤ nuAvoid res D Bd := by
  unfold nuAvoid
  exact Finset.le_sup (f := Finset.card)
    (by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hT, hf, hav⟩)

theorem exists_nuAvoid (res : α → Finset R) (D : Finset α) (Bd : Finset R) :
    ∃ T ⊆ D, ResFeasible res T ∧ (∀ d ∈ T, Disjoint (res d) Bd) ∧ T.card = nuAvoid res D Bd := by
  have hne : (D.powerset.filter
      (fun T => ResFeasible res T ∧ ∀ d ∈ T, Disjoint (res d) Bd)).Nonempty := by
    refine ⟨∅, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.empty_subset _, ?_, ?_⟩
    · intro a ha; exact absurd ha (Finset.notMem_empty a)
    · intro d hd; exact absurd hd (Finset.notMem_empty d)
  obtain ⟨T, hT, hmax⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hT
  refine ⟨T, hT.1, hT.2.1, hT.2.2, ?_⟩
  unfold nuAvoid; exact hmax.symm

/-! ### Standing hypotheses bundled as a structure -/

/-- The unit-boundary configuration. -/
structure Config (res : α → Finset R) (Q D : Finset α) (SR : Finset R) : Prop where
  /-- Two distinct outer objects meet only inside `SR` (private resources are page-disjoint and each
  page is internally feasible). -/
  hQ : ∀ ⦃a⦄, a ∈ Q → ∀ ⦃b⦄, b ∈ Q → a ≠ b → res a ∩ res b ⊆ SR
  /-- Each outer object uses at most one shared resource. -/
  hunit : ∀ o ∈ Q, (res o ∩ SR).card ≤ 1
  /-- Central objects live on shared resources. -/
  hD : ∀ d ∈ D, res d ⊆ SR
  /-- Outer and central labels are distinct. -/
  hdisj : Disjoint Q D

variable {res : α → Finset R} {Q D : Finset α} {SR : Finset R}

theorem Z_subset : Z res Q SR ⊆ Q := Finset.filter_subset _ _

theorem mem_Z {o : α} : o ∈ Z res Q SR ↔ o ∈ Q ∧ res o ∩ SR = ∅ := Finset.mem_filter

theorem mem_B {r : R} : r ∈ B res Q SR ↔ ∃ o ∈ Q \ Z res Q SR, r ∈ res o ∩ SR := by
  simp [B, Finset.mem_biUnion]

/-- An outer object outside `Z` has exactly one shared resource. -/
theorem card_shared_eq_one (cfg : Config res Q D SR) {o : α} (ho : o ∈ Q \ Z res Q SR) :
    (res o ∩ SR).card = 1 := by
  rw [Finset.mem_sdiff, mem_Z] at ho
  have h1 := cfg.hunit o ho.1
  have hne : (res o ∩ SR).card ≠ 0 := by
    rw [Ne, Finset.card_eq_zero]; exact fun h => ho.2 ⟨ho.1, h⟩
  omega

/-- The shared resource of an outer object outside `Z` lies in `B`. -/
theorem shared_subset_B {o : α} (ho : o ∈ Q \ Z res Q SR) : res o ∩ SR ⊆ B res Q SR :=
  fun r hr => mem_B.mpr ⟨o, ho, hr⟩

/-- Two distinct outer objects in a feasible family have distinct (unit) shared resources; hence
the shared-resource map is injective on `P \ Z`. -/
theorem shared_injOn (cfg : Config res Q D SR) {P : Finset α} (hP : P ⊆ Q) (hf : ResFeasible res P) :
    Set.InjOn (fun o => res o ∩ SR) ((P \ Z res Q SR : Finset α) : Set α) := by
  intro a ha b hb hab
  simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe] at ha hb
  by_contra hne
  have hd := hf ha.1 hb.1 hne
  have hcard := card_shared_eq_one cfg (Finset.mem_sdiff.mpr ⟨hP ha.1, ha.2⟩)
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcard
  have hra : r ∈ res a := (Finset.mem_inter.mp (hr ▸ Finset.mem_singleton_self r)).1
  have hrb : r ∈ res b := by
    have hab' : res a ∩ SR = res b ∩ SR := hab
    have : r ∈ res b ∩ SR := by rw [← hab', hr]; exact Finset.mem_singleton_self r
    exact (Finset.mem_inter.mp this).1
  exact Finset.disjoint_left.mp hd hra hrb

/-! ### Upper bound -/

/-- **Upper bound.** Every feasible `P ⊆ Q ∪ D` has `|P| ≤ z + |B| + ν_D(B)`. -/
theorem card_le_of_feasible (cfg : Config res Q D SR) {P : Finset α} (hPU : P ⊆ Q ∪ D)
    (hf : ResFeasible res P) :
    P.card ≤ (Z res Q SR).card + (B res Q SR).card + nuAvoid res D (B res Q SR) := by
  classical
  set Zs := Z res Q SR with hZs
  set Bs := B res Q SR with hBs
  -- split P into outer / central parts
  set PQ := P ∩ Q with hPQ
  set PD := P ∩ D with hPD
  have hsplit : P.card = PQ.card + PD.card := by
    have hcov : P = PQ ∪ PD := by
      ext x; simp only [hPQ, hPD, Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hx; rcases Finset.mem_union.mp (hPU hx) with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hdis : Disjoint PQ PD := by
      rw [hPQ, hPD]
      exact Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right cfg.hdisj)
    rw [hcov, Finset.card_union_of_disjoint hdis]
  -- outer part: |PQ ∩ Z| ≤ z, and |PQ \ Z| = |B'| with B' ⊆ B the used shared resources
  set B' := (PQ \ Zs).biUnion (fun o => res o ∩ SR) with hB'
  have hPQsub : PQ ⊆ Q := Finset.inter_subset_right
  have hfPQ : ResFeasible res PQ := fun a ha b hb hne => hf (Finset.mem_inter.mp ha).1
    (Finset.mem_inter.mp hb).1 hne
  have hB'sub : B' ⊆ Bs := by
    intro r hr
    rw [hB', Finset.mem_biUnion] at hr
    obtain ⟨o, ho, hro⟩ := hr
    rw [Finset.mem_sdiff] at ho
    exact shared_subset_B (Finset.mem_sdiff.mpr ⟨hPQsub ho.1, ho.2⟩) hro
  have houter : (PQ \ Zs).card = B'.card := by
    -- each o ∈ PQ \ Z has exactly one shared resource; they are pairwise distinct
    rw [hB', Finset.card_biUnion]
    · rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro o ho
      rw [Finset.mem_sdiff] at ho
      exact (card_shared_eq_one cfg (Finset.mem_sdiff.mpr ⟨hPQsub ho.1, ho.2⟩)).symm
    · intro a ha b hb hne
      have hinj := shared_injOn cfg hPQsub hfPQ
      have hne' : res a ∩ SR ≠ res b ∩ SR := fun h => hne (hinj ha hb h)
      have ha' := Finset.mem_sdiff.mp (Finset.mem_coe.mp ha)
      have hb' := Finset.mem_sdiff.mp (Finset.mem_coe.mp hb)
      have hca := card_shared_eq_one cfg (Finset.mem_sdiff.mpr ⟨hPQsub ha'.1, ha'.2⟩)
      have hcb := card_shared_eq_one cfg (Finset.mem_sdiff.mpr ⟨hPQsub hb'.1, hb'.2⟩)
      obtain ⟨ra, hra⟩ := Finset.card_eq_one.mp hca
      obtain ⟨rb, hrb⟩ := Finset.card_eq_one.mp hcb
      show Disjoint (res a ∩ SR) (res b ∩ SR)
      rw [hra, hrb] at hne' ⊢
      rw [Finset.disjoint_singleton]
      exact fun h => hne' (by rw [h])
  have hZpart : (PQ ∩ Zs).card ≤ Zs.card := Finset.card_le_card Finset.inter_subset_right
  have hPQcard : PQ.card = (PQ ∩ Zs).card + (PQ \ Zs).card := by
    rw [Finset.card_inter_add_card_sdiff]
  -- central part: remove one central per resource of B \ B', the rest avoids B
  have hPDsub : PD ⊆ D := Finset.inter_subset_right
  have hfPD : ResFeasible res PD := fun a ha b hb hne => hf (Finset.mem_inter.mp ha).1
    (Finset.mem_inter.mp hb).1 hne
  set PD' := PD.filter (fun d => Disjoint (res d) Bs) with hPD'
  have hPD'le : PD'.card ≤ nuAvoid res D Bs :=
    le_nuAvoid res (fun d hd => hPDsub (Finset.mem_filter.mp hd).1)
      (fun a ha b hb hne => hfPD (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hne)
      (fun d hd => (Finset.mem_filter.mp hd).2)
  -- the removed centrals hit B \ B'
  have hrem : (PD \ PD').card ≤ (Bs \ B').card := by
    apply Finset.card_le_card_of_forall_subsingleton (fun d r => r ∈ res d)
    · intro d hd
      rw [Finset.mem_sdiff, hPD', Finset.mem_filter, not_and] at hd
      have hnd := hd.2 hd.1
      rw [Finset.not_disjoint_iff] at hnd
      obtain ⟨r, hrd, hrB⟩ := hnd
      refine ⟨r, Finset.mem_sdiff.mpr ⟨hrB, ?_⟩, hrd⟩
      intro hrB'
      rw [hB', Finset.mem_biUnion] at hrB'
      obtain ⟨o, ho, hro⟩ := hrB'
      have hoP : o ∈ P := (Finset.mem_inter.mp (Finset.mem_sdiff.mp ho).1).1
      have hdP : d ∈ P := (Finset.mem_inter.mp hd.1).1
      have hne : o ≠ d := by
        intro h; subst h
        exact Finset.disjoint_left.mp cfg.hdisj (hPQsub (Finset.mem_sdiff.mp ho).1) (hPDsub hd.1)
      exact Finset.disjoint_left.mp (hf hoP hdP hne) (Finset.mem_inter.mp hro).1 hrd
    · intro r _ a ha b hb
      simp only [Set.mem_setOf_eq] at ha hb
      by_contra hne
      have hd := hfPD (Finset.mem_sdiff.mp ha.1).1 (Finset.mem_sdiff.mp hb.1).1 hne
      exact Finset.disjoint_left.mp hd ha.2 hb.2
  have hPDcard : (PD \ PD').card + PD'.card = PD.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have hBsplit : (Bs \ B').card + B'.card = Bs.card := Finset.card_sdiff_add_card_eq_card hB'sub
  omega

/-! ### Lower bound: the normalized packing -/

/-- Representative selection for `B`: a choice of an outer object per shared resource. -/
structure Reps (res : α → Finset R) (Q : Finset α) (SR : Finset R) where
  rep : R → α
  rep_mem : ∀ r ∈ B res Q SR, rep r ∈ Q \ Z res Q SR
  rep_uses : ∀ r ∈ B res Q SR, r ∈ res (rep r)

/-- Representatives exist (choose any witness of `mem_B`). -/
theorem exists_reps (res : α → Finset R) (Q : Finset α) (SR : Finset R) [Inhabited α] :
    Nonempty (Reps res Q SR) := by
  classical
  have h : ∀ r ∈ B res Q SR, ∃ o, o ∈ Q \ Z res Q SR ∧ r ∈ res o := by
    intro r hr
    obtain ⟨o, ho, hro⟩ := mem_B.mp hr
    exact ⟨o, ho, (Finset.mem_inter.mp hro).1⟩
  choose! f hf using h
  exact ⟨⟨f, fun r hr => (hf r hr).1, fun r hr => (hf r hr).2⟩⟩

/-- The set of chosen representatives. -/
def repSet (reps : Reps res Q SR) : Finset α := (B res Q SR).image reps.rep

/-- The **normalized packing**: all of `Z`, one representative per resource of `B`, plus a central
family `C`. -/
def normPack (reps : Reps res Q SR) (C : Finset α) : Finset α :=
  Z res Q SR ∪ repSet reps ∪ C

theorem rep_shared_eq (cfg : Config res Q D SR) (reps : Reps res Q SR) {r : R} (hr : r ∈ B res Q SR) :
    res (reps.rep r) ∩ SR = {r} := by
  have h1 := card_shared_eq_one cfg (reps.rep_mem r hr)
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp h1
  have hrmem : r ∈ res (reps.rep r) ∩ SR := by
    rw [Finset.mem_inter]
    refine ⟨reps.rep_uses r hr, ?_⟩
    obtain ⟨o, ho, hro⟩ := mem_B.mp hr
    exact (Finset.mem_inter.mp hro).2
  rw [hs] at hrmem ⊢
  rw [Finset.mem_singleton] at hrmem
  rw [hrmem]

theorem rep_injOn (cfg : Config res Q D SR) (reps : Reps res Q SR) :
    Set.InjOn reps.rep ((B res Q SR : Finset R) : Set R) := by
  intro r hr s hs hrs
  simp only [Finset.mem_coe] at hr hs
  have h1 := rep_shared_eq cfg reps hr
  have h2 := rep_shared_eq cfg reps hs
  rw [hrs] at h1
  rw [h1] at h2
  exact Finset.singleton_injective h2

theorem card_repSet (cfg : Config res Q D SR) (reps : Reps res Q SR) :
    (repSet reps).card = (B res Q SR).card :=
  Finset.card_image_of_injOn (rep_injOn cfg reps)

theorem repSet_subset (reps : Reps res Q SR) : repSet reps ⊆ Q \ Z res Q SR := by
  intro o ho
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ho
  exact reps.rep_mem r hr

/-- Shared resources of a representative lie in `B`. -/
theorem repSet_shared_subset (reps : Reps res Q SR) {o : α} (ho : o ∈ repSet reps) :
    res o ∩ SR ⊆ B res Q SR :=
  shared_subset_B (repSet_subset reps ho)

/-- **Feasibility of the normalized packing** for any feasible central `C ⊆ D` avoiding `B`. -/
theorem normPack_feasible (cfg : Config res Q D SR) (reps : Reps res Q SR) {C : Finset α}
    (hC : C ⊆ D) (hCf : ResFeasible res C) (hCav : ∀ d ∈ C, Disjoint (res d) (B res Q SR)) :
    ResFeasible res (normPack reps C) := by
  classical
  -- outer objects: any two distinct outer objects meet only in SR; a Z-object has nothing in SR;
  -- two reps have distinct singletons in SR.
  have outer : ∀ a ∈ Z res Q SR ∪ repSet reps, ∀ b ∈ Z res Q SR ∪ repSet reps, a ≠ b →
      Disjoint (res a) (res b) := by
    intro a ha b hb hne
    have haQ : a ∈ Q := by
      rcases Finset.mem_union.mp ha with h | h
      · exact Z_subset h
      · exact (Finset.mem_sdiff.mp (repSet_subset reps h)).1
    have hbQ : b ∈ Q := by
      rcases Finset.mem_union.mp hb with h | h
      · exact Z_subset h
      · exact (Finset.mem_sdiff.mp (repSet_subset reps h)).1
    have hmeet := cfg.hQ haQ hbQ hne
    rw [Finset.disjoint_left]
    intro r hra hrb
    have hrSR : r ∈ SR := hmeet (Finset.mem_inter.mpr ⟨hra, hrb⟩)
    rcases Finset.mem_union.mp ha with haZ | haR
    · have := (mem_Z.mp haZ).2
      have : r ∈ res a ∩ SR := Finset.mem_inter.mpr ⟨hra, hrSR⟩
      simp_all
    rcases Finset.mem_union.mp hb with hbZ | hbR
    · have := (mem_Z.mp hbZ).2
      have : r ∈ res b ∩ SR := Finset.mem_inter.mpr ⟨hrb, hrSR⟩
      simp_all
    -- both representatives
    obtain ⟨ra, hraB, rfl⟩ := Finset.mem_image.mp haR
    obtain ⟨rb, hrbB, rfl⟩ := Finset.mem_image.mp hbR
    have ea := rep_shared_eq cfg reps hraB
    have eb := rep_shared_eq cfg reps hrbB
    have hra' : r ∈ res (reps.rep ra) ∩ SR := Finset.mem_inter.mpr ⟨hra, hrSR⟩
    have hrb' : r ∈ res (reps.rep rb) ∩ SR := Finset.mem_inter.mpr ⟨hrb, hrSR⟩
    rw [ea, Finset.mem_singleton] at hra'
    rw [eb, Finset.mem_singleton] at hrb'
    subst hra'; subst hrb'
    exact hne rfl
  intro a ha b hb hne
  unfold normPack at ha hb
  rcases Finset.mem_union.mp ha with haO | haC <;> rcases Finset.mem_union.mp hb with hbO | hbC
  · exact outer a haO b hbO hne
  · -- a outer, b central: res b ⊆ SR avoids B; res a ∩ SR ⊆ B or = ∅
    rw [Finset.disjoint_left]
    intro r hra hrb
    have hrSR : r ∈ SR := cfg.hD b (hC hbC) hrb
    have hrB : r ∉ B res Q SR := Finset.disjoint_left.mp (hCav b hbC) hrb
    rcases Finset.mem_union.mp haO with haZ | haR
    · have := (mem_Z.mp haZ).2
      have : r ∈ res a ∩ SR := Finset.mem_inter.mpr ⟨hra, hrSR⟩
      simp_all
    · exact hrB (repSet_shared_subset reps haR (Finset.mem_inter.mpr ⟨hra, hrSR⟩))
  · rw [Finset.disjoint_left]
    intro r hra hrb
    have hrSR : r ∈ SR := cfg.hD a (hC haC) hra
    have hrB : r ∉ B res Q SR := Finset.disjoint_left.mp (hCav a haC) hra
    rcases Finset.mem_union.mp hbO with hbZ | hbR
    · have := (mem_Z.mp hbZ).2
      have : r ∈ res b ∩ SR := Finset.mem_inter.mpr ⟨hrb, hrSR⟩
      simp_all
    · exact hrB (repSet_shared_subset reps hbR (Finset.mem_inter.mpr ⟨hrb, hrSR⟩))
  · exact hCf haC hbC hne

theorem normPack_subset (reps : Reps res Q SR) {C : Finset α} (hC : C ⊆ D) :
    normPack reps C ⊆ Q ∪ D := by
  unfold normPack
  intro x hx
  rcases Finset.mem_union.mp hx with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union_left _ (Z_subset h)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp (repSet_subset reps h)).1
  · exact Finset.mem_union_right _ (hC h)

/-- `|normPack| = z + |B| + |C|` for central `C ⊆ D`. -/
theorem card_normPack (cfg : Config res Q D SR) (reps : Reps res Q SR) {C : Finset α} (hC : C ⊆ D) :
    (normPack reps C).card = (Z res Q SR).card + (B res Q SR).card + C.card := by
  classical
  unfold normPack
  have h1 : Disjoint (Z res Q SR) (repSet reps) := by
    rw [Finset.disjoint_left]
    intro o hoZ hoR
    exact (Finset.mem_sdiff.mp (repSet_subset reps hoR)).2 hoZ
  have h2 : Disjoint (Z res Q SR ∪ repSet reps) C := by
    rw [Finset.disjoint_left]
    intro o ho hoC
    have hoQ : o ∈ Q := by
      rcases Finset.mem_union.mp ho with h | h
      · exact Z_subset h
      · exact (Finset.mem_sdiff.mp (repSet_subset reps h)).1
    exact Finset.disjoint_left.mp cfg.hdisj hoQ (hC hoC)
  rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1, card_repSet cfg reps]

/-- **Lemma A (unit-boundary completion, exact optimum).**
`packOpt (Q ∪ D) = z + |B| + ν_D(B)`. -/
theorem unitBoundary_completion_optimal (cfg : Config res Q D SR) (reps : Reps res Q SR) :
    packOpt res (Q ∪ D) = (Z res Q SR).card + (B res Q SR).card + nuAvoid res D (B res Q SR) := by
  apply le_antisymm
  · exact packOpt_le res (fun P hP hf => card_le_of_feasible cfg hP hf)
  · obtain ⟨T, hT, hTf, hTav, hTcard⟩ := exists_nuAvoid res D (B res Q SR)
    have hfeas := normPack_feasible cfg reps hT hTf hTav
    have := le_packOpt res (normPack_subset reps hT) hfeas
    rw [card_normPack cfg reps hT, hTcard] at this
    exact this

/-- Lemma A, output form: an explicit optimal packing of the stated shape. -/
theorem exists_optimal_normPack (cfg : Config res Q D SR) (reps : Reps res Q SR) :
    ∃ C ⊆ D, ResFeasible res C ∧ (∀ d ∈ C, Disjoint (res d) (B res Q SR)) ∧
      ResFeasible res (normPack reps C) ∧ (normPack reps C).card = packOpt res (Q ∪ D) := by
  obtain ⟨T, hT, hTf, hTav, hTcard⟩ := exists_nuAvoid res D (B res Q SR)
  refine ⟨T, hT, hTf, hTav, normPack_feasible cfg reps hT hTf hTav, ?_⟩
  rw [card_normPack cfg reps hT, hTcard, unitBoundary_completion_optimal cfg reps]

/-! ### Lemma B: endpoint repacking -/

variable {Q₀ Q₁ : Finset α}

/-- Central objects removed in transport: those hitting `B₁`. -/
def keptCentral (res : α → Finset R) (C₀ : Finset α) (B₁ : Finset R) : Finset α :=
  C₀.filter (fun d => Disjoint (res d) B₁)

/-- Removed centrals avoid `B₀` but hit `B₁`, hence inject into `B₁ \ B₀`:
`h = |C₀| − |C₀'| ≤ |B₁ \ B₀|`. -/
theorem removed_le (res : α → Finset R) {C₀ : Finset α} {B₀ B₁ : Finset R}
    (hC₀f : ResFeasible res C₀) (hC₀av : ∀ d ∈ C₀, Disjoint (res d) B₀) :
    (C₀ \ keptCentral res C₀ B₁).card ≤ (B₁ \ B₀).card := by
  apply Finset.card_le_card_of_forall_subsingleton (fun d r => r ∈ res d)
  · intro d hd
    rw [Finset.mem_sdiff, keptCentral, Finset.mem_filter, not_and] at hd
    have hnd := hd.2 hd.1
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨r, hrd, hrB⟩ := hnd
    exact ⟨r, Finset.mem_sdiff.mpr ⟨hrB, Finset.disjoint_left.mp (hC₀av d hd.1) hrd⟩, hrd⟩
  · intro r _ a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb
    by_contra hne
    have hd := hC₀f (Finset.mem_sdiff.mp ha.1).1 (Finset.mem_sdiff.mp hb.1).1 hne
    exact Finset.disjoint_left.mp hd ha.2 hb.2

/-- **Lemma B (endpoint repacking, explicit witness).** Two outer families `Q₀, Q₁` over the same
central `D` and shared `SR`; `P₀ = normPack reps₀ C₀` with `C₀ ⊆ D` feasible avoiding `B₀`
(not necessarily maximum). Then `P₁ := normPack reps₁ (keptCentral C₀ B₁)` is feasible in `Q₁ ∪ D`,
`|P₁| = z₁ + |B₁| + |C₀| − h` with `h ≤ |B₁ \ B₀|`, and
`|P₀| + z₁ ≤ |P₁| + z₀ + |B₀ \ B₁|`. -/
theorem endpoint_repacking_card_bound (cfg₀ : Config res Q₀ D SR) (cfg₁ : Config res Q₁ D SR)
    (reps₀ : Reps res Q₀ SR) (reps₁ : Reps res Q₁ SR) {C₀ : Finset α} (hC₀ : C₀ ⊆ D)
    (hC₀f : ResFeasible res C₀) (hC₀av : ∀ d ∈ C₀, Disjoint (res d) (B res Q₀ SR)) :
    ResFeasible res (normPack reps₁ (keptCentral res C₀ (B res Q₁ SR))) ∧
      normPack reps₁ (keptCentral res C₀ (B res Q₁ SR)) ⊆ Q₁ ∪ D ∧
      (∃ h ≤ (B res Q₁ SR \ B res Q₀ SR).card,
        (normPack reps₁ (keptCentral res C₀ (B res Q₁ SR))).card + h =
          (Z res Q₁ SR).card + (B res Q₁ SR).card + C₀.card) ∧
      (normPack reps₀ C₀).card + (Z res Q₁ SR).card ≤
        (normPack reps₁ (keptCentral res C₀ (B res Q₁ SR))).card + (Z res Q₀ SR).card +
          (B res Q₀ SR \ B res Q₁ SR).card := by
  classical
  set C₁ := keptCentral res C₀ (B res Q₁ SR) with hC₁
  have hC₁sub : C₁ ⊆ C₀ := Finset.filter_subset _ _
  have hC₁D : C₁ ⊆ D := hC₁sub.trans hC₀
  have hC₁f : ResFeasible res C₁ := fun a ha b hb hne => hC₀f (hC₁sub ha) (hC₁sub hb) hne
  have hC₁av : ∀ d ∈ C₁, Disjoint (res d) (B res Q₁ SR) := fun d hd => (Finset.mem_filter.mp hd).2
  have hfeas := normPack_feasible cfg₁ reps₁ hC₁D hC₁f hC₁av
  have hsub := normPack_subset reps₁ hC₁D (D := D)
  have hcard₀ : (normPack reps₀ C₀).card = (Z res Q₀ SR).card + (B res Q₀ SR).card + C₀.card :=
    card_normPack cfg₀ reps₀ hC₀
  have hcard₁ : (normPack reps₁ C₁).card = (Z res Q₁ SR).card + (B res Q₁ SR).card + C₁.card :=
    card_normPack cfg₁ reps₁ hC₁D
  have hrem := removed_le res hC₀f hC₀av (B₁ := B res Q₁ SR)
  rw [← hC₁] at hrem
  have hCsplit : (C₀ \ C₁).card + C₁.card = C₀.card :=
    Finset.card_sdiff_add_card_eq_card hC₁sub
  refine ⟨hfeas, hsub, ⟨(C₀ \ C₁).card, hrem, by omega⟩, ?_⟩
  -- |B₀| = |B₀ ∩ B₁| + |B₀ \ B₁| ; |B₁| = |B₁ ∩ B₀| + |B₁ \ B₀|
  have hB₀ : (B res Q₀ SR).card =
      (B res Q₀ SR ∩ B res Q₁ SR).card + (B res Q₀ SR \ B res Q₁ SR).card :=
    (Finset.card_inter_add_card_sdiff _ _).symm
  have hB₁ : (B res Q₁ SR).card =
      (B res Q₁ SR ∩ B res Q₀ SR).card + (B res Q₁ SR \ B res Q₀ SR).card :=
    (Finset.card_inter_add_card_sdiff _ _).symm
  have hinter : (B res Q₀ SR ∩ B res Q₁ SR).card = (B res Q₁ SR ∩ B res Q₀ SR).card := by
    rw [Finset.inter_comm]
  omega

/-- **Corollary (non-loss).** If `B₀ ⊆ B₁` and `z₀ ≤ z₁` then the transported packing is at least as
large: `|P₀| ≤ |P₁|`. -/
theorem endpoint_repacking_nonloss (cfg₀ : Config res Q₀ D SR) (cfg₁ : Config res Q₁ D SR)
    (reps₀ : Reps res Q₀ SR) (reps₁ : Reps res Q₁ SR) {C₀ : Finset α} (hC₀ : C₀ ⊆ D)
    (hC₀f : ResFeasible res C₀) (hC₀av : ∀ d ∈ C₀, Disjoint (res d) (B res Q₀ SR))
    (hB : B res Q₀ SR ⊆ B res Q₁ SR) (hz : (Z res Q₀ SR).card ≤ (Z res Q₁ SR).card) :
    (normPack reps₀ C₀).card ≤ (normPack reps₁ (keptCentral res C₀ (B res Q₁ SR))).card := by
  obtain ⟨_, _, _, hineq⟩ :=
    endpoint_repacking_card_bound cfg₀ cfg₁ reps₀ reps₁ hC₀ hC₀f hC₀av
  have hsd : (B res Q₀ SR \ B res Q₁ SR).card = 0 := by
    rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]; exact hB
  omega

end UnitBoundary

end PaperV
