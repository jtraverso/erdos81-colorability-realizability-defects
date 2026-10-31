/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Load-2 triangle systems: pairwise edge-sharing triangles span a physical `K₄`
(DV27 combinatorial kernel).

If three distinct triangles pairwise share an edge and no edge lies in all three (edge-load ≤ 2),
then the third lies inside the 4-set spanned by the first two, that 4-set is a `K₄` of `G`, and any
family of pairwise edge-sharing triangles with load ≤ 2 has at most 4 members (the faces of one `K₄`).
In the conflict graph `H[X]` / `F_X` of a load-2 triangle multiset this says: every clique of the
conflict graph is `K₃` or `K₄` and comes from a physical `K₄` of `G`.
The clique-partition discount `cp(G) ≤ |E| − |X| + oct(F₀) − 2a − b` (DV27) is Paper V's.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.Copy

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [DecidableEq V]

/-- Two distinct 3-sets sharing at least two elements share exactly two. -/
theorem inter_card_eq_two_of_ne {t₁ t₂ : Finset V} (h1 : t₁.card = 3) (h2 : t₂.card = 3)
    (h12 : 2 ≤ (t₁ ∩ t₂).card) (hne : t₁ ≠ t₂) : (t₁ ∩ t₂).card = 2 := by
  have hle : (t₁ ∩ t₂).card ≤ 3 := h1 ▸ Finset.card_le_card Finset.inter_subset_left
  rcases (show (t₁ ∩ t₂).card = 2 ∨ (t₁ ∩ t₂).card = 3 by omega) with h | h
  · exact h
  · exfalso
    have e1 : t₁ ∩ t₂ = t₁ := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have e2 : t₁ ∩ t₂ = t₂ := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (e1.symm.trans e2)

/-- The union of two distinct edge-sharing triangles has exactly four vertices. -/
theorem card_union_eq_four {t₁ t₂ : Finset V} (h1 : t₁.card = 3) (h2 : t₂.card = 3)
    (h12 : 2 ≤ (t₁ ∩ t₂).card) (hne : t₁ ≠ t₂) : (t₁ ∪ t₂).card = 4 := by
  have := Finset.card_union_add_card_inter t₁ t₂
  have := inter_card_eq_two_of_ne h1 h2 h12 hne
  omega

/-- **Load-2 kernel.** A third triangle sharing an edge with each of two edge-sharing
triangles, with no edge common to all three, lies inside their 4-vertex union. -/
theorem third_subset_union {t₁ t₂ t₃ : Finset V} (h3 : t₃.card = 3)
    (h13 : 2 ≤ (t₁ ∩ t₃).card) (h23 : 2 ≤ (t₂ ∩ t₃).card)
    (hload : (t₁ ∩ t₂ ∩ t₃).card < 2) : t₃ ⊆ t₁ ∪ t₂ := by
  by_contra hnot
  obtain ⟨x, hx3, hxU⟩ := Finset.not_subset.mp hnot
  have hx1 : x ∉ t₁ := fun h => hxU (Finset.mem_union_left _ h)
  have hx2 : x ∉ t₂ := fun h => hxU (Finset.mem_union_right _ h)
  have hcard : (t₃.erase x).card = 2 := by rw [Finset.card_erase_of_mem hx3, h3]
  have hs1 : t₁ ∩ t₃ ⊆ t₃.erase x := by
    intro y hy
    rw [Finset.mem_inter] at hy
    rw [Finset.mem_erase]
    exact ⟨fun h => hx1 (h ▸ hy.1), hy.2⟩
  have hs2 : t₂ ∩ t₃ ⊆ t₃.erase x := by
    intro y hy
    rw [Finset.mem_inter] at hy
    rw [Finset.mem_erase]
    exact ⟨fun h => hx2 (h ▸ hy.1), hy.2⟩
  have e1 : t₁ ∩ t₃ = t₃.erase x := Finset.eq_of_subset_of_card_le hs1 (by omega)
  have e2 : t₂ ∩ t₃ = t₃.erase x := Finset.eq_of_subset_of_card_le hs2 (by omega)
  have hsub : t₃.erase x ⊆ t₁ ∩ t₂ ∩ t₃ := by
    intro y hy
    have hy1 : y ∈ t₁ ∩ t₃ := e1 ▸ hy
    have hy2 : y ∈ t₂ ∩ t₃ := e2 ▸ hy
    rw [Finset.mem_inter] at hy1 hy2 ⊢
    exact ⟨Finset.mem_inter.mpr ⟨hy1.1, hy2.1⟩, hy1.2⟩
  have := Finset.card_le_card hsub
  omega

/-- A third load-2 triangle distinct from the first two contains every non-shared vertex of
their union: it misses exactly one vertex of the 4-set, and that vertex is a shared one. -/
theorem private_mem_third {t₁ t₂ t₃ : Finset V} (h1 : t₁.card = 3) (h2 : t₂.card = 3)
    (h3 : t₃.card = 3) (h12 : 2 ≤ (t₁ ∩ t₂).card) (h13 : 2 ≤ (t₁ ∩ t₃).card)
    (h23 : 2 ≤ (t₂ ∩ t₃).card) (hne12 : t₁ ≠ t₂) (hne13 : t₁ ≠ t₃) (hne23 : t₂ ≠ t₃)
    (hload : (t₁ ∩ t₂ ∩ t₃).card < 2) {a : V} (ha : a ∈ t₁ ∪ t₂) (ha' : a ∉ t₁ ∩ t₂) :
    a ∈ t₃ := by
  have hsub := third_subset_union h3 h13 h23 hload
  have hU := card_union_eq_four h1 h2 h12 hne12
  by_contra hna
  have hdiff : ((t₁ ∪ t₂) \ t₃).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hU, h3]
  have hamem : a ∈ (t₁ ∪ t₂) \ t₃ := Finset.mem_sdiff.mpr ⟨ha, hna⟩
  have hsingle : (t₁ ∪ t₂) \ t₃ = {a} := by
    rw [Finset.card_eq_one] at hdiff
    obtain ⟨b, hb⟩ := hdiff
    rw [hb] at hamem ⊢
    rw [Finset.mem_singleton] at hamem
    rw [hamem]
  have hin : ∀ y ∈ t₁ ∪ t₂, y ≠ a → y ∈ t₃ := by
    intro y hy hya
    by_contra hy3
    have : y ∈ (t₁ ∪ t₂) \ t₃ := Finset.mem_sdiff.mpr ⟨hy, hy3⟩
    rw [hsingle, Finset.mem_singleton] at this
    exact hya this
  rw [Finset.mem_inter, not_and_or] at ha'
  rcases ha' with ha1 | ha2
  · have : t₁ ⊆ t₃ := fun y hy => hin y (Finset.mem_union_left _ hy) (fun h => ha1 (h ▸ hy))
    exact hne13 (Finset.eq_of_subset_of_card_le this (by omega))
  · have : t₂ ⊆ t₃ := fun y hy => hin y (Finset.mem_union_right _ hy) (fun h => ha2 (h ▸ hy))
    exact hne23 (Finset.eq_of_subset_of_card_le this (by omega))

/-- **Three pairwise edge-sharing load-2 triangles of `G` span a `K₄` of `G`.** -/
theorem k4_of_three_triangles (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype V]
    {t₁ t₂ t₃ : Finset V} (ht₁ : t₁ ∈ G.cliqueFinset 3) (ht₂ : t₂ ∈ G.cliqueFinset 3)
    (ht₃ : t₃ ∈ G.cliqueFinset 3) (h12 : 2 ≤ (t₁ ∩ t₂).card) (h13 : 2 ≤ (t₁ ∩ t₃).card)
    (h23 : 2 ≤ (t₂ ∩ t₃).card) (hne12 : t₁ ≠ t₂) (hne13 : t₁ ≠ t₃) (hne23 : t₂ ≠ t₃)
    (hload : (t₁ ∩ t₂ ∩ t₃).card < 2) :
    t₁ ∪ t₂ ∈ G.cliqueFinset 4 := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht₁ ht₂ ht₃ ⊢
  have h1 := ht₁.2; have h2 := ht₂.2; have h3 := ht₃.2
  refine ⟨?_, card_union_eq_four h1 h2 h12 hne12⟩
  intro a ha b hb hab
  rw [Finset.mem_coe] at ha hb
  have key : ∀ x ∈ t₁ ∪ t₂, x ∉ t₁ ∩ t₂ → x ∈ t₃ := fun x hx hx' =>
    private_mem_third h1 h2 h3 h12 h13 h23 hne12 hne13 hne23 hload hx hx'
  by_cases ha1 : a ∈ t₁ <;> by_cases hb1 : b ∈ t₁
  · exact ht₁.1 ha1 hb1 hab
  · by_cases ha2 : a ∈ t₂
    · have hb2 : b ∈ t₂ := (Finset.mem_union.mp hb).resolve_left hb1
      exact ht₂.1 ha2 hb2 hab
    · exact ht₃.1 (key a ha (fun h => ha2 (Finset.mem_inter.mp h).2))
        (key b hb (fun h => hb1 (Finset.mem_inter.mp h).1)) hab
  · by_cases hb2 : b ∈ t₂
    · have ha2 : a ∈ t₂ := (Finset.mem_union.mp ha).resolve_left ha1
      exact ht₂.1 ha2 hb2 hab
    · exact ht₃.1 (key a ha (fun h => ha1 (Finset.mem_inter.mp h).1))
        (key b hb (fun h => hb2 (Finset.mem_inter.mp h).2)) hab
  · have ha2 : a ∈ t₂ := (Finset.mem_union.mp ha).resolve_left ha1
    have hb2 : b ∈ t₂ := (Finset.mem_union.mp hb).resolve_left hb1
    exact ht₂.1 ha2 hb2 hab

/-- **At most four.** A family of 3-sets, pairwise sharing ≥ 2 elements, with no element-pair in
three of them, has at most 4 members (all lie in one 4-set). -/
theorem card_le_four_of_pairwise_share (T : Finset (Finset V))
    (hcard : ∀ t ∈ T, t.card = 3)
    (hpair : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → 2 ≤ (t ∩ s).card)
    (hload : ∀ t ∈ T, ∀ s ∈ T, ∀ u ∈ T, t ≠ s → t ≠ u → s ≠ u → (t ∩ s ∩ u).card < 2) :
    T.card ≤ 4 := by
  by_cases hsmall : T.card ≤ 2
  · omega
  · obtain ⟨t₁, ht₁, t₂, ht₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
    have hsub : T ⊆ (t₁ ∪ t₂).powersetCard 3 := by
      intro t ht
      rw [Finset.mem_powersetCard]
      refine ⟨?_, hcard t ht⟩
      by_cases e1 : t = t₁
      · subst e1; exact Finset.subset_union_left
      by_cases e2 : t = t₂
      · subst e2; exact Finset.subset_union_right
      exact third_subset_union (hcard t ht)
        (hpair t₁ ht₁ t ht (Ne.symm e1)) (hpair t₂ ht₂ t ht (Ne.symm e2))
        (hload t₁ ht₁ t₂ ht₂ t ht hne (Ne.symm e1) (Ne.symm e2))
    calc T.card ≤ ((t₁ ∪ t₂).powersetCard 3).card := Finset.card_le_card hsub
      _ = Nat.choose 4 3 := by
          rw [Finset.card_powersetCard, card_union_eq_four (hcard t₁ ht₁) (hcard t₂ ht₂)
            (hpair t₁ ht₁ t₂ ht₂ hne) hne]
      _ = 4 := by decide

/-- Bridge to the triangle conflict system `triCS G`: a set of triangles pairwise in conflict
(`K`), with edge-load ≤ 2 on every triple, has at most four members. -/
theorem triCS_clique_card_le_four (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype V]
    (T : Finset (triCS G).O)
    (hK : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → (triCS G).K t s)
    (hload : ∀ t ∈ T, ∀ s ∈ T, ∀ u ∈ T, t ≠ s → t ≠ u → s ≠ u →
      (t.1 ∩ s.1 ∩ u.1).card < 2) :
    T.card ≤ 4 := by
  have hinj : Set.InjOn (fun t : (triCS G).O => t.1) T := fun a _ b _ h => Subtype.ext h
  rw [← Finset.card_image_of_injOn hinj]
  apply card_le_four_of_pairwise_share
  · intro t ht
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp ht
    exact (SimpleGraph.mem_cliqueFinset_iff.mp s.2).2
  · intro t ht s hs hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
    exact (hK a ha b hb (fun h => hne (congrArg Subtype.val h))).2
  · intro t ht s hs u hu h1 h2 h3
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hu
    exact hload a ha b hb c hc (fun h => h1 (congrArg Subtype.val h))
      (fun h => h2 (congrArg Subtype.val h)) (fun h => h3 (congrArg Subtype.val h))

end PaperV
