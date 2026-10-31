/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV/V — §4.1 copy inequalities, N1 part (a): the copy graph `H[T₂]` is subcubic
(`triangle_Hgraph_maxDegree_le_three`). Split of the former `Copy.lean` (2026-09-14); statements unchanged.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.CopyCore

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Claim 4.1a, abstracted from the copy construction: an edge load bound of two makes the
triangle-copy conflict graph subcubic. -/
lemma triangle_Hgraph_maxDegree_le_three
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : (triCS G).O → ℕ)
    (hload : ∀ e : Finset V, e.card = 2 →
      (∑ t : (triCS G).O, if e ⊆ t.1 then X t else 0) ≤ 2) :
    (Hgraph (triCS G) X).maxDegree ≤ 3 := by
  rw [SimpleGraph.maxDegree]
  -- Need to show: WithBot.unbotD 0 (image (fun v => degree v) univ).max ≤ 3
  have hle : ∀ v : Copies (triCS G) X, (Hgraph (triCS G) X).degree v ≤ 3 := by
    intro ⟨t, i⟩
    simp only [SimpleGraph.degree]
    -- First show X t ≤ 2 using the edge-load condition
    have hxt : X t ≤ 2 := by
      -- t is a triangle, so t.1 has 3 elements
      have ht_card : t.1.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp t.2).2
      -- Get an element a ∈ t.1
      have ht_ne : t.1.Nonempty := Finset.card_pos.mp (ht_card.symm ▸ by norm_num : 0 < t.1.card)
      obtain ⟨a, ha⟩ := ht_ne
      -- Get another element b ∈ t.1, b ≠ a
      have ht_erase_pos : 0 < (t.1.erase a).card := by rw [Finset.card_erase_of_mem ha, ht_card]; norm_num
      obtain ⟨b, hb⟩ := Finset.card_pos.mp ht_erase_pos
      have hb_in : b ∈ t.1 := Finset.mem_of_mem_erase hb
      have hab : a ≠ b := by
        intro heq
        rw [heq] at hb
        simp at hb
      -- The edge {a, b} has load ≤ 2
      have he : ({a, b} : Finset V).card = 2 := Finset.card_pair hab
      have hload_t := hload {a, b} he
      -- t contains edge {a, b}
      have ht_edge : ({a, b} : Finset V) ⊆ t.1 := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> [exact ha; exact hb_in]
      have hmem : t ∈ Finset.univ := Finset.mem_univ t
      have hmono : X t ≤ ∑ s : (triCS G).O, (if {a, b} ⊆ s.1 then X s else 0) := by
        have := Finset.single_le_sum (fun s _ => Nat.zero_le (if {a, b} ⊆ s.1 then X s else 0)) hmem
        simp [ht_edge] at this
        exact this
      linarith
    -- Now bound the degree
    -- degree = (X t - 1) + ∑_{t' : K t t'} X t'
    -- We'll show degree ≤ 3
    -- The neighbors of (t, i) are:
    -- 1. Twin copies: (t, j) for j ≠ i  →  X t - 1 neighbors
    -- 2. Conflicting triangles: (t', j) for t' with K t t' and any j
    -- We need to show degree ≤ 3
    -- First, let's characterize the neighbor set
    have hneight : X t ≥ 1 := by
      have : i.val < X t := i.2
      omega
    -- Degree bound: degree ≤ (X t - 1) + ∑_{t' : K t t'} X t'
    -- Since X t ≤ 2 and X t ≥ 1, we have X t ∈ {1, 2}
    -- Key observation: each edge of t has load ≤ 2
    -- Each conflicting triangle shares at least one edge with t
    -- So ∑_{t' : K t t'} X t' ≤ ∑_{e ∈ edges(t)} (load at e - X t) ≤ 3 * (2 - X t)
    -- Therefore degree ≤ (X t - 1) + 3*(2 - X t) = 5 - 2*X t ≤ 3
    -- Case analysis on X t ∈ {1, 2}
    have hxteq : X t = 1 ∨ X t = 2 := by omega
    rcases hxteq with hxteq | hxteq
    · -- X t = 1: need to show degree ≤ 3
      -- Each edge of t can have load ≤ 2, and X t = 1, so each edge contributes ≤ 1 from conflicts
      -- Total conflicts ≤ 3
      have hxteq' : X t = 1 := hxteq
      -- Get the 3 elements of t
      have ht_card : t.1.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp t.2).2
      obtain ⟨a, b, c, hab, hac, hbc, heq⟩ := Finset.card_eq_three.mp ht_card
      -- Each edge of t has load ≤ 2
      have load_ab := hload {a, b} (by rw [Finset.card_pair hab])
      have load_bc := hload {b, c} (by rw [Finset.card_pair hbc])
      have load_ac := hload {a, c} (by rw [Finset.card_pair hac])
      -- t contains all three edges
      have ht_ab : ({a, b} : Finset V) ⊆ {a, b, c} := by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      have ht_bc : ({b, c} : Finset V) ⊆ {a, b, c} := by simp
      have ht_ac : ({a, c} : Finset V) ⊆ {a, b, c} := by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      -- X t = 1 contributes to each load
      have sum_ab : X t ≤ ∑ s : (triCS G).O, (if {a, b} ⊆ s.1 then X s else 0) := by
        have h := Finset.single_le_sum (fun s _ => Nat.zero_le (if {a, b} ⊆ s.1 then X s else 0)) (Finset.mem_univ t)
        simp [heq, ht_ab] at h
        exact h
      have sum_bc : X t ≤ ∑ s : (triCS G).O, (if {b, c} ⊆ s.1 then X s else 0) := by
        have h := Finset.single_le_sum (fun s _ => Nat.zero_le (if {b, c} ⊆ s.1 then X s else 0)) (Finset.mem_univ t)
        simp [heq, ht_bc] at h
        exact h
      have sum_ac : X t ≤ ∑ s : (triCS G).O, (if {a, c} ⊆ s.1 then X s else 0) := by
        have h := Finset.single_le_sum (fun s _ => Nat.zero_le (if {a, c} ⊆ s.1 then X s else 0)) (Finset.mem_univ t)
        simp [heq, ht_ac] at h
        exact h
      -- Each sum is ≤ 2, and X t = 1, so remaining capacity per edge is ≤ 1
      -- Bound the degree: degree ≤ sum over edges of (load - X t) ≤ 3 * 1 = 3
      simp only [SimpleGraph.card_neighborFinset_eq_degree]
      -- The neighbors are either twins (none since X t = 1) or conflicts
      -- For each conflict s, it shares at least one edge e with t, and X s contributes to load at e
      -- Total sum of X s over conflicts ≤ sum over edges of (load - X t) ≤ 3
      -- Let S be the set of conflicting triangles
      let S := Finset.filter (fun s : (triCS G).O => (triCS G).K t s) Finset.univ
      -- First, the neighborFinset is contained in the image of conflicting triangles
      have hsub : ((Hgraph (triCS G) X).neighborFinset ⟨t, i⟩) ⊆
          S.biUnion fun s => Finset.image (fun j : Fin (X s) => (⟨s, j⟩ : Copies (triCS G) X)) Finset.univ := by
        intro ⟨s, j⟩ hj
        rw [SimpleGraph.mem_neighborFinset] at hj
        have ⟨hne, hadj⟩ := hj
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
        rcases hadj with ⟨rfl, hne⟩ | hKs
        · -- Twins: s = t, but X t = 1 means j = i, contradiction
          exfalso
          have hij : j = i := by
            have hj_lt : j.val < X t := j.2
            simp [hxteq'] at hj_lt
            have hi_lt : i.val < X t := i.2
            simp [hxteq'] at hi_lt
            omega
          exact hne (by simp [hij])
        · -- Conflicts
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨s, hKs, j, rfl⟩
      have hcard_le : ((Hgraph (triCS G) X).neighborFinset ⟨t, i⟩).card ≤
          (S.biUnion fun s => Finset.image (fun j : Fin (X s) => (⟨s, j⟩ : Copies (triCS G) X)) Finset.univ).card :=
        Finset.card_le_card hsub
      -- Now bound the biUnion cardinality
      -- #(S.biUnion (fun s => image (fun j => ⟨s, j⟩) univ)) = ∑ s ∈ S, X s
      have hinj : ∀ s : (triCS G).O, Function.Injective (fun j : Fin (X s) => (⟨s, j⟩ : Copies (triCS G) X)) := fun s =>
        fun a b h => by simp at h; exact h
      have hpairwise : (S : Set (triCS G).O).Pairwise (fun s s' => Disjoint (Finset.image (fun j : Fin (X s) => (⟨s, j⟩ : Copies (triCS G) X)) Finset.univ)
          (Finset.image (fun j : Fin (X s') => (⟨s', j⟩ : Copies (triCS G) X)) Finset.univ)) := by
        intro s hs s' hs' hss'
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finset.mem_image] at hx1 hx2
        obtain ⟨a, _, ha⟩ := hx1
        obtain ⟨b, _, hb⟩ := hx2
        have hs_eq : s = s' := by
          have ha' : s = x.1 := by simpa using congrArg (fun p : Copies (triCS G) X => p.1) ha
          have hb' : s' = x.1 := by simpa using congrArg (fun p : Copies (triCS G) X => p.1) hb
          exact ha'.trans hb'.symm
        exact hss' hs_eq
      have hbiUnion_card : (S.biUnion fun s => Finset.image (fun j : Fin (X s) => (⟨s, j⟩ : Copies (triCS G) X)) Finset.univ).card =
          ∑ s ∈ S, X s := by
        rw [Finset.card_biUnion]
        · simp only [Finset.card_image_of_injective _ (hinj _), Finset.card_fin]
        · assumption
      -- Now show ∑ s ∈ S, X s ≤ 3
      -- Each edge e of t has load ≤ 2, and X t = 1, so sum over s with e ⊆ s.1 of X s ≤ 1
      -- Since each s ∈ S shares at least one edge with t, sum over S ≤ sum over edges ≤ 3
      have hdeg_eq : (Hgraph (triCS G) X).degree ⟨t, i⟩ = ((Hgraph (triCS G) X).neighborFinset ⟨t, i⟩).card :=
        SimpleGraph.card_neighborFinset_eq_degree _ _
      rw [hdeg_eq]
      calc ((Hgraph (triCS G) X).neighborFinset ⟨t, i⟩).card
        ≤ (S.biUnion fun s => Finset.image (fun j : Fin (X s) => (⟨s, j⟩ : Copies (triCS G) X)) Finset.univ).card := hcard_le
        _ = ∑ s ∈ S, X s := hbiUnion_card
        _ ≤ 3 := by
          -- X t = 1 contributes to each edge sum
          have term_ab : X t ≤ ∑ s : (triCS G).O, (if {a, b} ⊆ s.1 then X s else 0) := by
            have h := Finset.single_le_sum (fun s _ => Nat.zero_le (if {a, b} ⊆ s.1 then X s else 0)) (Finset.mem_univ t)
            rw [heq] at h
            simp [ht_ab] at h
            exact h
          have term_bc : X t ≤ ∑ s : (triCS G).O, (if {b, c} ⊆ s.1 then X s else 0) := by
            have h := Finset.single_le_sum (fun s _ => Nat.zero_le (if {b, c} ⊆ s.1 then X s else 0)) (Finset.mem_univ t)
            rw [heq] at h
            simp [ht_bc] at h
            exact h
          have term_ac : X t ≤ ∑ s : (triCS G).O, (if {a, c} ⊆ s.1 then X s else 0) := by
            have h := Finset.single_le_sum (fun s _ => Nat.zero_le (if {a, c} ⊆ s.1 then X s else 0)) (Finset.mem_univ t)
            rw [heq] at h
            simp [ht_ac] at h
            exact h
          -- So remaining capacity per edge is ≤ 1
          have cap_ab : ∑ s : (triCS G).O, (if {a, b} ⊆ s.1 then X s else 0) - X t ≤ 1 := by omega
          have cap_bc : ∑ s : (triCS G).O, (if {b, c} ⊆ s.1 then X s else 0) - X t ≤ 1 := by omega
          have cap_ac : ∑ s : (triCS G).O, (if {a, c} ⊆ s.1 then X s else 0) - X t ≤ 1 := by omega
          -- Each s ∈ S shares an edge with t
          have hS_edge : ∀ s ∈ S, ({a, b} ⊆ s.1 ∨ {b, c} ⊆ s.1 ∨ {a, c} ⊆ s.1) := by
            intro s hs
            have hmem := Finset.mem_filter.mp hs
            have hK := hmem.2
            have hcard2 : 2 ≤ (t.1 ∩ s.1).card := hK.2
            rw [heq] at hcard2
            rcases Finset.one_lt_card.mp hcard2 with ⟨x, hx, y, hy, hxy⟩
            have hx_s : x ∈ s.1 := Finset.mem_of_mem_inter_right hx
            have hy_s : y ∈ s.1 := Finset.mem_of_mem_inter_right hy
            have hx_mem : x = a ∨ x = b ∨ x = c := by
              have := Finset.mem_of_mem_inter_left hx; simp at this; exact this
            have hy_mem : y = a ∨ y = b ∨ y = c := by
              have := Finset.mem_of_mem_inter_left hy; simp at this; exact this
            rcases hx_mem with rfl | rfl | rfl <;> rcases hy_mem with rfl | rfl | rfl <;> grind
          have hmono : ∀ s ∈ S, X s ≤ (if {a, b} ⊆ s.1 then X s else 0) +
                                  (if {b, c} ⊆ s.1 then X s else 0) +
                                  (if {a, c} ⊆ s.1 then X s else 0) := by
            intro s hs
            rcases hS_edge s hs with h1 | h2 | h3
            · simp only [h1, ↓reduceIte]
              omega
            · simp only [h2, ↓reduceIte]
              omega
            · simp only [h3, ↓reduceIte]
              omega
          -- Bound sum over S by sum over all minus t
          have sub_ab : ∑ s ∈ S, (if {a, b} ⊆ s.1 then X s else 0) ≤
                        ∑ s : (triCS G).O, (if {a, b} ⊆ s.1 then X s else 0) - X t := by
            have h : ∑ s : (triCS G).O, (if {a, b} ⊆ s.1 then X s else 0) =
                     X t + ∑ s ∈ Finset.univ.erase t, (if {a, b} ⊆ s.1 then X s else 0) := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
              simp [if_pos (heq ▸ ht_ab)]
            have hS_sub : S ⊆ Finset.univ.erase t := by
              intro s hs
              have hK := (Finset.mem_filter.mp hs).2
              simp [Finset.mem_erase, Finset.mem_univ]
              exact fun h => hK.1 (by rw [h])
            calc ∑ s ∈ S, (if {a, b} ⊆ s.1 then X s else 0)
                ≤ ∑ s ∈ Finset.univ.erase t, (if {a, b} ⊆ s.1 then X s else 0) :=
                  Finset.sum_le_sum_of_subset hS_sub
              _ = (X t + ∑ s ∈ Finset.univ.erase t, (if {a, b} ⊆ s.1 then X s else 0)) - X t := by omega
              _ = ∑ s : (triCS G).O, (if {a, b} ⊆ s.1 then X s else 0) - X t := by rw [h]
          have sub_bc : ∑ s ∈ S, (if {b, c} ⊆ s.1 then X s else 0) ≤
                        ∑ s : (triCS G).O, (if {b, c} ⊆ s.1 then X s else 0) - X t := by
            have h : ∑ s : (triCS G).O, (if {b, c} ⊆ s.1 then X s else 0) =
                     X t + ∑ s ∈ Finset.univ.erase t, (if {b, c} ⊆ s.1 then X s else 0) := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
              simp [if_pos (heq ▸ ht_bc)]
            have hS_sub : S ⊆ Finset.univ.erase t := by
              intro s hs
              have hK := (Finset.mem_filter.mp hs).2
              simp [Finset.mem_erase, Finset.mem_univ]
              exact fun h => hK.1 (by rw [h])
            calc ∑ s ∈ S, (if {b, c} ⊆ s.1 then X s else 0)
                ≤ ∑ s ∈ Finset.univ.erase t, (if {b, c} ⊆ s.1 then X s else 0) :=
                  Finset.sum_le_sum_of_subset hS_sub
              _ = (X t + ∑ s ∈ Finset.univ.erase t, (if {b, c} ⊆ s.1 then X s else 0)) - X t := by omega
              _ = ∑ s : (triCS G).O, (if {b, c} ⊆ s.1 then X s else 0) - X t := by rw [h]
          have sub_ac : ∑ s ∈ S, (if {a, c} ⊆ s.1 then X s else 0) ≤
                        ∑ s : (triCS G).O, (if {a, c} ⊆ s.1 then X s else 0) - X t := by
            have h : ∑ s : (triCS G).O, (if {a, c} ⊆ s.1 then X s else 0) =
                     X t + ∑ s ∈ Finset.univ.erase t, (if {a, c} ⊆ s.1 then X s else 0) := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
              simp [if_pos (heq ▸ ht_ac)]
            have hS_sub : S ⊆ Finset.univ.erase t := by
              intro s hs
              have hK := (Finset.mem_filter.mp hs).2
              simp [Finset.mem_erase, Finset.mem_univ]
              exact fun h => hK.1 (by rw [h])
            calc ∑ s ∈ S, (if {a, c} ⊆ s.1 then X s else 0)
                ≤ ∑ s ∈ Finset.univ.erase t, (if {a, c} ⊆ s.1 then X s else 0) :=
                  Finset.sum_le_sum_of_subset hS_sub
              _ = (X t + ∑ s ∈ Finset.univ.erase t, (if {a, c} ⊆ s.1 then X s else 0)) - X t := by omega
              _ = ∑ s : (triCS G).O, (if {a, c} ⊆ s.1 then X s else 0) - X t := by rw [h]
          calc ∑ s ∈ S, X s ≤ ∑ s ∈ S, ((if {a, b} ⊆ s.1 then X s else 0) +
                                        (if {b, c} ⊆ s.1 then X s else 0) +
                                        (if {a, c} ⊆ s.1 then X s else 0)) :=
                   Finset.sum_le_sum hmono
            _ = ∑ s ∈ S, (if {a, b} ⊆ s.1 then X s else 0) +
                ∑ s ∈ S, (if {b, c} ⊆ s.1 then X s else 0) +
                ∑ s ∈ S, (if {a, c} ⊆ s.1 then X s else 0) := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            _ ≤ (∑ s : (triCS G).O, (if {a, b} ⊆ s.1 then X s else 0) - X t) +
                (∑ s : (triCS G).O, (if {b, c} ⊆ s.1 then X s else 0) - X t) +
                (∑ s : (triCS G).O, (if {a, c} ⊆ s.1 then X s else 0) - X t) := by linarith [sub_ab, sub_bc, sub_ac]
            _ ≤ 1 + 1 + 1 := by linarith [cap_ab, cap_bc, cap_ac]
            _ ≤ 3 := by norm_num
    · -- X t = 2: need to show degree ≤ 3
      -- When X t = 2, each edge e of t has ∑_{s : e ⊆ s.1} X s ≤ 2
      -- Since t contains e and X t = 2, the sum equals 2 and X s = 0 for all other s containing e
      have hxteq' : X t = 2 := hxteq
      -- Get the 3 elements of t
      have ht_card : t.1.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp t.2).2
      obtain ⟨a, b, c, hab, hac, hbc, heq⟩ := Finset.card_eq_three.mp ht_card
      -- Each edge of t has load ≤ 2
      have load_ab := hload {a, b} (by rw [Finset.card_pair hab])
      have load_bc := hload {b, c} (by rw [Finset.card_pair hbc])
      have load_ac := hload {a, c} (by rw [Finset.card_pair hac])
      -- t contains all three edges
      have ht_ab : ({a, b} : Finset V) ⊆ {a, b, c} := by
        simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      have ht_bc : ({b, c} : Finset V) ⊆ {a, b, c} := by
        simp
      have ht_ac : ({a, c} : Finset V) ⊆ {a, b, c} := by
        simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      -- So X t contributes to each load, and X t = 2 means load is exhausted
      have sum_ab : X t ≤ ∑ s : (triCS G).O, (if {a, b} ⊆ s.1 then X s else 0) := by
        have h := Finset.single_le_sum (fun s _ => Nat.zero_le (if {a, b} ⊆ s.1 then X s else 0)) (Finset.mem_univ t)
        simp [heq, ht_ab] at h
        exact h
      have sum_bc : X t ≤ ∑ s : (triCS G).O, (if {b, c} ⊆ s.1 then X s else 0) := by
        have h := Finset.single_le_sum (fun s _ => Nat.zero_le (if {b, c} ⊆ s.1 then X s else 0)) (Finset.mem_univ t)
        simp [heq, ht_bc] at h
        exact h
      have sum_ac : X t ≤ ∑ s : (triCS G).O, (if {a, c} ⊆ s.1 then X s else 0) := by
        have h := Finset.single_le_sum (fun s _ => Nat.zero_le (if {a, c} ⊆ s.1 then X s else 0)) (Finset.mem_univ t)
        simp [heq, ht_ac] at h
        exact h
      -- Therefore each sum equals X t = 2
      have hsum_ab : ∑ s : (triCS G).O, (if {a, b} ⊆ s.1 then X s else 0) = 2 := by omega
      have hsum_bc : ∑ s : (triCS G).O, (if {b, c} ⊆ s.1 then X s else 0) = 2 := by omega
      have hsum_ac : ∑ s : (triCS G).O, (if {a, c} ⊆ s.1 then X s else 0) = 2 := by omega
      -- Any triangle s conflicting with t shares at least one edge with t
      -- If s shares an edge, then X s = 0 (since the sum is exactly 2 = X t)
      have hnoX : ∀ s : (triCS G).O, (triCS G).K t s → X s = 0 := by
        intro s hK
        -- s conflicts with t means s.1 ≠ t.1 and |s.1 ∩ t.1| ≥ 2
        have hcard2 : 2 ≤ (t.1 ∩ s.1).card := hK.2
        rcases Finset.one_lt_card.mp hcard2 with ⟨a, ha, b, hb, hab⟩
        have ha_t := Finset.mem_inter.mp ha |>.1
        have ha_s := Finset.mem_inter.mp ha |>.2
        have hb_t := Finset.mem_inter.mp hb |>.1
        have hb_s := Finset.mem_inter.mp hb |>.2
        -- {a, b} is an edge of both s and t
        have hab_in_s : ({a, b} : Finset V) ⊆ s.1 := by
          intro x hx; simp at hx; rcases hx with rfl | rfl <;> [exact ha_s; exact hb_s]
        have hab_in_t : ({a, b} : Finset V) ⊆ t.1 := by
          intro x hx; simp at hx; rcases hx with rfl | rfl <;> [exact ha_t; exact hb_t]
        -- X s contributes to the load at {a, b}
        have ht_ab' : ({a, b} : Finset V) ⊆ t.1 := by
          intro x hx; simp at hx; rcases hx with rfl | rfl <;> [exact ha_t; exact hb_t]
        have ht_in_sum : X t ≤ ∑ r : (triCS G).O, (if {a, b} ⊆ r.1 then X r else 0) := by
          have h := Finset.single_le_sum (fun r _ => Nat.zero_le (if {a, b} ⊆ r.1 then X r else 0)) (Finset.mem_univ t)
          simp [ht_ab'] at h
          exact h
        have hs_ab : X s ≤ ∑ r : (triCS G).O, (if {a, b} ⊆ r.1 then X r else 0) := by
          have h := Finset.single_le_sum (fun r _ => Nat.zero_le (if {a, b} ⊆ r.1 then X r else 0)) (Finset.mem_univ s)
          simp [hab_in_s] at h
          exact h
        have hload_ab' := hload {a, b} (by rw [Finset.card_pair hab])
        have hsum_eq : ∑ r : (triCS G).O, (if {a, b} ⊆ r.1 then X r else 0) = 2 := by omega
        -- Since X t = 2 and the sum is exactly 2, X s must be 0
        -- (triCS G).K t s implies t.1 ≠ s.1, which means t ≠ s
        have ht_ne_s : t ≠ s := ne_of_apply_ne Subtype.val hK.1
        -- Decompose the sum: sum = term(t) + sum(r ≠ t)
        have hsum_decomp : ∑ r : (triCS G).O, (if {a, b} ⊆ r.1 then X r else 0) =
            (if {a, b} ⊆ t.1 then X t else 0) + ∑ r ∈ Finset.univ.erase t, (if {a, b} ⊆ r.1 then X r else 0) := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
        simp only [if_pos ht_ab'] at hsum_decomp
        rw [hxteq', hsum_eq] at hsum_decomp
        -- Now hsum_decomp : 2 = 2 + sum(r ≠ t), so sum(r ≠ t) = 0
        have hsum_rest : ∑ r ∈ Finset.univ.erase t, (if {a, b} ⊆ r.1 then X r else 0) = 0 :=
          Nat.add_left_cancel hsum_decomp.symm
        -- s ≠ t, so s ∈ Finset.univ.erase t
        have hs_erase : s ∈ Finset.univ.erase t := Finset.mem_erase.mpr ⟨ht_ne_s.symm, Finset.mem_univ s⟩
        -- The term for s is in the rest sum, which is 0
        have hs_term : (if {a, b} ⊆ s.1 then X s else 0) ≤ 0 := by
          have := Finset.single_le_sum (fun r _ => Nat.zero_le (if {a, b} ⊆ r.1 then X r else 0)) hs_erase
          linarith
        have hs_sub : {a, b} ⊆ s.1 := hab_in_s
        have hif : (if {a, b} ⊆ s.1 then X s else 0) = X s := if_pos hs_sub
        rw [hif] at hs_term
        omega
      -- All conflicting triangles have X s = 0, so the only neighbors are twins
      -- Degree ≤ X t - 1 = 1 ≤ 3
      have hdeg_le : (Hgraph (triCS G) X).degree ⟨t, i⟩ ≤ X t - 1 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        -- The neighborFinset is contained in twins
        have hsub : (Hgraph (triCS G) X).neighborFinset ⟨t, i⟩ ⊆
            Finset.image (fun j : Fin (X t) => ⟨t, j⟩) (Finset.univ.erase i) := by
          intro ⟨s, j⟩ hj
          rw [SimpleGraph.mem_neighborFinset] at hj
          have ⟨hne, hadj⟩ := hj
          rcases hadj with ⟨rfl, hne⟩ | hKs
          · -- Twins: s = t
            rw [Finset.mem_image]
            have hij : j ≠ i := fun h => hne (by simp [h])
            exact ⟨j, Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩, rfl⟩
          · -- Conflicts: K t s, so X s = 0
            have hs_zero : X s = 0 := hnoX s hKs
            have : ¬(0 < X s) := by simp [hs_zero]
            exact False.elim (this (Nat.zero_lt_of_lt j.2))
        have hcard_le : ((Hgraph (triCS G) X).neighborFinset ⟨t, i⟩).card ≤
            (Finset.image (fun j : Fin (X t) => (⟨t, j⟩ : Copies (triCS G) X)) (Finset.univ.erase i)).card :=
          Finset.card_le_card hsub
        have himage_card : (Finset.image (fun j : Fin (X t) => (⟨t, j⟩ : Copies (triCS G) X)) (Finset.univ.erase i)).card ≤ X t - 1 := by
          calc (Finset.image (fun j : Fin (X t) => (⟨t, j⟩ : Copies (triCS G) X)) (Finset.univ.erase i)).card
              ≤ (Finset.univ.erase i).card := Finset.card_image_le
            _ = X t - 1 := by simp
        linarith
      have heq : (Hgraph (triCS G) X).degree ⟨t, i⟩ = ((Hgraph (triCS G) X).neighborFinset ⟨t, i⟩).card :=
        SimpleGraph.card_neighborFinset_eq_degree _ _
      omega
  have hsup : (Finset.image (fun v => (Hgraph (triCS G) X).degree v) Finset.univ).max ≤ (3 : WithBot ℕ) := by
    apply Finset.sup_le
    intro v hv
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨c, rfl⟩ := hv
    exact WithBot.coe_le_coe.mpr (hle c)
  by_cases h : (Finset.univ.image (fun v => (Hgraph (triCS G) X).degree v)).max = ⊥
  · simp [h]
  · rcases m : (Finset.univ.image (fun v => (Hgraph (triCS G) X).degree v)).max with _ | n
    · contradiction
    · simp only [m] at hsup ⊢
      exact WithBot.coe_le_coe.mp hsup


end PaperV
