/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV/V — §4.1 copy inequalities, N1 part (b): `H[T₂]` is `K₄`-free (`copy_integral_cliqueFree_four`, the
book/tetrahedron analysis) and the structural Theorem 4.2 (`copy_integral_struct`). Split of the former
`Copy.lean` (2026-09-14); statements unchanged. This is the heavy module (large heartbeat budgets).

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.CopyN1Degree

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set
import Mathlib.Tactic.Tauto

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Sourcing lemma.** Two triangles from the SAME feasible packing whose images share an edge
must share it through the copy target `z` (else the preimages would share that edge, contradicting
edge-disjoint feasibility). Hence the target `z` lies in the image. -/
lemma copy_share_target
    (G : SimpleGraph V) [DecidableRel G.Adj] (w z : V)
    (P : Finset (triCS (copyGraph G w z)).O)
    (hP : CSFeasible (triCS (copyGraph G w z)) P)
    (s s' : (triCS (copyGraph G w z)).O) (hs : s ∈ P) (hs' : s' ∈ P)
    (hne : s.1 ≠ s'.1)
    (hshare : 2 ≤ (copyMap w z s.1 ∩ copyMap w z s'.1).card) :
    z ∈ copyMap w z s.1 := by
  by_contra hz
  apply hP hs hs'
  refine ⟨hne, ?_⟩
  have hsub : (copyMap w z s.1 ∩ copyMap w z s'.1) ⊆ s.1 ∩ s'.1 := by
    intro y hy
    rw [Finset.mem_inter] at hy
    obtain ⟨hyi, hyi'⟩ := hy
    have hyz : y ≠ z := fun h => hz (h ▸ hyi)
    rw [mem_copyMap] at hyi hyi'
    rw [Finset.mem_inter]
    refine ⟨?_, ?_⟩
    · rcases hyi with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · exact absurd h2 hyz
    · rcases hyi' with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · exact absurd h2 hyz
  exact le_trans hshare (Finset.card_le_card hsub)

/-- Two distinct copies of the same object force multiplicity ≥ 2 (avoids the sigma-`Fintype`
instance clash by destructuring the copy and using `Subsingleton (Fin 1)`). -/
lemma two_le_of_two_copies {C : ConflictSystem} {X : C.O → ℕ}
    (a b : Copies C X) (hab : a ≠ b) (hobj : a.1 = b.1) : 2 ≤ X a.1 := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only at hobj
  subst hobj
  show 2 ≤ X a1
  by_contra h
  push_neg at h
  have hpos : 0 < X a1 := lt_of_le_of_lt (Nat.zero_le _) a2.isLt
  have h1 : X a1 = 1 := by omega
  have : Subsingleton (Fin (X a1)) := by rw [h1]; infer_instance
  exact hab (by rw [Subsingleton.elim a2 b2])

/-- Three distinct copies of the same object force multiplicity ≥ 3. -/
lemma three_le_of_three_copies {C : ConflictSystem} {X : C.O → ℕ}
    (a b c : Copies C X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hb : b.1 = a.1) (hc : c.1 = a.1) : 3 ≤ X a.1 := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨c1, c2⟩ := c
  simp only at hb hc
  subst b1; subst c1
  show 3 ≤ X a1
  by_contra h
  push_neg at h
  have hab' : a2.val ≠ b2.val := fun heq => hab (by rw [Fin.ext heq])
  have hac' : a2.val ≠ c2.val := fun heq => hac (by rw [Fin.ext heq])
  have hbc' : b2.val ≠ c2.val := fun heq => hbc (by rw [Fin.ext heq])
  have := a2.isLt; have := b2.isLt; have := c2.isLt
  omega

/-- Edge-load lower bound: two distinct triangles sharing an edge `e` contribute their full
multiplicities to `edgeLoad e`. -/
lemma edgeLoad_ge_of_two
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : (triCS G).O → ℕ)
    (t₁ t₂ : (triCS G).O) (h12 : t₁ ≠ t₂) (e : Finset V)
    (he1 : e ⊆ t₁.1) (he2 : e ⊆ t₂.1) :
    X t₁ + X t₂ ≤ ∑ t : (triCS G).O, if e ⊆ t.1 then X t else 0 := by
  calc X t₁ + X t₂
      = ∑ t ∈ ({t₁, t₂} : Finset (triCS G).O), (if e ⊆ t.1 then X t else 0) := by
        rw [Finset.sum_pair h12]; simp [he1, he2]
    _ ≤ ∑ t : (triCS G).O, if e ⊆ t.1 then X t else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)

set_option maxHeartbeats 1000000 in
lemma four_triangles_book_or_tetrahedron
    (S : Finset (Finset V))
    (hcard : S.card = 4)
    (htri : ∀ t ∈ S, t.card = 3)
    (hpair : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 2 ≤ (a ∩ b).card) :
    (∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ S, e ⊆ t) ∨
      (∃ U : Finset V, U.card = 4 ∧ S = U.powersetCard 3) := by
  classical
  -- First, check if there's a common 2-element edge across all triangles
  by_cases hcommon : ∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ S, e ⊆ t
  · exact Or.inl hcommon
  · right
    -- Let U be the biUnion of all triangles in S
    let U := S.biUnion id
    use U
    -- First show S ⊆ U.powersetCard 3
    have hS_sub : S ⊆ U.powersetCard 3 := by
      intro t ht
      simp [Finset.mem_powersetCard]
      exact ⟨Finset.subset_biUnion_of_mem id ht, htri t ht⟩
    -- So S.card ≤ (U.powersetCard 3).card = C(U.card, 3)
    have hcard_U_ge : U.card ≥ 4 := by
      have h := Finset.card_le_card hS_sub
      rw [hcard, Finset.card_powersetCard] at h
      by_contra hlt
      push_neg at hlt
      interval_cases U.card <;> simp_all [Nat.choose]
    -- Now show U.card ≤ 4
    have hcard_U_le : U.card ≤ 4 := by
      -- Get two distinct triangles t₁, t₂ from S
      have hS_nontrivial : 1 < S.card := by omega
      rw [Finset.one_lt_card] at hS_nontrivial
      obtain ⟨t₁, ht₁, t₂, ht₂, hne⟩ := hS_nontrivial
      -- t₁ ∪ t₂ has at most 4 elements
      have hunion_le : (t₁ ∪ t₂).card ≤ 4 := by
        have h_inter : 2 ≤ (t₁ ∩ t₂).card := hpair t₁ ht₁ t₂ ht₂ hne
        have hcard_t1 : t₁.card = 3 := htri t₁ ht₁
        have hcard_t2 : t₂.card = 3 := htri t₂ ht₂
        have := Finset.card_union_add_card_inter t₁ t₂
        omega
      -- All elements of U are in t₁ ∪ t₂
      have hU_sub : U ⊆ t₁ ∪ t₂ := by
        -- First, show that any triangle t ∈ S is contained in t₁ ∪ t₂
        have ht_sub : ∀ t ∈ S, t ⊆ t₁ ∪ t₂ := by
          intro t ht
          by_cases h1 : t = t₁
          · simp [h1]
          · by_cases h2 : t = t₂
            · simp [h2]
            · have h2_1 : 2 ≤ (t ∩ t₁).card := hpair t ht t₁ ht₁ h1
              have h2_2 : 2 ≤ (t ∩ t₂).card := hpair t ht t₂ ht₂ h2
              have hcard_t : t.card = 3 := htri t ht
              -- |t ∩ t₁| ≥ 2 and |t ∩ t₂| ≥ 2, with t having only 3 elements
              -- By incl-excl on t ∩ t₁ and t ∩ t₂:
              -- |t ∩ t₁| + |t ∩ t₂| = |(t ∩ t₁) ∪ (t ∩ t₂)| + |(t ∩ t₁) ∩ (t ∩ t₂)|
              --                   = |t ∩ (t₁ ∪ t₂)| + |t ∩ t₁ ∩ t₂|
              -- So 4 ≤ |t ∩ (t₁ ∪ t₂)| + |t ∩ t₁ ∩ t₂|
              -- Since |t| = 3, we have |t ∩ (t₁ ∪ t₂)| ≤ 3
              -- And |t ∩ t₁ ∩ t₂| = |(t ∩ t₁) ∩ (t ∩ t₂)| ≥ |t ∩ t₁| + |t ∩ t₂| - |t| ≥ 2 + 2 - 3 = 1
              -- So |t ∩ (t₁ ∪ t₂)| ≥ 4 - |t ∩ t₁ ∩ t₂|
              -- If |t ∩ t₁ ∩ t₂| = 1, then |t ∩ (t₁ ∪ t₂)| ≥ 3, meaning t ⊆ t₁ ∪ t₂
              -- If |t ∩ t₁ ∩ t₂| ≥ 2, then |t ∩ (t₁ ∪ t₂)| ≥ 2... need more careful analysis
              have hincl_excl : (t ∩ t₁).card + (t ∩ t₂).card = (t ∩ (t₁ ∪ t₂)).card + (t ∩ t₁ ∩ t₂).card := by
                rw [← Finset.card_union_add_card_inter]
                congr 1
                · rw [Finset.inter_union_distrib_left]
                · congr 1; ext x; simp [Finset.inter_assoc]; tauto
              have hsum : (t ∩ t₁).card + (t ∩ t₂).card ≥ 4 := by omega
              have hsum' : (t ∩ (t₁ ∪ t₂)).card + (t ∩ t₁ ∩ t₂).card ≥ 4 := hincl_excl ▸ hsum
              have hcard_union_le : (t ∩ (t₁ ∪ t₂)).card ≤ 3 := by
                exact le_trans (Finset.card_le_card (Finset.inter_subset_left)) (hcard_t.le)
              have hinter_le : (t ∩ t₁).card ≤ (t ∩ (t₁ ∪ t₂)).card := by
                apply Finset.card_le_card
                simp_all [Finset.subset_iff]
              have h2_le_d : 2 ≤ (t ∩ (t₁ ∪ t₂)).card := by linarith
              have hcard_inter : (t ∩ t₁ ∩ t₂).card ≥ 1 := by omega
              -- Either d = 3 and t ⊆ t₁ ∪ t₂, or d = 2 and t ∩ t₁ = t ∩ t₂ is a common edge
              by_cases hd : (t ∩ (t₁ ∪ t₂)).card = 3
              · have : t ∩ (t₁ ∪ t₂) = t := by
                  apply Finset.eq_of_subset_of_card_le (Finset.inter_subset_left)
                  linarith [hcard_t]
                exact this ▸ Finset.inter_subset_right
              · -- d ≤ 2 case: t ∩ t₁ and t ∩ t₂ are both 2-element subsets of t ∩ (t₁ ∪ t₂)
                have hd_eq_2 : (t ∩ (t₁ ∪ t₂)).card = 2 := by omega
                have h_eq_t1 : (t ∩ t₁).card = 2 := by linarith
                have h2_le_d : (t ∩ t₂).card ≤ (t ∩ (t₁ ∪ t₂)).card := by
                  apply Finset.card_le_card; simp [Finset.subset_iff]; intros; tauto
                have h_eq_t2 : (t ∩ t₂).card = 2 := by linarith
                -- t ∩ t₁ ⊆ t ∩ (t₁ ∪ t₂) and both have size 2, so t ∩ t₁ = t ∩ (t₁ ∪ t₂)
                have ht1_subset : t ∩ t₁ ⊆ t ∩ (t₁ ∪ t₂) := by
                  simp [Finset.subset_iff]; intros; tauto
                have ht1_eq : t ∩ t₁ = t ∩ (t₁ ∪ t₂) := Finset.eq_of_subset_of_card_le ht1_subset (by linarith)
                have ht2_subset : t ∩ t₂ ⊆ t ∩ (t₁ ∪ t₂) := by
                  simp [Finset.subset_iff]; intros; tauto
                have ht2_eq : t ∩ t₂ = t ∩ (t₁ ∪ t₂) := Finset.eq_of_subset_of_card_le ht2_subset (by linarith)
                -- So t ∩ t₁ = t ∩ t₂, meaning this 2-element set is in t₁ ∩ t₂
                have h_inter_eq : t ∩ t₁ = t ∩ t₂ := by rw [ht1_eq, ht2_eq]
                -- This 2-element set is contained in t₁ ∩ t₂
                have h_edge_in_inter : (t ∩ t₁) ⊆ t₁ ∩ t₂ := by
                  intro x hx
                  obtain ⟨hx_t, hx_t1⟩ := Finset.mem_inter.mp hx
                  have hx_t2 : x ∈ t₂ := Finset.mem_inter.mp (h_inter_eq ▸ hx) |>.2
                  exact Finset.mem_inter.mpr ⟨hx_t1, hx_t2⟩
                -- t ∩ t₁ = t₁ ∩ t₂, so t₁ ∩ t₂ ⊆ t
                -- First compute |t₁ ∩ t₂| = 2
                have ht1t2_card : (t₁ ∩ t₂).card = 2 := by
                  have h := hpair t₁ ht₁ t₂ ht₂ hne
                  have h1 : t₁.card = 3 := htri t₁ ht₁
                  have h2 : t₂.card = 3 := htri t₂ ht₂
                  have hunion : (t₁ ∪ t₂).card ≤ 4 := hunion_le
                  have heq := Finset.card_union_add_card_inter t₁ t₂
                  have hinter_le_t1 : (t₁ ∩ t₂).card ≤ t₁.card := Finset.card_le_card Finset.inter_subset_left
                  have hinter_lt : (t₁ ∩ t₂).card < 3 := by
                    by_contra hc
                    push_neg at hc
                    have hc' : t₁.card ≤ (t₁ ∩ t₂).card := h1 ▸ hc
                    have h_eq : t₁ ∩ t₂ = t₁ := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hc'
                    have hsub : t₁ ⊆ t₂ := h_eq ▸ Finset.inter_subset_right
                    have : t₁ = t₂ := Finset.eq_of_subset_of_card_le hsub (le_of_eq h1.symm |> le_trans (le_of_eq h2))
                    exact hne this
                  omega
                have ht1t2_eq : t₁ ∩ t₂ = t ∩ t₁ := (Finset.eq_of_subset_of_card_le h_edge_in_inter (by linarith)).symm
                have ht_contains : t₁ ∩ t₂ ⊆ t := ht1t2_eq ▸ Finset.inter_subset_left
                -- By pigeonhole: at most 2 triangles can miss an element of t₁ ∩ t₂
                -- Since |S| = 4, at least one triangle contains all of t₁ ∩ t₂
                -- Actually, t₁, t₂, t all contain t₁ ∩ t₂. We need one more.
                -- Any s ∈ S with s ≠ t₁, t₂, t:
                --   If s ∩ t₁ = s ∩ t₂, then s contains t₁ ∩ t₂.
                --   If s ∩ t₁ ≠ s ∩ t₂, then |s ∩ t₁ ∩ t₂| ≥ 1, so s misses at most 1 element.
                -- Since |t₁ ∩ t₂| = 2, and at most 2 elements can be "missed" by triangles,
                -- and we have 4 triangles, at least one triangle contains both elements.
                -- Let's just show: there exists s ∈ S \ {t₁, t₂, t} with s ∩ t₁ = s ∩ t₂
                exfalso
                -- We'll show t₁ ∩ t₂ is a common edge, contradicting hcommon
                apply hcommon
                use t₁ ∩ t₂, ht1t2_card
                intro s hs
                -- We need t₁ ∩ t₂ ⊆ s
                by_cases hs_t : s = t
                · rw [hs_t]; exact ht_contains
                by_cases hs_t1 : s = t₁
                · rw [hs_t1]; exact Finset.inter_subset_left
                by_cases hs_t2 : s = t₂
                · rw [hs_t2]; exact Finset.inter_subset_right
                -- s is different from t, t₁, t₂
                -- Check if s ∩ t₁ = s ∩ t₂
                have h_st1_card : 2 ≤ (s ∩ t₁).card := by
                  by_cases heq : s = t₁
                  · simp [heq, htri t₁ ht₁]
                  · exact hpair s hs t₁ ht₁ heq
                have h_st2_card : 2 ≤ (s ∩ t₂).card := by
                  by_cases heq : s = t₂
                  · simp [heq, htri t₂ ht₂]
                  · exact hpair s hs t₂ ht₂ heq
                have h_st1t2_eq : s ∩ t₁ = s ∩ t₂ → t₁ ∩ t₂ ⊆ s := by
                  intro heq
                  have h_inter : s ∩ t₁ ⊆ t₁ ∩ t₂ := by
                    intro x hx
                    simp [Finset.mem_inter] at hx ⊢
                    have hx_st1 : x ∈ s ∩ t₁ := Finset.mem_inter.mpr hx
                    have hx_st2 := heq ▸ hx_st1
                    exact ⟨hx.2, Finset.mem_inter.mp hx_st2 |>.2⟩
                  exact (Finset.eq_of_subset_of_card_le h_inter (by rw [ht1t2_card]; linarith)).symm ▸ Finset.inter_subset_left
                by_cases hs_inter : s ∩ t₁ = s ∩ t₂
                · exact h_st1t2_eq hs_inter
                · -- s ∩ t₁ ≠ s ∩ t₂, but |s ∩ t₁| ≥ 2, |s ∩ t₂| ≥ 2, |s| = 3
                  -- s ∩ t₁ and s ∩ t₂ are different subsets of s (with 3 elements)
                  -- So |s ∩ t₁| = 2 and |s ∩ t₂| = 2 (can't be 3 since they're different and subsets of s)
                  have hs_card : s.card = 3 := htri s hs
                  have h_st1_le : (s ∩ t₁).card ≤ 3 := by
                    calc (s ∩ t₁).card ≤ s.card := Finset.card_le_card Finset.inter_subset_left
                      _ = 3 := hs_card
                  have h_st2_le : (s ∩ t₂).card ≤ 3 := by
                    calc (s ∩ t₂).card ≤ s.card := Finset.card_le_card Finset.inter_subset_left
                      _ = 3 := hs_card
                  have h_st1_eq_2 : (s ∩ t₁).card = 2 := by
                    have : (s ∩ t₁).card ≠ 3 := by
                      intro hc
                      have : s ∩ t₁ = t₁ := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by linarith [htri t₁ ht₁])
                      have : s ⊇ t₁ := by simp_all [Finset.inter_eq_right]
                      have hcard_s_t1 : s.card = t₁.card := by simp_all
                      have hsub : t₁ ⊆ s := this
                      have : t₁ = s := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_s_t1)
                      exact hs_t1 this.symm
                    omega
                  have h_st2_eq_2 : (s ∩ t₂).card = 2 := by
                    have : (s ∩ t₂).card ≠ 3 := by
                      intro hc
                      have : s ∩ t₂ = t₂ := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by linarith [htri t₂ ht₂])
                      have : s ⊇ t₂ := by simp_all [Finset.inter_eq_right]
                      have hcard_s_t2 : s.card = t₂.card := by simp_all
                      have hsub : t₂ ⊆ s := this
                      have : t₂ = s := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_s_t2)
                      exact hs_t2 this.symm
                    omega
                  -- s ∩ t₁ ⊆ t₁ and |s ∩ t₁| = 2, so s ∩ t₁ = t₁ \ {y₁} for some y₁
                  -- Similarly s ∩ t₂ = t₂ \ {y₂} for some y₂
                  -- Since s ∩ t₁ ≠ s ∩ t₂, we have y₁ ≠ y₂
                  -- Both y₁, y₂ ∈ t₁ ∩ t₂ (since s ∩ t₁ ⊆ t₁ and s ∩ t₁ ⊆ t₁ means the missed element is in t₁ \ s)
                  -- Actually y₁ = the element in t₁ \ s, and since |s ∩ t₁| = 2 and |t₁| = 3
                  -- y₁ ∈ t₁ and y₁ ∉ s. Similarly y₂ ∈ t₂ and y₂ ∉ s.
                  -- Since y₁ ∈ t₁ \ s and |t₁ \ s| = 1, y₁ is unique.
                  -- Key: y₁ ∈ t₁ and y₁ ∉ s. Since s ∩ t₁ ⊆ t₁ ∩ s, y₁ ∉ t₁ ∩ s.
                  -- Does y₁ ∈ t₂? We need y₁ ∈ t₁ ∩ t₂ for the contradiction.
                  -- Since |s ∩ t₁| = 2 and s ∩ t₁ ⊆ t₁, and t₁ ∩ t₂ ⊆ t₁ has 2 elements...
                  -- Actually, s ∩ t₁ is a 2-element subset of t₁. t₁ ∩ t₂ is also a 2-element subset.
                  -- They could be different.
                  -- The key constraint: t ∩ s has ≥ 2 elements (by hpair)
                  have h_ts_card : 2 ≤ (t ∩ s).card := hpair t ht s hs (by tauto)
                  -- t ∩ s ⊆ s and |s| = 3, so t ∩ s has 2 or 3 elements
                  -- By incl-excl on s ∩ t₁ and s ∩ t₂: |s ∩ t₁ ∩ t₂| ≥ 1
                  have h_sincincl : (s ∩ t₁).card + (s ∩ t₂).card = (s ∩ (t₁ ∪ t₂)).card + (s ∩ t₁ ∩ t₂).card := by
                    rw [← Finset.card_union_add_card_inter]
                    congr 1
                    · rw [Finset.inter_union_distrib_left]
                    · congr 1; ext x; simp [Finset.inter_assoc]; tauto
                  have h_sincincl_bound : (s ∩ (t₁ ∪ t₂)).card ≤ 3 := by
                    have := Finset.card_le_card (Finset.inter_subset_left : s ∩ (t₁ ∪ t₂) ⊆ s)
                    linarith [hs_card]
                  have h_sinter_t1t2_ge : 1 ≤ (s ∩ t₁ ∩ t₂).card := by omega
                  -- If |s ∩ t₁ ∩ t₂| = 2, then s ∩ t₁ ∩ t₂ = t₁ ∩ t₂, so t₁ ∩ t₂ ⊆ s ∩ t₁ and t₁ ∩ t₂ ⊆ s ∩ t₂
                  -- Since |s ∩ t₁| = 2, we'd have s ∩ t₁ = t₁ ∩ t₂ = s ∩ t₂, contradicting hs_inter
                  have h_sinter_t1t2_eq1 : (s ∩ t₁ ∩ t₂).card = 1 := by
                    by_contra hc
                    push_neg at hc
                    have hc2 : (s ∩ t₁ ∩ t₂).card = 2 := by
                      have h_le : (s ∩ t₁ ∩ t₂).card ≤ (s ∩ t₁).card := Finset.card_le_card (Finset.inter_subset_left)
                      omega
                    have hsub : s ∩ t₁ ∩ t₂ ⊆ t₁ ∩ t₂ := by
                      intro x hx; simp only [Finset.mem_inter] at hx ⊢; exact ⟨hx.1.2, hx.2⟩
                    have h_eq : s ∩ t₁ ∩ t₂ = t₁ ∩ t₂ := Finset.eq_of_subset_of_card_le hsub (by linarith [ht1t2_card])
                    have h_st1_eq : s ∩ t₁ = t₁ ∩ t₂ := by
                      have h1 : s ∩ t₁ ∩ t₂ = s ∩ t₁ := by
                        apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
                        linarith
                      rw [← h1, h_eq]
                    have h_st2_eq : s ∩ t₂ = t₁ ∩ t₂ := by
                      have hcomm : s ∩ t₂ ∩ t₁ = s ∩ t₁ ∩ t₂ := by ext; simp [Finset.mem_inter]; tauto
                      have hcard_s_t2_t1 : (s ∩ t₂ ∩ t₁).card = 2 := by rw [hcomm]; linarith
                      have h1 : s ∩ t₂ ∩ t₁ = s ∩ t₂ := by
                        apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
                        linarith
                      rw [← h1, hcomm, h_eq]
                    exact hs_inter (h_st1_eq.trans h_st2_eq.symm)
                  -- So |s ∩ (t₁ ∪ t₂)| = 3, meaning s ⊆ t₁ ∪ t₂
                  have hs_sub_union : s ⊆ t₁ ∪ t₂ := by
                    have hcard_eq : (s ∩ (t₁ ∪ t₂)).card = 3 := by linarith
                    have h_eq : s ∩ (t₁ ∪ t₂) = s := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by linarith [hs_card])
                    exact h_eq ▸ Finset.inter_subset_right
                  -- t ∩ (t₁ ∪ t₂) = t ∩ t₁ = t₁ ∩ t₂
                  have ht_inter_union_eq : t ∩ (t₁ ∪ t₂) = t₁ ∩ t₂ := ht1_eq.symm.trans ht1t2_eq.symm
                  -- t \ (t₁ ∪ t₂) has 1 element
                  have ht_diff_card : (t \ (t₁ ∪ t₂)).card = 1 := by
                    rw [Finset.card_sdiff]
                    have h_inter_eq : (t₁ ∪ t₂) ∩ t = t ∩ (t₁ ∪ t₂) := Finset.inter_comm _ _
                    rw [h_inter_eq, ht_inter_union_eq, ht1t2_card]
                    omega
                  -- t = (t ∩ (t₁ ∪ t₂)) ∪ (t \ (t₁ ∪ t₂))
                  have ht_decomp : t = (t ∩ (t₁ ∪ t₂)) ∪ (t \ (t₁ ∪ t₂)) := by ext x; simp; tauto
                  -- The element in t \ (t₁ ∪ t₂) is not in s (since s ⊆ t₁ ∪ t₂)
                  have h_ts_subset : t ∩ s ⊆ (t ∩ (t₁ ∪ t₂)) ∩ s := by
                    intro x hx; exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨Finset.mem_inter.mp hx |>.1, hs_sub_union (Finset.mem_inter.mp hx |>.2)⟩, Finset.mem_inter.mp hx |>.2⟩
                  have h_ts_eq : t ∩ s = (t₁ ∩ t₂) ∩ s := by
                    have : t ∩ s = (t ∩ (t₁ ∪ t₂)) ∩ s := by
                      ext x
                      simp only [Finset.mem_inter]
                      constructor <;> intro h <;> tauto
                    rw [this, ht_inter_union_eq]
                  -- So |t ∩ s| = |(t₁ ∩ t₂) ∩ s| = |s ∩ t₁ ∩ t₂| = 1
                  have h_ts_card_eq : (t ∩ s).card = 1 := by
                    rw [h_ts_eq]
                    have : (t₁ ∩ t₂) ∩ s = s ∩ t₁ ∩ t₂ := by ext; simp [Finset.inter_assoc]; tauto
                    rw [this, h_sinter_t1t2_eq1]
                  -- But h_ts_card says |t ∩ s| ≥ 2. Contradiction!
                  omega
        intro v hv
        simp [U, Finset.mem_biUnion] at hv
        obtain ⟨t, ht, hv_in_t⟩ := hv
        exact (ht_sub t ht) hv_in_t
      exact le_trans (Finset.card_le_card hU_sub) hunion_le
    have hcard_U : U.card = 4 := le_antisymm hcard_U_le hcard_U_ge
    have hcard_powerset : (U.powersetCard 3).card = 4 := by simp [hcard_U]
    exact ⟨hcard_U, Finset.eq_of_subset_of_card_le hS_sub (by linarith)⟩

set_option maxHeartbeats 1000000 in
lemma copy_tetra_avoids_centres_impossible
    (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V)
    (P' : Finset (triCS (copyGraph G v u)).O)
    (P'' : Finset (triCS (copyGraph G u v)).O)
    (hP' : CSFeasible (triCS (copyGraph G v u)) P')
    (hP'' : CSFeasible (triCS (copyGraph G u v)) P'')
    (U : Finset V) (hU : U.card = 4) (hu : u ∉ U) (hv : v ∉ U)
    (hfaces : ∀ t ∈ U.powersetCard 3, t ∈ G.cliqueFinset 3) :
    let T₂ : (triCS G).O → ℕ := fun t =>
      (P'.filter (fun s => copyMap v u s.1 = t.1)).card +
      (P''.filter (fun s => copyMap u v s.1 = t.1)).card
    ¬ (∀ t : (triCS G).O, t.1 ∈ U.powersetCard 3 → 0 < T₂ t) := by
  intro T₂ hall
  -- The 4 triangles of U form a clique in the conflict graph (any two share an edge)
  -- A feasible packing can contain at most 1 triangle from any clique
  -- So P' covers at most 1, P'' covers at most 1, but we need 4 covered
  have hcard3 : (U.powersetCard 3).card = 4 := by simp [hU]
  -- Any two distinct 3-subsets of U share exactly 2 elements
  have hconflict : ∀ t₁ t₂ : Finset V, t₁ ∈ U.powersetCard 3 → t₂ ∈ U.powersetCard 3 →
      t₁ ≠ t₂ → 2 ≤ (t₁ ∩ t₂).card := by
    intro t₁ t₂ ht₁ ht₂ hne
    have c₁ : t₁.card = 3 := Finset.mem_powersetCard.mp ht₁ |>.2
    have c₂ : t₂.card = 3 := Finset.mem_powersetCard.mp ht₂ |>.2
    have s₁ : t₁ ⊆ U := Finset.mem_powersetCard.mp ht₁ |>.1
    have s₂ : t₂ ⊆ U := Finset.mem_powersetCard.mp ht₂ |>.1
    have := Finset.card_inter_add_card_union t₁ t₂
    have union_sub : t₁ ∪ t₂ ⊆ U := Finset.union_subset s₁ s₂
    have union_card : (t₁ ∪ t₂).card ≤ 4 := Finset.card_le_card union_sub |> le_trans <| hU.le
    have inter_card : (t₁ ∩ t₂).card + (t₁ ∪ t₂).card = 6 := by omega
    omega
  -- Each packing contains at most 1 triangle from U.powersetCard 3
  have hP'_at_most_one : (P'.filter (fun t => t.1 ∈ U.powersetCard 3)).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    by_contra hne
    apply hP' ha.1 hb.1
    exact ⟨Subtype.val_injective.ne_iff.mpr hne, hconflict _ _ ha.2 hb.2 (Subtype.val_injective.ne_iff.mpr hne)⟩
  have hP''_at_most_one : (P''.filter (fun t => t.1 ∈ U.powersetCard 3)).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    by_contra hne
    apply hP'' ha.1 hb.1
    exact ⟨Subtype.val_injective.ne_iff.mpr hne, hconflict _ _ ha.2 hb.2 (Subtype.val_injective.ne_iff.mpr hne)⟩
  -- For t ⊆ U, copyMap v u s = t implies s = t (since u ∉ t means v ∉ s)
  have filter_P'_at_most_one : ∀ t : (triCS G).O, t.1 ∈ U.powersetCard 3 →
      (P'.filter (fun s => copyMap v u s.1 = t.1)).card ≤ 1 := by
    intro t ht
    apply Finset.card_le_one.mpr
    intro s₁ hs₁ s₂ hs₂
    simp only [Finset.mem_filter] at hs₁ hs₂
    have hU3 := Finset.mem_powersetCard.mp ht
    have hu_t : u ∉ t.1 := fun hu' => hu (hU3.1 hu')
    have hv_t : v ∉ t.1 := fun hv' => hv (hU3.1 hv')
    -- From copyMap v u s₁.1 = t.1 and u ∉ t.1, we get v ∉ s₁.1
    have hv_s₁ : v ∉ s₁.1 := by
      by_contra hv_s₁'
      have : u ∈ copyMap v u s₁.1 := by
        rw [copyMap]
        apply Finset.mem_image.mpr
        exact ⟨v, hv_s₁', by simp⟩
      rw [hs₁.2] at this
      exact hu_t this
    have hv_s₂ : v ∉ s₂.1 := by
      by_contra hv_s₂'
      have : u ∈ copyMap v u s₂.1 := by
        rw [copyMap]
        apply Finset.mem_image.mpr
        exact ⟨v, hv_s₂', by simp⟩
      rw [hs₂.2] at this
      exact hu_t this
    -- Since v ∉ s₁.1 and v ∉ s₂.1, copyMap v u = id on s₁.1 and s₂.1
    have inj_on : Set.InjOn (fun x => if x = v then u else x) (s₁.1 : Set V) := by
      intro x hx y hy hxy
      by_cases hxv : x = v
      · rw [hxv] at hx; exact absurd hx hv_s₁
      · by_cases hyv : y = v
        · rw [hyv] at hy; exact absurd hy hv_s₁
        · simp_all
    have hs₁_eq : copyMap v u s₁.1 = s₁.1 := by
      simp only [copyMap]
      apply Finset.eq_of_subset_of_card_le
      · rw [Finset.image_subset_iff]
        intro x hx
        by_cases hxv : x = v
        · rw [hxv] at hx; exact absurd hx hv_s₁
        · simp_all
      · rw [Finset.card_image_of_injOn inj_on]
    have hs₂_eq : copyMap v u s₂.1 = s₂.1 := by
      have inj_on₂ : Set.InjOn (fun x => if x = v then u else x) (s₂.1 : Set V) := by
        intro x hx y hy hxy
        by_cases hxv : x = v
        · rw [hxv] at hx; exact absurd hx hv_s₂
        · by_cases hyv : y = v
          · rw [hyv] at hy; exact absurd hy hv_s₂
          · simp_all
      simp only [copyMap]
      apply Finset.eq_of_subset_of_card_le
      · rw [Finset.image_subset_iff]
        intro x hx
        by_cases hxv : x = v
        · rw [hxv] at hx; exact absurd hx hv_s₂
        · simp_all
      · rw [Finset.card_image_of_injOn inj_on₂]
    rw [hs₁_eq] at hs₁
    rw [hs₂_eq] at hs₂
    exact Subtype.ext (hs₁.2.trans hs₂.2.symm)
  have filter_P''_at_most_one : ∀ t : (triCS G).O, t.1 ∈ U.powersetCard 3 →
      (P''.filter (fun s => copyMap u v s.1 = t.1)).card ≤ 1 := by
    intro t ht
    apply Finset.card_le_one.mpr
    intro s₁ hs₁ s₂ hs₂
    simp only [Finset.mem_filter] at hs₁ hs₂
    have hU3 := Finset.mem_powersetCard.mp ht
    have hu_t : u ∉ t.1 := fun hu' => hu (hU3.1 hu')
    have hv_t : v ∉ t.1 := fun hv' => hv (hU3.1 hv')
    -- From copyMap u v s₁.1 = t.1 and v ∉ t.1, we get u ∉ s₁.1
    have hu_s₁ : u ∉ s₁.1 := by
      by_contra hu_s₁'
      have : v ∈ copyMap u v s₁.1 := by
        rw [copyMap]
        apply Finset.mem_image.mpr
        exact ⟨u, hu_s₁', by simp⟩
      rw [hs₁.2] at this
      exact hv_t this
    have hu_s₂ : u ∉ s₂.1 := by
      by_contra hu_s₂'
      have : v ∈ copyMap u v s₂.1 := by
        rw [copyMap]
        apply Finset.mem_image.mpr
        exact ⟨u, hu_s₂', by simp⟩
      rw [hs₂.2] at this
      exact hv_t this
    -- Since u ∉ s₁.1 and u ∉ s₂.1, copyMap u v = id on s₁.1 and s₂.1
    have inj_on : Set.InjOn (fun x => if x = u then v else x) (s₁.1 : Set V) := by
      intro x hx y hy hxy
      by_cases hxu : x = u
      · rw [hxu] at hx; exact absurd hx hu_s₁
      · by_cases hyu : y = u
        · rw [hyu] at hy; exact absurd hy hu_s₁
        · simp_all
    have hs₁_eq : copyMap u v s₁.1 = s₁.1 := by
      simp only [copyMap]
      apply Finset.eq_of_subset_of_card_le
      · rw [Finset.image_subset_iff]
        intro x hx
        by_cases hxu : x = u
        · rw [hxu] at hx; exact absurd hx hu_s₁
        · simp_all
      · rw [Finset.card_image_of_injOn inj_on]
    have inj_on₂ : Set.InjOn (fun x => if x = u then v else x) (s₂.1 : Set V) := by
      intro x hx y hy hxy
      by_cases hxu : x = u
      · rw [hxu] at hx; exact absurd hx hu_s₂
      · by_cases hyu : y = u
        · rw [hyu] at hy; exact absurd hy hu_s₂
        · simp_all
    have hs₂_eq : copyMap u v s₂.1 = s₂.1 := by
      simp only [copyMap]
      apply Finset.eq_of_subset_of_card_le
      · rw [Finset.image_subset_iff]
        intro x hx
        by_cases hxu : x = u
        · rw [hxu] at hx; exact absurd hx hu_s₂
        · simp_all
      · rw [Finset.card_image_of_injOn inj_on₂]
    rw [hs₁_eq] at hs₁
    rw [hs₂_eq] at hs₂
    exact Subtype.ext (hs₁.2.trans hs₂.2.symm)
  -- The total load across all 4 triangles is at most 2
  -- So at least one triangle has load 0
  -- Count: sum of h t over all t in U.powersetCard 3
  -- Each h t = #(filter P') + #(filter P'')
  -- Sum = #{s ∈ P' with copyMap v u s ∈ U.powersetCard 3} + #{s ∈ P'' with copyMap u v s ∈ U.powersetCard 3}
  -- Each term ≤ 1, so sum ≤ 2
  -- But hall says each h t ≥ 1, so sum ≥ 4. Contradiction.
  
  -- For t ⊆ U, copyMap v u s = t implies s = t (since u,v ∉ t implies v ∉ s)
  have key : ∀ t : (triCS G).O, t.1 ∈ U.powersetCard 3 →
      ∀ s : (triCS (copyGraph G v u)).O, copyMap v u s.1 = t.1 → s.1 = t.1 := by
    intro t ht s hst
    have hU3 := Finset.mem_powersetCard.mp ht
    have hu_t : u ∉ t.1 := fun hu' => hu (hU3.1 hu')
    have hv_t : v ∉ t.1 := fun hv' => hv (hU3.1 hv')
    -- v ∉ s.1 (otherwise u ∈ copyMap v u s.1 = t.1)
    have hv_s : v ∉ s.1 := by
      by_contra hv_s'
      have : u ∈ copyMap v u s.1 := by
        simp only [copyMap]
        exact Finset.mem_image.mpr ⟨v, hv_s', by simp⟩
      exact hu_t (hst ▸ this)
    -- copyMap v u = id on s.1
    have heq : copyMap v u s.1 = s.1 := by
      simp only [copyMap]
      apply Finset.eq_of_subset_of_card_le
      · rw [Finset.image_subset_iff]
        intro x hx
        by_cases hxv : x = v
        · rw [hxv] at hx; exact absurd hx hv_s
        · simp_all
      · rw [Finset.card_image_of_injOn]
        intro x hx y hy hxy
        by_cases hxv : x = v
        · rw [hxv] at hx; exact absurd hx hv_s
        · by_cases hyv : y = v
          · rw [hyv] at hy; exact absurd hy hv_s
          · simpa [hxv, hyv] using hxy
    exact heq.symm.trans hst
  
  have key' : ∀ t : (triCS G).O, t.1 ∈ U.powersetCard 3 →
      ∀ s : (triCS (copyGraph G u v)).O, copyMap u v s.1 = t.1 → s.1 = t.1 := by
    intro t ht s hst
    have hU3 := Finset.mem_powersetCard.mp ht
    have hu_t : u ∉ t.1 := fun hu' => hu (hU3.1 hu')
    have hv_t : v ∉ t.1 := fun hv' => hv (hU3.1 hv')
    have hu_s : u ∉ s.1 := by
      by_contra hu_s'
      have : v ∈ copyMap u v s.1 := by
        simp only [copyMap]
        exact Finset.mem_image.mpr ⟨u, hu_s', by simp⟩
      exact hv_t (hst ▸ this)
    have heq : copyMap u v s.1 = s.1 := by
      simp only [copyMap]
      apply Finset.eq_of_subset_of_card_le
      · rw [Finset.image_subset_iff]
        intro x hx
        by_cases hxu : x = u
        · rw [hxu] at hx; exact absurd hx hu_s
        · simp_all
      · rw [Finset.card_image_of_injOn]
        intro x hx y hy hxy
        by_cases hxu : x = u
        · rw [hxu] at hx; exact absurd hx hu_s
        · by_cases hyu : y = u
          · rw [hyu] at hy; exact absurd hy hu_s
          · simpa [hxu, hyu] using hxy
    exact heq.symm.trans hst
  
  -- Now derive contradiction: sum of h t ≤ 2 but ≥ 4
  -- Sum_{t ∈ U.powersetCard 3} h t = #{s ∈ P' with copyMap v u s ∈ U} + #{s ∈ P'' with copyMap u v s ∈ U}
  -- Each term ≤ 1, so sum ≤ 2
  -- Define T = the set of (triCS G).O elements with .1 ∈ U.powersetCard 3
  let T : Finset (triCS G).O := (Finset.powersetCard 3 U).attach.image (fun ⟨t, ht⟩ => ⟨t, hfaces t ht⟩)
  have hT_card : T.card = 4 := by
    rw [← hcard3]
    rw [Finset.card_image_of_injOn]
    · rw [Finset.card_attach]
    · intro x hx y hy hxy
      have hx' : (x : Finset V) ∈ Finset.powersetCard 3 U := x.2
      have hy' : (y : Finset V) ∈ Finset.powersetCard 3 U := y.2
      simp only [Finset.mem_coe] at hx hy
      injection hxy with h
      exact Subtype.ext h
  have sum_bound : T.sum (fun t => T₂ t) ≤ 2 := by
    -- Rewrite sum as sum of filters
    have hsum_eq : T.sum (fun t => T₂ t) =
        T.sum (fun t => (P'.filter (fun s => copyMap v u s.1 = t.1)).card) +
        T.sum (fun t => (P''.filter (fun s => copyMap u v s.1 = t.1)).card) := by
      simp only [T₂]
      rw [Finset.sum_add_distrib]
    rw [hsum_eq]
    -- Each sum counts elements of P' or P'' with copyMap image in U
    -- By `key` and `key'`, this equals #{s ∈ P' : s.1 ∈ U.powersetCard 3} ≤ 1
    have sum_P' : T.sum (fun t => (P'.filter (fun s => copyMap v u s.1 = t.1)).card) ≤ 1 := by
      have hle : T.sum (fun t => (P'.filter (fun s => copyMap v u s.1 = t.1)).card) =
          (P'.filter (fun s => s.1 ∈ U.powersetCard 3)).card := by
        conv_lhs =>
          arg 2
          ext t
          rw [Finset.card_eq_sum_ones]
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
        conv_rhs =>
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro s _
        by_cases hsU : s.1 ∈ U.powersetCard 3
        · simp only [hsU, ↓reduceIte]
          have hsT : ⟨s.1, hfaces s.1 hsU⟩ ∈ T := Finset.mem_image.mpr ⟨⟨s.1, hsU⟩, Finset.mem_attach _ _, by rfl⟩
          rw [show (∑ x ∈ T, if copyMap v u s.1 = x.1 then 1 else 0) =
              (T.filter (fun t => copyMap v u s.1 = t.1)).card by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]]
          rw [Finset.card_eq_one]
          use ⟨s.1, hfaces s.1 hsU⟩
          ext t
          simp only [Finset.mem_filter]
          constructor
          · intro ⟨hmem, heq⟩
            rw [Finset.mem_image] at hmem
            obtain ⟨t', _, htu⟩ := hmem
            simp only at htu
            have htu' : t = ⟨t'.val, hfaces t'.val t'.property⟩ := htu.symm
            have ht1 : t.1 = t'.val := congrArg Subtype.val htu'
            have heq' : t.1 = s.1 := by
              have heq'' : copyMap v u s.1 = t'.val := ht1 ▸ heq
              exact ht1.trans (key ⟨t'.val, hfaces t'.val t'.property⟩ t'.property s heq'').symm
            rw [htu']
            rw [Finset.mem_singleton]
            exact Subtype.ext (ht1.symm.trans heq')
          · intro h
            rw [Finset.mem_singleton] at h
            refine ⟨h ▸ hsT, ?_⟩
            rw [h]
            have hU3 := Finset.mem_powersetCard.mp hsU
            have hu_t : u ∉ s.1 := fun hu' => hu (hU3.1 hu')
            have hv_t : v ∉ s.1 := fun hv' => hv (hU3.1 hv')
            simp only [copyMap]
            apply Finset.eq_of_subset_of_card_le
            · rw [Finset.image_subset_iff]
              intro x hx
              by_cases hxv : x = v
              · rw [hxv] at hx; exact absurd hx hv_t
              · simp_all
            · rw [Finset.card_image_of_injOn]
              intro x hx y hy hxy
              by_cases hxv : x = v
              · rw [hxv] at hx; exact absurd hx hv_t
              · by_cases hyv : y = v
                · rw [hyv] at hy; exact absurd hy hv_t
                · simpa [hxv, hyv] using hxy
        · simp only [hsU, ↓reduceIte]
          rw [Finset.sum_eq_zero]
          intro t ht
          by_contra heq
          have hcopy : copyMap v u s.1 = t.1 := by simpa using heq
          have : s.1 ∈ U.powersetCard 3 := by
            have ht_mem : t.1 ∈ U.powersetCard 3 := by
              rw [Finset.mem_image] at ht
              obtain ⟨t', _, htu⟩ := ht
              simp only at htu
              have : t = ⟨t'.val, hfaces t'.val t'.property⟩ := htu.symm
              simp [this]
            have hs_eq_t : s.1 = t.1 := key t ht_mem s hcopy
            rw [hs_eq_t]
            exact ht_mem
          exact hsU this
      rw [hle]
      exact hP'_at_most_one
    have sum_P'' : T.sum (fun t => (P''.filter (fun s => copyMap u v s.1 = t.1)).card) ≤ 1 := by
      have hle : T.sum (fun t => (P''.filter (fun s => copyMap u v s.1 = t.1)).card) =
          (P''.filter (fun s => s.1 ∈ U.powersetCard 3)).card := by
        conv_lhs =>
          arg 2
          ext t
          rw [Finset.card_eq_sum_ones]
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
        conv_rhs =>
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro s _
        by_cases hsU : s.1 ∈ U.powersetCard 3
        · simp only [hsU, ↓reduceIte]
          have hsT : ⟨s.1, hfaces s.1 hsU⟩ ∈ T := Finset.mem_image.mpr ⟨⟨s.1, hsU⟩, Finset.mem_attach _ _, by rfl⟩
          rw [show (∑ x ∈ T, if copyMap u v s.1 = x.1 then 1 else 0) =
              (T.filter (fun t => copyMap u v s.1 = t.1)).card by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]]
          rw [Finset.card_eq_one]
          use ⟨s.1, hfaces s.1 hsU⟩
          ext t
          simp only [Finset.mem_filter]
          constructor
          · intro ⟨hmem, heq⟩
            rw [Finset.mem_image] at hmem
            obtain ⟨t', _, htu⟩ := hmem
            simp only at htu
            have htu' : t = ⟨t'.val, hfaces t'.val t'.property⟩ := htu.symm
            have ht1 : t.1 = t'.val := congrArg Subtype.val htu'
            have heq' : t.1 = s.1 := by
              have heq'' : copyMap u v s.1 = t'.val := ht1 ▸ heq
              exact ht1.trans (key' ⟨t'.val, hfaces t'.val t'.property⟩ t'.property s heq'').symm
            rw [htu']
            rw [Finset.mem_singleton]
            exact Subtype.ext (ht1.symm.trans heq')
          · intro h
            rw [Finset.mem_singleton] at h
            refine ⟨h ▸ hsT, ?_⟩
            rw [h]
            have hU3 := Finset.mem_powersetCard.mp hsU
            have hu_t : u ∉ s.1 := fun hu' => hu (hU3.1 hu')
            have hv_t : v ∉ s.1 := fun hv' => hv (hU3.1 hv')
            simp only [copyMap]
            apply Finset.eq_of_subset_of_card_le
            · rw [Finset.image_subset_iff]
              intro x hx
              by_cases hxu : x = u
              · rw [hxu] at hx; exact absurd hx hu_t
              · simp_all
            · rw [Finset.card_image_of_injOn]
              intro x hx y hy hxy
              by_cases hxu : x = u
              · rw [hxu] at hx; exact absurd hx hu_t
              · by_cases hyu : y = u
                · rw [hyu] at hy; exact absurd hy hu_t
                · simpa [hxu, hyu] using hxy
        · simp only [hsU, ↓reduceIte]
          rw [Finset.sum_eq_zero]
          intro t ht
          by_contra heq
          have hcopy : copyMap u v s.1 = t.1 := by simpa using heq
          have : s.1 ∈ U.powersetCard 3 := by
            have ht_mem : t.1 ∈ U.powersetCard 3 := by
              rw [Finset.mem_image] at ht
              obtain ⟨t', _, htu⟩ := ht
              simp only at htu
              have : t = ⟨t'.val, hfaces t'.val t'.property⟩ := htu.symm
              simp [this]
            have hs_eq_t : s.1 = t.1 := key' t ht_mem s hcopy
            rw [hs_eq_t]
            exact ht_mem
          exact hsU this
      rw [hle]
      exact hP''_at_most_one
    linarith [sum_P', sum_P'']
  -- But h t ≥ 1 for all t ∈ T, so sum ≥ T.card = 4
  have hall_sum : T.sum (fun t => T₂ t) ≥ 4 := by
    have h_each : ∀ t ∈ T, 1 ≤ T₂ t := by
      intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨⟨t', ht'⟩, h_eq⟩ := ht
      have ht'_U : t' ∈ U.powersetCard 3 := ht'
      have h_eq' := h_eq.2
      simp only at h_eq'
      have heq'' : (⟨t', hfaces t' ht'_U⟩ : (triCS G).O) = t := h_eq'
      have : T₂ ⟨t', hfaces t' ht'_U⟩ ≥ 1 := by
        have := hall ⟨t', hfaces t' ht'_U⟩ ht'_U
        omega
      rw [heq''.symm]; exact this
    calc T.sum (fun t => T₂ t) ≥ T.sum (fun _ => 1) := Finset.sum_le_sum h_each
      _ = T.card := by simp
      _ = 4 := hT_card
  omega


set_option maxHeartbeats 1000000 in
lemma copy_tetra_contains_u_impossible
    (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v)
    (P' : Finset (triCS (copyGraph G v u)).O)
    (P'' : Finset (triCS (copyGraph G u v)).O)
    (hP' : CSFeasible (triCS (copyGraph G v u)) P')
    (hP'' : CSFeasible (triCS (copyGraph G u v)) P'')
    (U : Finset V) (hU : U.card = 4) (hu : u ∈ U)
    (hfaces : ∀ t ∈ U.powersetCard 3, t ∈ G.cliqueFinset 3) :
    let T₂ : (triCS G).O → ℕ := fun t =>
      (P'.filter (fun s => copyMap v u s.1 = t.1)).card +
      (P''.filter (fun s => copyMap u v s.1 = t.1)).card
    ¬ (∀ t : (triCS G).O, t.1 ∈ U.powersetCard 3 → 0 < T₂ t) := by
  simp only
  intro h_all
  -- If v ∈ U, then since u ∈ U and |U| = 4 ≥ 3, we can find w ∈ U with w ≠ u, v
  -- Then {u, v, w} ⊆ U with card 3 (when u ≠ v), but u and v are not adjacent
  -- This contradicts hfaces
  by_cases hvU : v ∈ U
  · -- v ∈ U: find w ∈ U \ {u, v} and derive contradiction
    have hUVsub : ({u, v} : Finset V) ⊆ U := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hu
      · simp only [Finset.mem_singleton] at hx'
        exact hx' ▸ hvU
    have hUVcard : ({u, v} : Finset V).card ≤ 2 := by apply Finset.card_insert_le
    have hdiff_nonempty : (U \ {u, v}).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have hsub : U ⊆ {u, v} := by
        intro x hx
        by_contra hxnot
        have : x ∈ U \ {u, v} := Finset.mem_sdiff.mpr ⟨hx, hxnot⟩
        rw [h] at this
        contradiction
      have := Finset.card_le_card hsub
      have hp : ({u, v} : Finset V).card ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨w, hw⟩ := hdiff_nonempty
    have hwU : w ∈ U := Finset.mem_sdiff.mp hw |>.1
    have hwnu : w ≠ u := by simp at hw; exact hw.2.1
    have hwnv : w ≠ v := by simp at hw; exact hw.2.2
    by_cases huv_eq : u = v
    · -- u = v: In this case copyGraph G u u = G
      subst huv_eq
      -- When u = v, copyMap u u = id, so P'_U = {s ∈ P' | s.1 ∈ U.powersetCard 3}
      -- All triangles in U form a K₄, so any packing has at most 1 triangle from U
      -- Thus |P'_U| ≤ 1 and |P''_U| ≤ 1, but we need |P'_U| + |P''_U| ≥ 4
      have copyMap_uu_id : ∀ s : (triCS (copyGraph G u u)).O, copyMap u u s.1 = s.1 := by
        intro s
        ext x
        simp only [copyMap, Finset.mem_image]
        constructor
        · rintro ⟨a, ha, rfl⟩
          by_cases hxu : a = u <;> simp [hxu]
          · exact hxu ▸ ha
          · assumption
        · intro hx
          refine ⟨x, hx, ?_⟩
          by_cases hxu : x = u <;> simp [hxu]
      -- Define P'_U and P''_U
      let P'_U := P'.filter (fun s => copyMap u u s.1 ∈ U.powersetCard 3)
      let P''_U := P''.filter (fun s => copyMap u u s.1 ∈ U.powersetCard 3)
      -- copyMap is injective (it's the identity)
      have h_injP' : Set.InjOn (fun (s : (triCS (copyGraph G u u)).O) => copyMap u u s.1) P' := by
        intro a ha b hb hab
        simp only [copyMap_uu_id] at hab
        exact Subtype.ext hab
      have h_injP'' : Set.InjOn (fun (s : (triCS (copyGraph G u u)).O) => copyMap u u s.1) P'' := by
        intro a ha b hb hab
        simp only [copyMap_uu_id] at hab
        exact Subtype.ext hab
      -- Images have same cardinality as domains
      have himgP'_card : (P'_U.image (fun s => copyMap u u s.1)).card = P'_U.card := by
        apply Finset.card_image_of_injOn
        exact h_injP'.mono (Finset.filter_subset _ _)
      have himgP''_card : (P''_U.image (fun s => copyMap u u s.1)).card = P''_U.card := by
        apply Finset.card_image_of_injOn
        exact h_injP''.mono (Finset.filter_subset _ _)
      -- P'_U triangles are subsets of U (since copyMap u u = id)
      have hP'_U_subset : ∀ s ∈ P'_U, s.1 ⊆ U := by
        intro s hs
        simp only [P'_U, Finset.mem_filter, copyMap_uu_id] at hs
        exact (Finset.mem_powersetCard.mp hs.2).1
      have hP''_U_subset : ∀ s ∈ P''_U, s.1 ⊆ U := by
        intro s hs
        simp only [P''_U, Finset.mem_filter, copyMap_uu_id] at hs
        exact (Finset.mem_powersetCard.mp hs.2).1
      -- P'_U.card ≤ 1 and P''_U.card ≤ 1 (packing on K₄)
      have hP'_U_card : P'_U.card ≤ 1 := by
        by_contra hc
        push_neg at hc
        have hne : P'_U.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨s1, hs1⟩ := hne
        obtain ⟨s2, hs2, hsne⟩ : ∃ s2 ∈ P'_U, s2 ≠ s1 := by
          by_contra hall
          push_neg at hall
          have : P'_U = {s1} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hs1, hall⟩
          simp [this] at hc
        obtain ⟨hs1_mem, _⟩ := Finset.mem_filter.mp hs1
        obtain ⟨hs2_mem, _⟩ := Finset.mem_filter.mp hs2
        have hconf : (triCS (copyGraph G u u)).K s1 s2 := by
          refine ⟨?_, ?_⟩
          · intro heq; apply hsne; exact Subtype.ext heq.symm
          · have hs1U := hP'_U_subset s1 hs1
            have hs2U := hP'_U_subset s2 hs2
            have hs1card : s1.1.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp s1.2).2
            have hs2card : s2.1.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp s2.2).2
            have hUeq : U ∪ {u} = U := by ext x; simp [hu]
            have hUcard : (U ∪ {u}).card = 4 := by simp [hUeq, hU]
            have hsub12 : s1.1 ∩ s2.1 ⊆ U ∪ {u} := by rw [hUeq]; exact Finset.Subset.trans (Finset.inter_subset_inter hs1U hs2U) (by simp)
            have hunion : s1.1 ∪ s2.1 ⊆ U ∪ {u} := by rw [hUeq]; exact Finset.Subset.trans (Finset.union_subset hs1U hs2U) (by simp)
            have hunion_card : (s1.1 ∪ s2.1).card ≤ 4 := by
              have := Finset.card_le_card hunion
              simp only [hUcard] at this
              exact this
            have hcard_formula := Finset.card_union_add_card_inter s1.1 s2.1
            have hcard_inter_lt : (s1.1 ∩ s2.1).card < 3 := by
              by_contra h
              push_neg at h
              have hle : (s1.1 ∩ s2.1).card ≤ 3 := le_trans (Finset.card_le_card (Finset.inter_subset_left)) hs1card.le
              have h1 : (s1.1 ∩ s2.1).card = 3 := by omega
              have heq1 : s1.1 ∩ s2.1 = s1.1 := by
                exact Finset.eq_of_subset_of_card_le (Finset.inter_subset_left) (by simp [h1, hs1card])
              have heq2 : s1.1 ∩ s2.1 = s2.1 := by
                exact Finset.eq_of_subset_of_card_le (Finset.inter_subset_right) (by simp [h1, hs2card])
              exact hsne.symm (Subtype.ext (heq1.symm.trans heq2))
            omega
        have hnotconf := hP' hs1_mem hs2_mem
        exact hnotconf hconf
      have hP''_U_card : P''_U.card ≤ 1 := by
        by_contra hc
        push_neg at hc
        have hne : P''_U.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨s1, hs1⟩ := hne
        obtain ⟨s2, hs2, hsne⟩ : ∃ s2 ∈ P''_U, s2 ≠ s1 := by
          by_contra hall
          push_neg at hall
          have : P''_U = {s1} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hs1, hall⟩
          simp [this] at hc
        obtain ⟨hs1_mem, _⟩ := Finset.mem_filter.mp hs1
        obtain ⟨hs2_mem, _⟩ := Finset.mem_filter.mp hs2
        have hconf : (triCS (copyGraph G u u)).K s1 s2 := by
          refine ⟨?_, ?_⟩
          · intro heq; apply hsne; exact Subtype.ext heq.symm
          · have hs1U := hP''_U_subset s1 hs1
            have hs2U := hP''_U_subset s2 hs2
            have hs1card : s1.1.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp s1.2).2
            have hs2card : s2.1.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp s2.2).2
            have hUeq : U ∪ {u} = U := by ext x; simp [hu]
            have hUcard : (U ∪ {u}).card = 4 := by simp [hUeq, hU]
            have hsub12 : s1.1 ∩ s2.1 ⊆ U ∪ {u} := by rw [hUeq]; exact Finset.Subset.trans (Finset.inter_subset_inter hs1U hs2U) (by simp)
            have hunion : s1.1 ∪ s2.1 ⊆ U ∪ {u} := by rw [hUeq]; exact Finset.Subset.trans (Finset.union_subset hs1U hs2U) (by simp)
            have hunion_card : (s1.1 ∪ s2.1).card ≤ 4 := by
              have := Finset.card_le_card hunion
              simp only [hUcard] at this
              exact this
            have hcard_formula := Finset.card_union_add_card_inter s1.1 s2.1
            have hcard_inter_lt : (s1.1 ∩ s2.1).card < 3 := by
              by_contra h
              push_neg at h
              have hle : (s1.1 ∩ s2.1).card ≤ 3 := le_trans (Finset.card_le_card (Finset.inter_subset_left)) hs1card.le
              have h1 : (s1.1 ∩ s2.1).card = 3 := by omega
              have heq1 : s1.1 ∩ s2.1 = s1.1 := by
                exact Finset.eq_of_subset_of_card_le (Finset.inter_subset_left) (by simp [h1, hs1card])
              have heq2 : s1.1 ∩ s2.1 = s2.1 := by
                exact Finset.eq_of_subset_of_card_le (Finset.inter_subset_right) (by simp [h1, hs2card])
              exact hsne.symm (Subtype.ext (heq1.symm.trans heq2))
            omega
        have hnotconf := hP'' hs1_mem hs2_mem
        exact hnotconf hconf
      -- Every triangle in U.powersetCard 3 is covered by P' or P''
      -- Since copyMap u u = id, the triangles in P'_U and P''_U are exactly those covered
      have h_card_U : (U.powersetCard 3).card = 4 := by simp [hU]
      -- Define the image sets
      let imgP' := P'_U.image (fun s => copyMap u u s.1)
      let imgP'' := P''_U.image (fun s => copyMap u u s.1)
      have himgP'_card : imgP'.card = P'_U.card := Finset.card_image_of_injOn
        (h_injP'.mono (Finset.filter_subset _ _))
      have himgP''_card : imgP''.card = P''_U.card := Finset.card_image_of_injOn
        (h_injP''.mono (Finset.filter_subset _ _))
      -- The images are subsets of U.powersetCard 3
      have himgP'_sub : imgP' ⊆ U.powersetCard 3 := by
        intro t ht; rw [Finset.mem_image] at ht; obtain ⟨s, hs, rfl⟩ := ht; exact (Finset.mem_filter.mp hs).2
      have himgP''_sub : imgP'' ⊆ U.powersetCard 3 := by
        intro t ht; rw [Finset.mem_image] at ht; obtain ⟨s, hs, rfl⟩ := ht; exact (Finset.mem_filter.mp hs).2
      -- Every t ∈ U.powersetCard 3 is in imgP' ∪ imgP''
      have hcover : U.powersetCard 3 ⊆ imgP' ∪ imgP'' := by
        intro t ht
        let t' : (triCS G).O := ⟨t, hfaces t ht⟩
        have hh := h_all t' ht
        have hpos : 0 < ({s ∈ P' | copyMap u u s.1 = t}).card + ({s ∈ P'' | copyMap u u s.1 = t}).card := hh
        by_cases hP'pos : 0 < ({s ∈ P' | copyMap u u s.1 = t}).card
        · have : ({s ∈ P' | copyMap u u s.1 = t}).Nonempty := Finset.card_pos.mp hP'pos
          obtain ⟨s, hs⟩ := this
          have hsP'_U : s ∈ P'_U := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, by rw [(Finset.mem_filter.mp hs).2]; exact ht⟩
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, hsP'_U, (Finset.mem_filter.mp hs).2⟩)
        · have hP''pos : 0 < ({s ∈ P'' | copyMap u u s.1 = t}).card := by omega
          have : ({s ∈ P'' | copyMap u u s.1 = t}).Nonempty := Finset.card_pos.mp hP''pos
          obtain ⟨s, hs⟩ := this
          have hsP''_U : s ∈ P''_U := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, by rw [(Finset.mem_filter.mp hs).2]; exact ht⟩
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, hsP''_U, (Finset.mem_filter.mp hs).2⟩)
      -- Therefore |P'_U| + |P''_U| = |imgP'| + |imgP''| ≥ |U.powersetCard 3| = 4
      have := Finset.card_le_card hcover
      rw [h_card_U] at this
      have hunion : (imgP' ∪ imgP'').card ≤ imgP'.card + imgP''.card := Finset.card_union_le _ _
      omega
    · have hcard : ({u, v, w} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
        · rfl
        · intro h; simp at h; rcases h with rfl | rfl; tauto
        · intro h; simp at h; rcases h with rfl | rfl <;> tauto
      have hsubset : ({u, v, w} : Finset V) ⊆ U := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> [exact hu; exact hvU; exact hwU]
      have hmem : ({u, v, w} : Finset V) ∈ U.powersetCard 3 := by
        exact Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩
      have hclique := hfaces _ hmem
      have hu_in : u ∈ ({u, v, w} : Finset V) := by simp
      have hv_in : v ∈ ({u, v, w} : Finset V) := by simp
      have hadj' := (SimpleGraph.mem_cliqueFinset_iff.mp hclique).isClique hu_in hv_in huv_eq
      exact False.elim (huv hadj')
  · -- v ∉ U: proceed with original proof
    -- Define the subsets of P' and P'' that cover triangles in U
    let P'_U := P'.filter (fun s => copyMap v u s.1 ∈ U.powersetCard 3)
    let P''_U := P''.filter (fun s => copyMap u v s.1 ∈ U.powersetCard 3)
    -- Every triangle in U.powersetCard 3 is covered by some element of P' or P''
    have h_cover : ∀ t : (triCS G).O, t.1 ∈ U.powersetCard 3 →
        (∃ s ∈ P', copyMap v u s.1 = t.1) ∨ (∃ s ∈ P'', copyMap u v s.1 = t.1) := by
      intro t ht
      have hpos : 0 < ({s ∈ P' | copyMap v u s.1 = t.1}).card + ({s ∈ P'' | copyMap u v s.1 = t.1}).card := h_all t ht
      by_cases h : ({s ∈ P' | copyMap v u s.1 = t.1}).card > 0
      · have := Finset.card_pos.mp h
        obtain ⟨s, hs⟩ := this
        exact Or.inl ⟨s, Finset.mem_filter.mp hs |>.1, Finset.mem_filter.mp hs |>.2⟩
      · right
        have h' : ({s ∈ P'' | copyMap u v s.1 = t.1}).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨s, hs⟩ := h'
        use s
        exact ⟨Finset.mem_filter.mp hs |>.1, Finset.mem_filter.mp hs |>.2⟩
    -- The number of distinct triangles in U.powersetCard 3 covered by P' is at most P'.card
    -- Similarly for P''
    -- Since each triangle in U.powersetCard 3 needs coverage, we need |P'_U| + |P''_U| ≥ 4
    have h_card_U : (U.powersetCard 3).card = 4 := by simp [hU]
    -- Key: for s ∈ P' with copyMap v u s.1 ∈ U.powersetCard 3, we have s.1 ⊆ U ∪ {v}
    have hP'_U_subset : ∀ s ∈ P'_U, s.1 ⊆ U ∪ {v} := by
      intro s hs
      simp only [P'_U, Finset.mem_filter] at hs
      obtain ⟨hs_mem, hs_in_U⟩ := hs
      rw [Finset.mem_powersetCard] at hs_in_U
      have hs_card : s.1.card = 3 := by
        have := s.2
        rw [SimpleGraph.mem_cliqueFinset_iff] at this
        exact this.2
      have hs_sub := hs_in_U.1
      by_cases hv_s1 : v ∈ s.1
      · -- v ∈ s.1: copyMap v u s.1 = (s.1 \ {v}) ∪ {u}
        have himage : copyMap v u s.1 = (s.1 \ {v}) ∪ {u} := by
          ext x
          simp only [copyMap, Finset.mem_image, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_sdiff]
          constructor
          · rintro ⟨a, ha, rfl⟩
            split_ifs with h
            · simp
            · exact Or.inl ⟨ha, h⟩
          · rintro (⟨hx_s, hxv⟩ | rfl)
            · use x; simp [hxv]; exact hx_s
            · use v; simp [hv_s1]
        have hsub : (s.1 \ {v}) ∪ {u} ⊆ U := himage ▸ hs_sub
        have hsub1 : s.1 \ {v} ⊆ U := by
          apply Finset.Subset.trans _ hsub
          intro x hx
          exact Finset.mem_union_left _ hx
        intro x hx
        by_cases hxv : x = v
        · simp [hxv]
        · have hxv' : x ∉ ({v} : Finset V) := fun h => hxv (Finset.mem_singleton.mp h)
          exact Finset.mem_union_left _ (hsub1 (Finset.mem_sdiff.mpr ⟨hx, hxv'⟩))
      · -- v ∉ s.1: copyMap v u s.1 = s.1
        have heq : copyMap v u s.1 = s.1 := by
          ext x
          simp only [copyMap, Finset.mem_image]
          constructor
          · rintro ⟨a, ha, rfl⟩
            by_cases hav : a = v <;> simp_all
          · intro hx
            have hxv : x ≠ v := fun h => hv_s1 (h ▸ hx)
            exact ⟨x, hx, by simp [hxv]⟩
        have hsub_s1 : s.1 ⊆ U := heq ▸ hs_sub
        exact Finset.Subset.trans hsub_s1 (Finset.subset_union_left)
    -- Similarly for P''_U
    have hP''_U_subset : ∀ s ∈ P''_U, s.1 ⊆ U := by
      intro s hs
      simp only [P''_U, Finset.mem_filter] at hs
      obtain ⟨hs_mem, hs_in_U⟩ := hs
      rw [Finset.mem_powersetCard] at hs_in_U
      have hs_card : s.1.card = 3 := by
        have := s.2
        rw [SimpleGraph.mem_cliqueFinset_iff] at this
        exact this.2
      by_cases hu_s1 : u ∈ s.1
      · -- u ∈ s.1: copyMap u v s.1 = (s.1 \ {u}) ∪ {v}
        have himage : copyMap u v s.1 = (s.1 \ {u}) ∪ {v} := by
          ext x
          simp only [copyMap, Finset.mem_image, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_sdiff]
          constructor
          · rintro ⟨a, ha, rfl⟩
            split_ifs with h
            · simp
            · exact Or.inl ⟨ha, h⟩
          · rintro (⟨ha, hxu⟩ | rfl)
            · exact ⟨x, ha, by simp [hxu]⟩
            · exact ⟨u, hu_s1, by simp⟩
        have hsub : (s.1 \ {u}) ∪ {v} ⊆ U := himage ▸ hs_in_U.1
        intro x hx
        by_cases hxv : x = v
        · rw [hxv]; exact hsub (Finset.mem_union_right _ (Finset.mem_singleton_self _))
        · by_cases hxu : x = u
          · rw [hxu]; exact hu
          · have hxu' : x ∉ ({u} : Finset V) := by simp [hxu]
            have hmem : x ∈ s.1 \ {u} := Finset.mem_sdiff.mpr ⟨hx, hxu'⟩
            exact hsub (Finset.mem_union_left _ hmem)
      · -- u ∉ s.1: copyMap u v s.1 = s.1
        have heq : copyMap u v s.1 = s.1 := by
          ext x
          simp only [copyMap, Finset.mem_image]
          constructor
          · rintro ⟨a, ha, rfl⟩
            by_cases hav : a = u <;> simp_all
          · intro hx
            have hxu : x ≠ u := fun h => hu_s1 (h ▸ hx)
            use x
            simp [hxu]
            exact hx
        exact heq ▸ hs_in_U.1
    -- P''_U triangles are subsets of U (card 4), so any two distinct ones share 2 vertices
    -- Hence P''_U can have at most 1 element if CSFeasible
    have hP''_U_card : P''_U.card ≤ 1 := by
      by_contra h
      push_neg at h
      have hne : P''_U.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨s1, hs1⟩ := hne
      obtain ⟨s2, hs2, hsne⟩ : ∃ s2 ∈ P''_U, s2 ≠ s1 := by
        by_contra hall
        push_neg at hall
        have : P''_U = {s1} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hs1, hall⟩
        simp [this] at h
      -- Extract P'' membership from P''_U membership
      obtain ⟨hs1_mem, _⟩ := Finset.mem_filter.mp hs1
      obtain ⟨hs2_mem, _⟩ := Finset.mem_filter.mp hs2
      have hconf : (triCS (copyGraph G u v)).K s1 s2 := by
        refine ⟨?_, ?_⟩
        · intro heq
          apply hsne
          exact Subtype.ext heq.symm
        · have hs1U := hP''_U_subset s1 hs1
          have hs2U := hP''_U_subset s2 hs2
          have hs1card : s1.1.card = 3 := by
            have := s1.2
            rw [SimpleGraph.mem_cliqueFinset_iff] at this
            exact this.2
          have hs2card : s2.1.card = 3 := by
            have := s2.2
            rw [SimpleGraph.mem_cliqueFinset_iff] at this
            exact this.2
          have hUcard : U.card = 4 := hU
          -- Two distinct 3-element subsets of a 4-element set share exactly 2 elements
          have hcard_inter : (s1.1 ∩ s2.1).card = 2 := by
            have hsub12 : s1.1 ∩ s2.1 ⊆ U :=
              Finset.Subset.trans (Finset.inter_subset_inter hs1U hs2U) (by simp)
            have hunion : s1.1 ∪ s2.1 ⊆ U := Finset.union_subset hs1U hs2U
            have hunion_card : (s1.1 ∪ s2.1).card ≤ 4 := by
              have := Finset.card_le_card hunion
              simp [hUcard] at this
              exact this
            have hcard_formula := Finset.card_union_add_card_inter s1.1 s2.1
            have hcard_inter_le : (s1.1 ∩ s2.1).card ≤ 3 := by
              calc (s1.1 ∩ s2.1).card ≤ s1.1.card := Finset.card_le_card (Finset.inter_subset_left)
                _ = 3 := hs1card
            have hcard_inter_le' : (s1.1 ∩ s2.1).card < 3 := by
              by_contra h
              push_neg at h
              have h1 : (s1.1 ∩ s2.1).card = 3 := by omega
              have heq1 : s1.1 ∩ s2.1 = s1.1 := by
                exact Finset.eq_of_subset_of_card_le (Finset.inter_subset_left) (by simp [h1, hs1card])
              have heq2 : s1.1 ∩ s2.1 = s2.1 := by
                exact Finset.eq_of_subset_of_card_le (Finset.inter_subset_right) (by simp [h1, hs2card])
              exact hsne.symm (Subtype.ext (heq1.symm.trans heq2))
            omega
          exact hcard_inter ▸ le_rfl
      have hnotconf := hP'' hs1_mem hs2_mem
      exact hnotconf hconf
    -- Every triangle in U is covered by P' or P''
    -- Key fact: |P'_U| + |P''_U| ≥ |U.powersetCard 3| = 4
    -- copyMap is injective on feasible packings
    have copyMap_inj : ∀ (Q : Finset (triCS (copyGraph G v u)).O),
      CSFeasible (triCS (copyGraph G v u)) Q →
      Set.InjOn (fun s : (triCS (copyGraph G v u)).O => copyMap v u s.1) Q := by
        intro Q hQ a ha b hb hab
        apply Subtype.ext
        by_contra hne
        apply hQ ha hb
        constructor
        · exact hne
        · have himage : (copyMap v u a.1).card = 3 :=
            (SimpleGraph.mem_cliqueFinset_iff.mp
              (copyMap_mem_triangles G v u huv a.1 a.2)).2
          have hsub : copyMap v u a.1 \ {u} ⊆ a.1 ∩ b.1 := by
            intro x hx
            have hximg : x ∈ copyMap v u a.1 := (Finset.mem_sdiff.mp hx).1
            have hxu : x ≠ u := by simpa using (Finset.mem_sdiff.mp hx).2
            have hxa : x ∈ a.1 := by
              rw [copyMap, Finset.mem_image] at hximg
              obtain ⟨y, hya, hy⟩ := hximg
              by_cases hyv : y = v
              · subst y
                exact False.elim (hxu (by simpa using hy.symm))
              · have hyx : y = x := by simpa [hyv] using hy
                rwa [← hyx]
            have hximg' : x ∈ copyMap v u b.1 := by
              change copyMap v u a.1 = copyMap v u b.1 at hab
              rw [← hab]
              exact hximg
            have hxb : x ∈ b.1 := by
              rw [copyMap, Finset.mem_image] at hximg'
              obtain ⟨y, hyb, hy⟩ := hximg'
              by_cases hyv : y = v
              · subst y
                exact False.elim (hxu (by simpa using hy.symm))
              · have hyx : y = x := by simpa [hyv] using hy
                rwa [← hyx]
            simp [hxa, hxb]
          have hcarddiff : 2 ≤ (copyMap v u a.1 \ {u}).card := by
            rw [Finset.card_sdiff]
            have hone : ({u} ∩ copyMap v u a.1).card ≤ 1 :=
              (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
            omega
          exact hcarddiff.trans (Finset.card_le_card hsub)
    have copyMap_inj' : ∀ (Q : Finset (triCS (copyGraph G u v)).O),
      CSFeasible (triCS (copyGraph G u v)) Q →
      Set.InjOn (fun s : (triCS (copyGraph G u v)).O => copyMap u v s.1) Q := by
        intro Q hQ a ha b hb hab
        apply Subtype.ext
        by_contra hne
        apply hQ ha hb
        constructor
        · exact hne
        · have himage : (copyMap u v a.1).card = 3 :=
            (SimpleGraph.mem_cliqueFinset_iff.mp
              (copyMap_mem_triangles G u v (fun h => huv h.symm) a.1 a.2)).2
          have hsub : copyMap u v a.1 \ {v} ⊆ a.1 ∩ b.1 := by
            intro x hx
            have hximg : x ∈ copyMap u v a.1 := (Finset.mem_sdiff.mp hx).1
            have hxv : x ≠ v := by simpa using (Finset.mem_sdiff.mp hx).2
            have hxa : x ∈ a.1 := by
              rw [copyMap, Finset.mem_image] at hximg
              obtain ⟨y, hya, hy⟩ := hximg
              by_cases hyv : y = u
              · subst y
                exact False.elim (hxv (by simpa using hy.symm))
              · have hyx : y = x := by simpa [hyv] using hy
                rwa [← hyx]
            have hximg' : x ∈ copyMap u v b.1 := by
              change copyMap u v a.1 = copyMap u v b.1 at hab
              rw [← hab]
              exact hximg
            have hxb : x ∈ b.1 := by
              rw [copyMap, Finset.mem_image] at hximg'
              obtain ⟨y, hyb, hy⟩ := hximg'
              by_cases hyv : y = u
              · subst y
                exact False.elim (hxv (by simpa using hy.symm))
              · have hyx : y = x := by simpa [hyv] using hy
                rwa [← hyx]
            simp [hxa, hxb]
          have hcarddiff : 2 ≤ (copyMap u v a.1 \ {v}).card := by
            rw [Finset.card_sdiff]
            have hone : ({v} ∩ copyMap u v a.1).card ≤ 1 :=
              (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
            omega
          exact hcarddiff.trans (Finset.card_le_card hsub)
    have h_injP'' : Set.InjOn (fun s : (triCS (copyGraph G u v)).O => copyMap u v s.1) P'' :=
        copyMap_inj' P'' hP''
    have h_injP' : Set.InjOn (fun s : (triCS (copyGraph G v u)).O => copyMap v u s.1) P' :=
        copyMap_inj P' hP'
    -- Define the image sets
    let imgP' := P'_U.image (fun s => copyMap v u s.1)
    let imgP'' := P''_U.image (fun s => copyMap u v s.1)
    have himgP'_card : imgP'.card = P'_U.card := Finset.card_image_of_injOn (h_injP'.mono (Finset.filter_subset _ _))
    have himgP''_card : imgP''.card = P''_U.card := Finset.card_image_of_injOn (h_injP''.mono (Finset.filter_subset _ _))
    -- The images are subsets of U.powersetCard 3
    have himgP'_sub : imgP' ⊆ U.powersetCard 3 := by
        intro t ht
        rw [Finset.mem_image] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        exact (Finset.mem_filter.mp hs).2
    have himgP''_sub : imgP'' ⊆ U.powersetCard 3 := by
        intro t ht
        rw [Finset.mem_image] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        exact (Finset.mem_filter.mp hs).2
    -- Every t ∈ U.powersetCard 3 is in imgP' ∪ imgP''
    have hcover : U.powersetCard 3 ⊆ imgP' ∪ imgP'' := by
        intro t ht
        let t' : (triCS G).O := ⟨t, hfaces t ht⟩
        have hh := h_all t' ht
        have hpos : 0 < ({s ∈ P' | copyMap v u s.1 = t}).card + ({s ∈ P'' | copyMap u v s.1 = t}).card := hh
        by_cases hP'pos : 0 < ({s ∈ P' | copyMap v u s.1 = t}).card
        · have : ({s ∈ P' | copyMap v u s.1 = t}).Nonempty := Finset.card_pos.mp hP'pos
          obtain ⟨s, hs⟩ := this
          have hsP'_U : s ∈ P'_U := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, by rw [(Finset.mem_filter.mp hs).2]; exact ht⟩
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, hsP'_U, (Finset.mem_filter.mp hs).2⟩)
        · have hP''pos : 0 < ({s ∈ P'' | copyMap u v s.1 = t}).card := by omega
          have : ({s ∈ P'' | copyMap u v s.1 = t}).Nonempty := Finset.card_pos.mp hP''pos
          obtain ⟨s, hs⟩ := this
          have hsP''_U : s ∈ P''_U := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, by rw [(Finset.mem_filter.mp hs).2]; exact ht⟩
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, hsP''_U, (Finset.mem_filter.mp hs).2⟩)
    -- Therefore |P'_U| + |P''_U| ≥ |U.powersetCard 3| = 4
    have h_sum_ge : P'_U.card + P''_U.card ≥ 4 := by
      have h1 := Finset.card_le_card hcover
      rw [h_card_U] at h1
      have h2 := Finset.card_union_le imgP' imgP''
      rw [himgP'_card, himgP''_card] at h2
      omega
    -- Now show |P'_U| ≤ 2: P'_U is a packing on U ∪ {v} (at most 5 vertices)
    -- Any 3 triangles on 5 vertices must have two that share an edge
    have hP'_U_card : P'_U.card ≤ 2 := by
      by_contra h
      push_neg at h
      -- Get 3 distinct elements of P'_U
      have ⟨s1, hs1, s2, hs2, s3, hs3, hs1ne2, hs1ne3, hs2ne3⟩ := Finset.two_lt_card.mp h
      -- s1, s2, s3 are distinct triangles in P'_U, all with vertex sets ⊆ U ∪ {v}
      have hs1U := hP'_U_subset s1 hs1
      have hs2U := hP'_U_subset s2 hs2
      have hs3U := hP'_U_subset s3 hs3
      have hs1card : s1.1.card = 3 := by
        have := s1.2; rw [SimpleGraph.mem_cliqueFinset_iff] at this; exact this.2
      have hs2card : s2.1.card = 3 := by
        have := s2.2; rw [SimpleGraph.mem_cliqueFinset_iff] at this; exact this.2
      have hs3card : s3.1.card = 3 := by
        have := s3.2; rw [SimpleGraph.mem_cliqueFinset_iff] at this; exact this.2
      have hUVcard : (U ∪ {v}).card = 5 := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hvU)]; simp [hU]
      -- Among three 3-element subsets of a 5-element set, at least two share ≥2 elements
      -- We check all pairs: (s1,s2), (s1,s3), (s2,s3)
      have hconf12 : (s1.1 ∩ s2.1).card ≥ 2 ∨ (s1.1 ∩ s2.1).card ≤ 1 := or_iff_not_imp_left.mpr (fun h => by omega)
      have hconf13 : (s1.1 ∩ s3.1).card ≥ 2 ∨ (s1.1 ∩ s3.1).card ≤ 1 := or_iff_not_imp_left.mpr (fun h => by omega)
      have hconf23 : (s2.1 ∩ s3.1).card ≥ 2 ∨ (s2.1 ∩ s3.1).card ≤ 1 := or_iff_not_imp_left.mpr (fun h => by omega)
      -- If any pair shares ≥2 vertices, they conflict
      by_cases h12 : (s1.1 ∩ s2.1).card ≥ 2
      · have hconf : (triCS (copyGraph G v u)).K s1 s2 := ⟨by exact fun h => hs1ne2 (Subtype.ext h), h12⟩
        have hnotconf := hP' (Finset.mem_filter.mp hs1).1 (Finset.mem_filter.mp hs2).1
        exact absurd (hnotconf hconf) (by norm_num)
      · push_neg at h12
        by_cases h13 : (s1.1 ∩ s3.1).card ≥ 2
        · have hconf : (triCS (copyGraph G v u)).K s1 s3 := ⟨fun h => hs1ne3 (Subtype.ext h), h13⟩
          have hnotconf := hP' (Finset.mem_filter.mp hs1).1 (Finset.mem_filter.mp hs3).1
          exact absurd (hnotconf hconf) (by norm_num)
        · push_neg at h13
          by_cases h23 : (s2.1 ∩ s3.1).card ≥ 2
          · have hconf : (triCS (copyGraph G v u)).K s2 s3 := ⟨fun h => hs2ne3 (Subtype.ext h), h23⟩
            have hnotconf := hP' (Finset.mem_filter.mp hs2).1 (Finset.mem_filter.mp hs3).1
            exact absurd (hnotconf hconf) (by norm_num)
          · push_neg at h23
            -- All pairs share ≤1 vertex
            -- By inclusion-exclusion: |s1 ∪ s2 ∪ s3| = 9 - |s1∩s2| - |s1∩s3| - |s2∩s3| + |s1∩s2∩s3| ≥ 9 - 1 - 1 - 1 = 6
            -- But s1 ∪ s2 ∪ s3 ⊆ U ∪ {v} has card 5, contradiction
            have hunion_sub : (s1.1 ∪ s2.1 ∪ s3.1) ⊆ U ∪ {v} := by
              apply Finset.union_subset (Finset.union_subset hs1U hs2U) hs3U
            have hunion_card_le : (s1.1 ∪ s2.1 ∪ s3.1).card ≤ 5 := by
              have := Finset.card_le_card hunion_sub
              have hUVcard : (U ∪ {v}).card = 5 := by
                rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hvU)]; simp [hU]
              rw [hUVcard] at this
              exact this
            have h12' : (s1.1 ∩ s2.1).card ≤ 1 := by omega
            have h13' : (s1.1 ∩ s3.1).card ≤ 1 := by omega
            have h23' : (s2.1 ∩ s3.1).card ≤ 1 := by omega
            -- Inclusion-exclusion: |s1 ∪ s2 ∪ s3| ≥ 3+3+3 - 1-1-1 = 6
            have hineq : (s1.1 ∪ s2.1 ∪ s3.1).card ≥
                s1.1.card + s2.1.card + s3.1.card - (s1.1 ∩ s2.1).card - (s1.1 ∩ s3.1).card - (s2.1 ∩ s3.1).card := by
              have h1 := Finset.card_union_add_card_inter s1.1 s2.1
              have h2 := Finset.card_union_add_card_inter (s1.1 ∪ s2.1) s3.1
              have h3 : ((s1.1 ∪ s2.1) ∩ s3.1).card ≤ (s1.1 ∩ s3.1).card + (s2.1 ∩ s3.1).card := by
                have hsub : (s1.1 ∪ s2.1) ∩ s3.1 ⊆ (s1.1 ∩ s3.1) ∪ (s2.1 ∩ s3.1) := by
                  intro x hx
                  simp only [Finset.mem_union, Finset.mem_inter] at hx ⊢
                  rcases hx.1 with hx1 | hx2
                  · exact Or.inl ⟨hx1, hx.2⟩
                  · exact Or.inr ⟨hx2, hx.2⟩
                calc ((s1.1 ∪ s2.1) ∩ s3.1).card ≤ ((s1.1 ∩ s3.1) ∪ (s2.1 ∩ s3.1)).card :=
                      Finset.card_le_card hsub
                  _ ≤ (s1.1 ∩ s3.1).card + (s2.1 ∩ s3.1).card := Finset.card_union_le _ _
              omega
            -- Therefore 4 ≤ #P'_U + #P''_U ≤ 2 + 1 = 3, contradiction
            omega
    -- Therefore 4 ≤ #P'_U + #P''_U ≤ 2 + 1 = 3, contradiction
    omega


set_option maxHeartbeats 1000000 in
lemma copy_tetra_support_impossible
    (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v)
    (P' : Finset (triCS (copyGraph G v u)).O)
    (P'' : Finset (triCS (copyGraph G u v)).O)
    (hP' : CSFeasible (triCS (copyGraph G v u)) P')
    (hP'' : CSFeasible (triCS (copyGraph G u v)) P'') :
    let T₂ : (triCS G).O → ℕ := fun t =>
      (P'.filter (fun s => copyMap v u s.1 = t.1)).card +
      (P''.filter (fun s => copyMap u v s.1 = t.1)).card
    ∀ U : Finset V, U.card = 4 →
      (∀ t ∈ U.powersetCard 3, t ∈ G.cliqueFinset 3) →
      ¬ (∀ t : (triCS G).O, t.1 ∈ U.powersetCard 3 → 0 < T₂ t) := by
  dsimp only
  intro U hU hfaces hall
  by_cases hu : u ∈ U
  · exact copy_tetra_contains_u_impossible G v u huv P' P'' hP' hP'' U hU hu hfaces hall
  by_cases hv : v ∈ U
  · have hvu : ¬ G.Adj v u := fun h => huv h.symm
    have h := copy_tetra_contains_u_impossible G u v hvu P'' P' hP'' hP' U hU hv hfaces
    apply h
    intro t ht
    simpa [Nat.add_comm] using hall t ht
  · exact copy_tetra_avoids_centres_impossible G v u P' P'' hP' hP'' U hU hu hv hfaces hall

set_option maxHeartbeats 1000000 in
lemma clique_four_yields_triangle_family
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : (triCS G).O → ℕ)
    (Q : Finset (Copies (triCS G) X))
    (hQ : (Hgraph (triCS G) X).IsNClique 4 Q)
    (hload : ∀ e : Finset V, e.card = 2 →
      (∑ t : (triCS G).O, if e ⊆ t.1 then X t else 0) ≤ 2) :
    let S : Finset (Finset V) := Q.image (fun c => c.1.1)
    S.card = 4 ∧
    (∀ t ∈ S, t.card = 3) ∧
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → 2 ≤ (a ∩ b).card) ∧
    (∀ t : (triCS G).O, t.1 ∈ S → 0 < X t) := by
  cases hQ with
  | mk hclique hcard =>
  let S : Finset (Finset V) := Q.image (fun c => c.1.1)
  -- First show that Q.map (fun c => c.1) is injective (no twins in Q due to load condition)
  have hcardS : S.card = Q.card := by
    rw [card_image_of_injOn]
    intro c₁ hc₁ c₂ hc₂ heq
    -- heq : c₁.1.1 = c₂.1.1 (the Finset V is the same)
    -- First show c₁.1 = c₂.1
    have heqobj : c₁.1 = c₂.1 := Subtype.ext heq
    -- Now heqobj : c₁.1 = c₂.1
    -- If c₁ ≠ c₂, they differ in the copy index, so they are twins in Hgraph
    apply Sigma.ext heqobj
    by_contra hne
    -- We'll derive a contradiction
    -- c₁ and c₂ are different copies of the same triangle, so they are adjacent in Hgraph
    have hne' : c₁ ≠ c₂ := by
      intro h
      apply hne
      exact (Sigma.ext_iff.mp h).2
    have hadj : (Hgraph (triCS G) X).Adj c₁ c₂ := hclique hc₁ hc₂ hne'
    -- The adjacency must be because they're twins (same object)
    unfold Hgraph at hadj
    simp at hadj
    -- The triangle c₁.1 is in G.cliqueFinset 3, so it has 3 vertices
    have htri := c₁.1.2
    rw [SimpleGraph.mem_cliqueFinset_iff] at htri
    -- Get the vertex set of the triangle
    let t := c₁.1.1
    have ht_card : t.card = 3 := htri.2
    -- Since c₁ and c₂ are distinct copies of t, X t ≥ 2
    have hXge2 : X c₁.1 ≥ 2 := by
      -- c₁ = ⟨t, i₁⟩ and c₂ = ⟨t, i₂⟩ with i₁ ≠ i₂
      -- Both are valid copies, so i₁ < X t and i₂ < X t
      have hi₁ : (c₁.snd : ℕ) < X c₁.1 := Fin.is_lt c₁.snd
      have hi₂ : (c₂.snd : ℕ) < X c₂.1 := Fin.is_lt c₂.snd
      have hXeq : X c₁.1 = X c₂.1 := congrArg X heqobj
      -- Convert c₁.snd to Fin (X c₂.1) using hXeq
      set c₁snd' : Fin (X c₂.1) := hXeq ▸ c₁.snd with hc₁snd'
      have hi₁' : c₁snd'.val < X c₂.1 := by simp [hc₁snd']
      have hne' : c₁snd' ≠ c₂.snd := by
        intro h
        apply hne
        simp_all
      have hi₂' : c₂.snd.val < X c₂.1 := Fin.is_lt c₂.snd
      have hge2 : X c₂.1 ≥ 2 := by omega
      rwa [← heqobj] at hge2
    -- Now we have hXge2 : X c₁.1 ≥ 2
    -- Use the load condition: each edge of c₁.1 has load ≥ X c₁.1 ≥ 2
    -- So no other triangle can share an edge with c₁.1
    -- But Q is a 4-clique with at least 2 copies of c₁.1, so there are ≥2 other elements
    -- Each must conflict with c₁.1, contradiction
    -- Pick an edge e of t: t has 3 elements, so there exist a ≠ b in t
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ t, ∃ b ∈ t, a ≠ b := by
      have hcard := ht_card
      rcases Finset.one_lt_card.mp (by omega : 1 < t.card) with ⟨a, ha, b, hb, hab⟩
      exact ⟨a, ha, b, hb, hab⟩
    let e : Finset V := {a, b}
    have he_card : e.card = 2 := by simp [e, hab]
    -- The load on e is at least X t ≥ 2
    have hload_e := hload e he_card
    have hsum_ge : (∑ t' : (triCS G).O, if e ⊆ t'.1 then X t' else 0) ≥ X c₁.1 := by
      have hmem : c₁.1 ∈ Finset.univ := Finset.mem_univ _
      have hif : (if e ⊆ c₁.1.1 then X c₁.1 else 0) = X c₁.1 := by
        rw [if_pos]
        exact fun x hx => by simp only [e, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
      rw [← hif]
      exact Finset.single_le_sum (fun t' _ => Nat.zero_le (if e ⊆ t'.1 then X t' else 0)) hmem
    have hcontra : X c₁.1 ≤ 2 := hsum_ge.trans hload_e
    -- So X c₁.1 = 2, meaning the load on edge e is exactly 2
    -- Q has 4 elements, at least 2 of which are copies of c₁.1
    -- So there exists c₃ ∈ Q with c₃.1 ≠ c₁.1
    -- c₃ must be adjacent to c₁ in Hgraph, so c₃.1 conflicts with c₁.1
    -- This means c₃.1 shares an edge with c₁.1, making load > 2
    have hcardQ : Q.card = 4 := hcard
    -- Count: Q has 4 elements. The set {c : Q | c.1.1 = t} has size ≤ X t ≤ 2
    -- So there exists c₃ ∈ Q with c₃.1.1 ≠ t
    let t : (triCS G).O := c₁.1
    let Q_t : Finset (Copies (triCS G) X) := {c ∈ Q | c.1 = t}
    have hcard_Qt_le : Q_t.card ≤ X t := by
      have hsub : Q_t ⊆ Finset.univ.filter (fun c : Copies (triCS G) X => c.1 = t) := by
        exact Finset.filter_subset_filter _ (Finset.subset_univ Q)
      have hcarg : (Finset.univ.filter (fun c : Copies (triCS G) X => c.1 = t)).card ≤ X t := by
        have heq : Finset.univ.filter (fun c : Copies (triCS G) X => c.1 = t) =
            (Finset.univ : Finset (Fin (X t))).image (fun k : Fin (X t) => (⟨t, k⟩ : Copies (triCS G) X)) := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · intro h
            rw [← h]
            exact ⟨c.2, rfl⟩
          · intro ⟨j, hj⟩
            rw [← hj]
        rw [heq]
        have hinj : Function.Injective (fun k : Fin (X t) => (⟨t, k⟩ : Copies (triCS G) X)) := by
          intro a b h
          simpa using h
        rw [Finset.card_image_of_injective _ hinj]
        simp
      exact le_trans (Finset.card_le_card hsub) hcarg
    have hcard_Qt_lt : Q_t.card < Q.card := by
      calc Q_t.card ≤ X t := hcard_Qt_le
        _ ≤ 2 := hcontra
        _ < 4 := by decide
        _ = Q.card := hcardQ.symm
    obtain ⟨c₃, hc₃Q, hc₃ne⟩ : ∃ c₃ ∈ Q, c₃ ∉ Q_t := by
      by_contra hall
      push_neg at hall
      have hall' : ∀ x ∈ Q, x.1 = t := by
        intro x hx
        have := hall x hx
        rw [Finset.mem_filter] at this
        exact this.2
      have hQeq : Q_t = Q := Finset.filter_eq_self.mpr hall'
      rw [hQeq] at hcard_Qt_lt
      omega
    -- c₃.1 ≠ t
    have hc₃_t_ne : c₃.1 ≠ t := fun h => hc₃ne (Finset.mem_filter.mpr ⟨hc₃Q, h⟩)
    -- c₃ is adjacent to c₁ in Hgraph
    have hc₃_ne_c₁ : c₃ ≠ c₁ := by
      intro heq
      apply hc₃ne
      rw [heq]
      exact Finset.mem_filter.mpr ⟨hc₁, rfl⟩
    have hadj₃ : (Hgraph (triCS G) X).Adj c₃ c₁ := hclique hc₃Q hc₁ hc₃_ne_c₁
    -- Since c₃.1 ≠ c₁.1, they must conflict
    unfold Hgraph at hadj₃
    simp at hadj₃
    -- hadj₃ : c₃ ≠ c₁ ∧ (c₃.1 = c₁.1 ∨ (triCS G).K c₃.1 c₁.1)
    have hconf : (triCS G).K c₃.1 c₁.1 := by
      rcases hadj₃.2 with h | h
      · exact absurd h hc₃_t_ne
      · exact ⟨fun he => h.1 (Subtype.ext he), h.2⟩
    -- K means |c₃.1.1 ∩ c₁.1|.card ≥ 2
    -- So c₃.1 and c₁.1 share an edge, contradicting the load bound
    obtain ⟨hne, hcard_int⟩ := hconf
    -- Find an edge e in the intersection
    obtain ⟨a, ha_int, b, hb_int, hab⟩ : ∃ a ∈ c₃.1.1 ∩ c₁.1.1, ∃ b ∈ c₃.1.1 ∩ c₁.1.1, a ≠ b := by
      exact Finset.one_lt_card.mp hcard_int
    have ha₁ : a ∈ c₁.1.1 := Finset.mem_inter.mp ha_int |>.2
    have ha₃ : a ∈ c₃.1.1 := Finset.mem_inter.mp ha_int |>.1
    have hb₁ : b ∈ c₁.1.1 := Finset.mem_inter.mp hb_int |>.2
    have hb₃ : b ∈ c₃.1.1 := Finset.mem_inter.mp hb_int |>.1
    -- The edge {a, b} has load ≥ 3, contradicting hload
    let e : Finset V := {a, b}
    have he_card : e.card = 2 := by simp [e, hab]
    have hload_e := hload e he_card
    -- The load on e is at least X c₁.1 + X c₃.1 ≥ 2 + 1 = 3
    have hsum_ge : (∑ t' : (triCS G).O, if e ⊆ t'.1 then X t' else 0) ≥ X c₁.1 + X c₃.1 := by
      have he_sub₁ : e ⊆ c₁.1.1 := by
        intro x hx
        simp only [e, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have he_sub₃ : e ⊆ c₃.1.1 := by
        intro x hx
        simp only [e, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hif₁ : (if e ⊆ c₁.1.1 then X c₁.1 else 0) = X c₁.1 := if_pos he_sub₁
      have hif₃ : (if e ⊆ c₃.1.1 then X c₃.1 else 0) = X c₃.1 := if_pos he_sub₃
      have h₁ := Finset.single_le_sum (fun t' _ => Nat.zero_le (if e ⊆ t'.1 then X t' else 0))
        (Finset.mem_univ c₁.1)
      have h₃ := Finset.single_le_sum (fun t' _ => Nat.zero_le (if e ⊆ t'.1 then X t' else 0))
        (Finset.mem_univ c₃.1)
      rw [hif₁] at h₁
      rw [hif₃] at h₃
      have hdist : c₁.1 ≠ c₃.1 := by
        intro h
        apply hc₃_t_ne
        simp [t, h]
      have hsum_two : X c₁.1 + X c₃.1 ≤ ∑ t' ∈ {c₁.1, c₃.1}, if e ⊆ t'.1 then X t' else 0 := by
        rw [Finset.sum_pair hdist]
        simp [he_sub₁, he_sub₃]
      calc X c₁.1 + X c₃.1 ≤ ∑ t' ∈ {c₁.1, c₃.1}, if e ⊆ t'.1 then X t' else 0 := hsum_two
        _ ≤ ∑ t' : (triCS G).O, if e ⊆ t'.1 then X t' else 0 := Finset.sum_le_sum_of_subset (by intro x hx; exact Finset.mem_univ x)
    have hcontra2 : X c₁.1 + X c₃.1 > 2 := by
      have hXc₃ : X c₃.1 ≥ 1 := by
        have := c₃.snd.is_lt
        omega
      omega
    have hcontra3 : X c₁.1 + X c₃.1 ≤ 2 := hsum_ge.trans hload_e
    exact False.elim (by omega)
  -- Now we have hcardS : #S = #Q = 4
  refine ⟨by rw [hcardS, hcard], ?_, ?_, ?_⟩
  · -- ∀ t ∈ S, t.card = 3
    intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨c, hc, rfl⟩ := ht
    have := c.1.2
    rw [SimpleGraph.mem_cliqueFinset_iff] at this
    exact this.2
  · -- ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 2 ≤ #(a ∩ b)
    intro a ha b hb hab
    simp only [Finset.mem_image] at ha hb
    obtain ⟨c₁, hc₁, rfl⟩ := ha
    obtain ⟨c₂, hc₂, rfl⟩ := hb
    have hne : c₁.1 ≠ c₂.1 := by intro h; apply hab; simp_all
    have hadj : (Hgraph (triCS G) X).Adj c₁ c₂ := hclique hc₁ hc₂ (by
      intro h
      apply hne
      exact congrArg Sigma.fst h)
    unfold Hgraph at hadj
    simp at hadj
    obtain ⟨_, hconf⟩ := hadj
    rcases hconf with h | h
    · exact absurd h (fun heq => hab (by simp [heq]))
    · exact h.2
  · -- ∀ t : (triCS G).O, t.1 ∈ S → 0 < X t
    intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨c, hc, ht_eq⟩ := ht
    have heq : c.1 = t := Subtype.ext ht_eq
    rw [← heq]
    have h := c.snd.is_lt
    omega

set_option maxHeartbeats 10000000 in
/-- Claim 4.1b: the conflict graph of the multiset obtained from the two copied packings
contains no four-clique. -/
lemma copy_integral_cliqueFree_four
    (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v)
    (P' : Finset (triCS (copyGraph G v u)).O)
    (P'' : Finset (triCS (copyGraph G u v)).O)
    (hP' : CSFeasible (triCS (copyGraph G v u)) P')
    (hP'' : CSFeasible (triCS (copyGraph G u v)) P'') :
    let T₂ : (triCS G).O → ℕ := fun t =>
      (P'.filter (fun s => copyMap v u s.1 = t.1)).card +
      (P''.filter (fun s => copyMap u v s.1 = t.1)).card
    (Hgraph (triCS G) T₂).CliqueFree 4 := by
  classical
  dsimp only
  intro Q hQ
  have hload := copy_integral_edgeLoad_le_two G v u huv P' P'' hP' hP''
  dsimp only at hload
  let S : Finset (Finset V) := Q.image (fun c => c.1.1)
  obtain ⟨hScard, hStri, hSpair, hSpos⟩ :=
    clique_four_yields_triangle_family G _ Q hQ hload
  rcases four_triangles_book_or_tetrahedron S hScard hStri hSpair with hbook | htetra
  · obtain ⟨e, hecard, heS⟩ := hbook
    have hsum_ge : S.card ≤ ∑ t : (triCS G).O,
        if e ⊆ t.1 then
          (P'.filter (fun s => copyMap v u s.1 = t.1)).card +
          (P''.filter (fun s => copyMap u v s.1 = t.1)).card else 0 := by
      let f : S → (triCS G).O := fun t =>
        ⟨t.1, by
          have htcard := hStri t.1 t.2
          rw [SimpleGraph.mem_cliqueFinset_iff]
          refine ⟨?_, htcard⟩
          intro a ha b hb hab
          obtain ⟨c, hcQ, hcval⟩ := Finset.mem_image.mp t.2
          have ha' : a ∈ c.1.1 := by rwa [hcval]
          have hb' : b ∈ c.1.1 := by rwa [hcval]
          exact (SimpleGraph.mem_cliqueFinset_iff.mp c.1.2).1 ha' hb' hab⟩
      have hf_inj : Function.Injective f := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : (triCS G).O => z.1) hab
      calc
        S.card = ∑ x : S, 1 := by simp
        _ ≤ ∑ x : S, (if e ⊆ (f x).1 then
            (P'.filter (fun s => copyMap v u s.1 = (f x).1)).card +
            (P''.filter (fun s => copyMap u v s.1 = (f x).1)).card else 0) := by
          apply Finset.sum_le_sum
          intro x hx
          rw [if_pos (heS x.1 x.2)]
          exact hSpos (f x) x.2
        _ ≤ ∑ t : (triCS G).O, (if e ⊆ t.1 then
            (P'.filter (fun s => copyMap v u s.1 = t.1)).card +
            (P''.filter (fun s => copyMap u v s.1 = t.1)).card else 0) := by
          let w : (triCS G).O → ℕ := fun t => if e ⊆ t.1 then
            (P'.filter (fun s => copyMap v u s.1 = t.1)).card +
            (P''.filter (fun s => copyMap u v s.1 = t.1)).card else 0
          change (∑ x : S, w (f x)) ≤ ∑ t : (triCS G).O, w t
          rw [← Finset.sum_image (s := Finset.univ) (fun _ _ _ _ h => hf_inj h)]
          exact Finset.sum_le_sum_of_subset_of_nonneg (by intro x hx; exact Finset.mem_univ x) (fun _ _ _ => Nat.zero_le _)
    have hbound := hload e hecard
    rw [hScard] at hsum_ge
    have hbad : 4 ≤ 2 := hsum_ge.trans hbound
    omega
  · obtain ⟨U, hU, hSU⟩ := htetra
    apply copy_tetra_support_impossible G v u huv P' P'' hP' hP'' U hU
    · intro t ht
      have htS : t ∈ S := by rwa [hSU]
      obtain ⟨c, hcQ, hc⟩ := Finset.mem_image.mp htS
      rw [← hc]
      exact c.1.2
    · intro t ht
      apply hSpos t
      change t.1 ∈ S
      rw [hSU]
      exact ht

/-- **Theorem 4.2 strengthened with Claim 4.1a/b (structural).** The same witness multiset
`T₂ = φ'(P') ⊎ φ''(P'')` additionally has a *subcubic* and *K₄-free* conflict graph `H[T₂]`.

Claim 4.1a (Δ ≤ 3): `P'` and `P''` are feasible packings, i.e. edge-disjoint triangle families
in the respective copy graphs; hence each of the three edges of a triangle `t` lies in at most
one triangle of the opposite family, so a copy `(t,k)` has at most three conflicting copies
(its twin counts against one of the three edge slots).  Claim 4.1b (K₄-free): four pairwise
edge-sharing triangles at multiplicity ≤ 2 cannot embed in the copy construction.

The two structural conjuncts close the N1 obligation; the size identity and the transfer bound are
exactly as in `copy_integral`. -/
theorem copy_integral_struct (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V)
    (huv : ¬ G.Adj u v) :
    ∃ T₂ : (triCS G).O → ℕ,
      multSize (triCS G) T₂ = nu3 (copyGraph G v u) + nu3 (copyGraph G u v) ∧
      nu3 (copyGraph G v u) + nu3 (copyGraph G u v)
        ≤ 2 * nu3 G + oct (Hgraph (triCS G) T₂) ∧
      (Hgraph (triCS G) T₂).maxDegree ≤ 3 ∧
      (Hgraph (triCS G) T₂).CliqueFree 4 := by
  classical
  obtain ⟨P', hP', hP'card⟩ := exists_max_feasible (triCS (copyGraph G v u))
  have hvu : ¬G.Adj v u := fun h => huv h.symm
  obtain ⟨P'', hP'', hP''card⟩ := exists_max_feasible (triCS (copyGraph G u v))
  let T₂ : (triCS G).O → ℕ := fun t =>
    (P'.filter (fun s => copyMap v u s.1 = t.1)).card +
    (P''.filter (fun s => copyMap u v s.1 = t.1)).card
  have hinj' := copyMap_injective_on_feasible G v u huv P' hP'
  have hinj'' := copyMap_injective_on_feasible G u v hvu P'' hP''
  have hqm : IsQMultiset (triCS G) T₂ 2 := by
    intro t
    have hleft : (P'.filter (fun s => copyMap v u s.1 = t.1)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      apply hinj' (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
      exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    have hright : (P''.filter (fun s => copyMap u v s.1 = t.1)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      apply hinj'' (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
      exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    exact Nat.add_le_add hleft hright
  have hsize : multSize (triCS G) T₂ = P'.card + P''.card := by
    simp only [multSize, T₂, Finset.sum_add_distrib]
    rw [← card_copyMap_fibers G v u huv P', ← card_copyMap_fibers G u v hvu P'']
  have hsize' : multSize (triCS G) T₂
      = nu3 (copyGraph G v u) + nu3 (copyGraph G u v) := by
    show multSize (triCS G) T₂
      = nu (triCS (copyGraph G v u)) + nu (triCS (copyGraph G u v))
    rw [hsize, hP'card, hP''card]
  have hbound := transfer_half (triCS G) T₂ hqm
  rw [hsize, hP'card, hP''card] at hbound
  have hload : ∀ e : Finset V, e.card = 2 →
      (∑ t : (triCS G).O, if e ⊆ t.1 then T₂ t else 0) ≤ 2 := by
    simpa only [T₂] using
      copy_integral_edgeLoad_le_two G v u huv P' P'' hP' hP''
  refine ⟨T₂, hsize', hbound,
    triangle_Hgraph_maxDegree_le_three G T₂ hload, ?_⟩
  simpa only [T₂] using
    copy_integral_cliqueFree_four G v u huv P' P'' hP' hP''


end PaperV
