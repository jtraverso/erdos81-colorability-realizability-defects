/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV/V — Theorem A (integral part): weighted copy inequality for the mixed {K₃, K₄} family.

Objects: cliques of `G` of size 3 or 4 (`mixedCS G`), conflicting when they share an edge, with a
gain depending only on the size (`gainOf`, e.g. 2 and 5). For nonadjacent `u, v` and feasible
packings `P'` of `G_{v→u}` and `P''` of `G_{u→v}`, the images under the copy relabellings form a
multiset `X` on `G` with `|X|_w = w(P') + w(P'')`, and the weighted transfer gives

    w(P') + w(P'') ≤ 2 · ν_w(G) + D₂^w(H[X])          (A2)

hence, for optimal packings, `W(G_{v→u}) + W(G_{u→v}) ≤ 2 W(G) + D₂^w(H[X])`.
The fractional statement (A1) and the edge-load-≤2 structure of `X` are not needed for (A2) and are
left to the manuscript / second wave.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.Copy
public import PaperV.WeightedTransfer

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The copy relabelling sends a `k`-clique of `G_{v→u}` to a `k`-clique of `G` (general `k`). -/
theorem copyMap_mem_cliqueFinset (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V)
    (huv : ¬ G.Adj u v) (k : ℕ) (t : Finset V) (ht : t ∈ (copyGraph G v u).cliqueFinset k) :
    copyMap v u t ∈ G.cliqueFinset k := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht ⊢
  constructor
  · intro a ha b hb hab
    rw [copyMap, Finset.mem_coe, Finset.mem_image] at ha hb
    obtain ⟨x, hxt, rfl⟩ := ha
    obtain ⟨y, hyt, rfl⟩ := hb
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hab rfl
    have hadj := ht.1 hxt hyt hxy
    rcases hadj with ⟨hxv, hyv, hG⟩ | ⟨rfl, hyv, hG⟩ | ⟨rfl, hxv, hG⟩
    · simpa [hxv, hyv]
    · simp only [if_pos, if_neg hyv]
      exact hG
    · simp only [if_pos, if_neg hxv]
      exact hG.symm
  · rw [copyMap, Finset.card_image_of_injOn]
    · exact ht.2
    · intro x hxt y hyt hxy
      by_contra hne
      have hadj := ht.1 hxt hyt hne
      by_cases hxv : x = v
      · subst x
        by_cases hyv : y = v
        · exact hne hyv.symm
        · simp [hyv] at hxy
          subst y
          simp [copyGraph, huv] at hadj
      · by_cases hyv : y = v
        · subst y
          simp [hxv] at hxy
          subst x
          simp [copyGraph, huv] at hadj
        · exact hne (by simpa [hxv, hyv] using hxy)

/-- The mixed conflict system: cliques of size 3 or 4, conflicting iff they share an edge. -/
abbrev mixedCS (G : SimpleGraph V) [DecidableRel G.Adj] : ConflictSystem where
  O := {t : Finset V // t ∈ G.cliqueFinset 3 ∨ t ∈ G.cliqueFinset 4}
  K t₁ t₂ := t₁.1 ≠ t₂.1 ∧ 2 ≤ (t₁.1 ∩ t₂.1).card
  Ksymm := by
    rintro a b ⟨h1, h2⟩
    exact ⟨h1.symm, by rwa [Finset.inter_comm]⟩
  Kirrefl := by rintro a ⟨h1, _⟩; exact h1 rfl
  decK := by intro a b; dsimp only; infer_instance

/-- Size-dependent gain as a weight on the mixed system. -/
def mixedWeight (G : SimpleGraph V) [DecidableRel G.Adj] (gainOf : ℕ → ℕ) : (mixedCS G).O → ℕ :=
  fun t => gainOf t.1.card

/-- Total gain of a packing. -/
def packGain (G : SimpleGraph V) [DecidableRel G.Adj] (gainOf : ℕ → ℕ) (P : Finset (mixedCS G).O) : ℕ :=
  ∑ s ∈ P, gainOf s.1.card

/-- The image object of a mixed clique of `G_{v→u}` in `G`. -/
def imgObj (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v)
    (s : (mixedCS (copyGraph G v u)).O) : (mixedCS G).O :=
  ⟨copyMap v u s.1, by
    rcases s.2 with h | h
    · exact Or.inl (copyMap_mem_cliqueFinset G v u huv 3 s.1 h)
    · exact Or.inr (copyMap_mem_cliqueFinset G v u huv 4 s.1 h)⟩

theorem card_imgObj (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v)
    (s : (mixedCS (copyGraph G v u)).O) : (imgObj G v u huv s).1.card = s.1.card := by
  have hk : ∀ k, s.1 ∈ (copyGraph G v u).cliqueFinset k → (copyMap v u s.1).card = s.1.card := by
    intro k hk
    have h1 := (SimpleGraph.mem_cliqueFinset_iff.mp hk).2
    have h2 := (SimpleGraph.mem_cliqueFinset_iff.mp (copyMap_mem_cliqueFinset G v u huv k s.1 hk)).2
    rw [h1, h2]
  rcases s.2 with h | h
  · exact hk 3 h
  · exact hk 4 h

/-- The image multiset of two packings of the two copies. -/
def imageMultiset (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v)
    (hvu : ¬ G.Adj v u) (P' : Finset (mixedCS (copyGraph G v u)).O)
    (P'' : Finset (mixedCS (copyGraph G u v)).O) : (mixedCS G).O → ℕ :=
  fun t => (P'.filter (fun s => imgObj G v u huv s = t)).card +
    (P''.filter (fun s => imgObj G u v hvu s = t)).card

/-- Fibre sum: `Σ_t f(t) · #{s ∈ P : img s = t} = Σ_{s∈P} f(img s)`. -/
theorem sum_fiber_card {A B : Type*} [Fintype B] [DecidableEq B] (P : Finset A) (img : A → B)
    (f : B → ℕ) : ∑ t, f t * (P.filter (fun s => img s = t)).card = ∑ s ∈ P, f (img s) := by
  classical
  rw [← Finset.sum_fiberwise P img (fun s => f (img s))]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.card_eq_sum_ones, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [(Finset.mem_filter.mp hs).2]; ring

/-- `|X|_w = w(P') + w(P'')`: the image multiset carries exactly the gains of both packings. -/
theorem wMultSize_imageMultiset (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V)
    (huv : ¬ G.Adj u v) (hvu : ¬ G.Adj v u) (gainOf : ℕ → ℕ)
    (P' : Finset (mixedCS (copyGraph G v u)).O) (P'' : Finset (mixedCS (copyGraph G u v)).O) :
    wMultSize (mixedCS G) (mixedWeight G gainOf) (imageMultiset G v u huv hvu P' P'') =
      packGain _ gainOf P' + packGain _ gainOf P'' := by
  classical
  unfold wMultSize imageMultiset packGain mixedWeight
  simp only [mul_add, Finset.sum_add_distrib]
  rw [sum_fiber_card P' (imgObj G v u huv) (fun t : (mixedCS G).O => gainOf t.1.card),
    sum_fiber_card P'' (imgObj G u v hvu) (fun t : (mixedCS G).O => gainOf t.1.card)]
  congr 1
  · exact Finset.sum_congr rfl (fun s _ => by rw [card_imgObj])
  · exact Finset.sum_congr rfl (fun s _ => by rw [card_imgObj])

/-- **Theorem A2 (packing form).** For feasible packings of the two copies,
`w(P') + w(P'') ≤ 2·ν_w(G) + D₂^w(H[X])` with `X` their image multiset. -/
theorem mixed_copy_integral (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V)
    (huv : ¬ G.Adj u v) (gainOf : ℕ → ℕ)
    (P' : Finset (mixedCS (copyGraph G v u)).O) (P'' : Finset (mixedCS (copyGraph G u v)).O) :
    packGain _ gainOf P' + packGain _ gainOf P'' ≤
      2 * wNu (mixedCS G) (mixedWeight G gainOf) +
        wDq (mixedCS G) (mixedWeight G gainOf)
          (imageMultiset G v u huv (fun h => huv h.symm) P' P'') 2 := by
  have h := transfer_q_weighted (mixedCS G) (mixedWeight G gainOf)
    (imageMultiset G v u huv (fun h => huv h.symm) P' P'') 2 (by norm_num)
  rwa [wMultSize_imageMultiset] at h

/-- A maximum-weight feasible packing exists. -/
theorem exists_wNu_witness (C : ConflictSystem) (w : C.O → ℕ) :
    ∃ P : Finset C.O, CSFeasible C P ∧ (∑ o ∈ P, w o) = wNu C w := by
  classical
  have hne : (Finset.univ.filter (fun P : Finset C.O => CSFeasible C P)).Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro a ha; exact absurd ha (Finset.notMem_empty a)
  obtain ⟨P, hP, hmax⟩ := Finset.exists_mem_eq_sup _ hne (fun S : Finset C.O => ∑ o ∈ S, w o)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP
  refine ⟨P, hP, ?_⟩
  unfold wNu
  exact hmax.symm

/-- **Theorem A2.** `W(G_{v→u}) + W(G_{u→v}) ≤ 2·W(G) + D₂^w(H[X])` for the image multiset `X` of a
pair of optimal packings (`W` = weighted packing number `ν_w` of the mixed system). -/
theorem mixed_copy_integral_opt (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V)
    (huv : ¬ G.Adj u v) (gainOf : ℕ → ℕ) :
    ∃ X : (mixedCS G).O → ℕ,
      wMultSize (mixedCS G) (mixedWeight G gainOf) X =
        wNu (mixedCS (copyGraph G v u)) (mixedWeight _ gainOf) +
          wNu (mixedCS (copyGraph G u v)) (mixedWeight _ gainOf) ∧
      wNu (mixedCS (copyGraph G v u)) (mixedWeight _ gainOf) +
          wNu (mixedCS (copyGraph G u v)) (mixedWeight _ gainOf) ≤
        2 * wNu (mixedCS G) (mixedWeight G gainOf) + wDq (mixedCS G) (mixedWeight G gainOf) X 2 := by
  obtain ⟨P', _, hP'⟩ := exists_wNu_witness (mixedCS (copyGraph G v u)) (mixedWeight _ gainOf)
  obtain ⟨P'', _, hP''⟩ := exists_wNu_witness (mixedCS (copyGraph G u v)) (mixedWeight _ gainOf)
  have hg' : packGain _ gainOf P' = wNu (mixedCS (copyGraph G v u)) (mixedWeight _ gainOf) := hP'
  have hg'' : packGain _ gainOf P'' = wNu (mixedCS (copyGraph G u v)) (mixedWeight _ gainOf) := hP''
  refine ⟨imageMultiset G v u huv (fun h => huv h.symm) P' P'', ?_, ?_⟩
  · rw [wMultSize_imageMultiset, hg', hg'']
  · have := mixed_copy_integral G v u huv gainOf P' P''
    rwa [hg', hg''] at this

end PaperV
