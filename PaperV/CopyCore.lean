/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV/V — §4.1 copy inequalities, CORE (split of the former monolithic `Copy.lean`, 2026-09-14):
copy graph `G_{v→u}`, the triangle conflict system `triCS`, `ν₃`, the total map `copyMap`, Theorem 4.2
(`copy_integral`) and the edge-load lemma (`copy_integral_edgeLoad_le_two`). Statements and proofs are
unchanged; only the file boundaries and the visibility of helper lemmas (now public, reusable) changed.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.ConflictGraph
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum

@[expose] public section
open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

def copyGraph (G : SimpleGraph V) (v u : V) : SimpleGraph V where
  Adj a b :=
    (a ≠ v ∧ b ≠ v ∧ G.Adj a b) ∨
    (a = v ∧ b ≠ v ∧ G.Adj u b) ∨
    (b = v ∧ a ≠ v ∧ G.Adj u a)
  symm := by
    constructor
    rintro a b (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h2, h1, h3.symm⟩
    · exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
    · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
  loopless := by
    refine ⟨fun a h => ?_⟩
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · exact h3.ne rfl
    · exact h2 h1
    · exact h2 h1

instance (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) :
    DecidableRel (copyGraph G v u).Adj := by
  intro a b; unfold copyGraph; infer_instance

/-- The triangle conflict system of `G`: objects are the 3-cliques (triangles); two distinct
triangles conflict iff they share an edge (`|t₁ ∩ t₂| ≥ 2`). -/
abbrev triCS (G : SimpleGraph V) [DecidableRel G.Adj] : ConflictSystem where
  O := {t : Finset V // t ∈ G.cliqueFinset 3}
  K t₁ t₂ := t₁.1 ≠ t₂.1 ∧ 2 ≤ (t₁.1 ∩ t₂.1).card
  Ksymm := by
    rintro a b ⟨h1, h2⟩
    exact ⟨h1.symm, by rwa [Finset.inter_comm]⟩
  Kirrefl := by rintro a ⟨h1, _⟩; exact h1 rfl
  decK := by intro a b; dsimp only; infer_instance

/-- The (integral) triangle packing number `ν₃(G) = ν(triCS G)`: the maximum number of
pairwise edge-disjoint triangles. -/
noncomputable def nu3 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := nu (triCS G)

/-- The copy relabelling on a triangle: replace `v` by `u` (identity if `v ∉ t`). This is the
total map `φ'` of §4.1. -/
def copyMap (v u : V) (t : Finset V) : Finset V := t.image (fun x => if x = v then u else x)

/-- Well-definedness of the total map: a triangle of `G_{v→u}` is sent to a triangle of `G`.
(A `v`-triangle `(v,x,y)` maps to `(u,x,y)`, a triangle of `G` because `v` is joined to
`N_G(u)`; a triangle avoiding `v` is a triangle of `G` unchanged.) -/
theorem copyMap_mem_triangles (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V)
    (huv : ¬ G.Adj u v) (t : Finset V) (ht : t ∈ (copyGraph G v u).cliqueFinset 3) :
    copyMap v u t ∈ G.cliqueFinset 3 := by
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

lemma exists_max_feasible (C : ConflictSystem) :
    ∃ P : Finset C.O, CSFeasible C P ∧ P.card = nu C := by
  classical
  let F := Finset.univ.filter (fun P : Finset C.O => CSFeasible C P)
  have hF : F.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro a ha
    exact False.elim (Finset.notMem_empty a ha)
  obtain ⟨P, hPF, hsup⟩ := Finset.exists_mem_eq_sup F hF Finset.card
  refine ⟨P, (Finset.mem_filter.mp hPF).2, ?_⟩
  rw [nu]
  exact hsup.symm

lemma copyMap_injective_on_feasible
    (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v)
    (P : Finset (triCS (copyGraph G v u)).O)
    (hP : CSFeasible (triCS (copyGraph G v u)) P) :
    Set.InjOn (fun t : (triCS (copyGraph G v u)).O => copyMap v u t.1) P := by
  intro a ha b hb hab
  apply Subtype.ext
  by_contra hne
  apply hP ha hb
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

lemma card_copyMap_fibers
    (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v)
    (P : Finset (triCS (copyGraph G v u)).O) :
    P.card = ∑ t : (triCS G).O,
      (P.filter (fun s => copyMap v u s.1 = t.1)).card := by
  -- Define the function f : (triCS (copyGraph G v u)).O → (triCS G).O
  let f : (triCS (copyGraph G v u)).O → (triCS G).O := fun s =>
    ⟨copyMap v u s.1, copyMap_mem_triangles G v u huv s.1 s.2⟩
  -- Use the fact that summing fiber cardinalities equals total cardinality
  rw [← Finset.card_biUnion]
  · congr 1
    ext s
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hs
      exact ⟨f s, Finset.mem_univ _, hs, rfl⟩
    · intro ⟨x, _, hs, hx⟩
      exact hs
  · intro x _ y _ hxy
    rw [Function.onFun]
    rw [Finset.disjoint_left]
    simp only [Finset.mem_filter]
    intro s ⟨hsp, hpx⟩ ⟨hsq, hpy⟩
    exfalso
    apply hxy
    exact Subtype.ext (hpx.symm.trans hpy)

/-- **Theorem 4.2 (integral copy inequality).** There is a copy multiset `T₂` of triangles of
`G` (the image `φ'(P') ⊎ φ''(P'')` of maximum packings of the two copy graphs) with
`ν₃(G_{v→u}) + ν₃(G_{u→v}) ≤ 2·ν₃(G) + oct(H[T₂])`.

Proof route (cleaner than the manuscript's): the bound is `transfer_half` on the triangle
conflict system `triCS G` applied to `T₂`, together with `multSize T₂ = ν₃(G_{v→u})+ν₃(G_{u→v})`
(the total map is size-preserving and lands in triangles of `G`). The manuscript's edge-load
lemma is not needed for the inequality: twin-adjacency in `H[T₂]` already forces each colour
class to be a genuine triangle packing of `G` (via `indep_le_nu`). -/
theorem copy_integral (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v) :
    ∃ T₂ : (triCS G).O → ℕ,
      multSize (triCS G) T₂ = nu3 (copyGraph G v u) + nu3 (copyGraph G u v) ∧
      nu3 (copyGraph G v u) + nu3 (copyGraph G u v)
        ≤ 2 * nu3 G + oct (Hgraph (triCS G) T₂) := by
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
  exact ⟨T₂, hsize', hbound⟩

omit [Fintype V] in
/-- Membership in a copy image: `y ∈ φ(t)` iff `y` survives (`y∈t, y≠w`) or is the image of `w`. -/
lemma mem_copyMap (w z : V) (t : Finset V) (y : V) :
    y ∈ copyMap w z t ↔ (y ∈ t ∧ y ≠ w) ∨ (w ∈ t ∧ y = z) := by
  simp only [copyMap, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hfx⟩
    by_cases hxw : x = w
    · subst hxw; rw [if_pos rfl] at hfx; exact Or.inr ⟨hx, hfx.symm⟩
    · rw [if_neg hxw] at hfx; subst hfx; exact Or.inl ⟨hx, hxw⟩
  · rintro (⟨hy, hyw⟩ | ⟨hw, hyz⟩)
    · exact ⟨y, hy, by rw [if_neg hyw]⟩
    · exact ⟨w, hw, by rw [if_pos rfl, hyz]⟩

omit [Fintype V] in
/-- The copy image `φ(t) = t[w↦z]` never contains `w` (when `z ≠ w`). -/
lemma w_notMem_copyMap (w z : V) (hwz : z ≠ w) (t : Finset V) :
    w ∉ copyMap w z t := by
  rw [mem_copyMap]
  rintro (⟨_, h⟩ | ⟨_, h⟩)
  · exact h rfl
  · exact hwz h.symm

omit [Fintype V] in
/-- The trivial copy `w ↦ w` is the identity on triangles. -/
lemma copyMap_self (w : V) (t : Finset V) : copyMap w w t = t := by
  ext y; rw [mem_copyMap]
  constructor
  · rintro (⟨hy, _⟩ | ⟨hw, hyz⟩)
    · exact hy
    · rwa [hyz]
  · intro hy
    by_cases hyw : y = w
    · exact Or.inr ⟨hyw ▸ hy, hyw⟩
    · exact Or.inl ⟨hy, hyw⟩

/-- In a feasible packing, at most one triangle contains any given edge (two would conflict). -/
lemma feasible_edge_count_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (w z : V)
    (P : Finset (triCS (copyGraph G w z)).O)
    (hP : CSFeasible (triCS (copyGraph G w z)) P) (e' : Finset V) (he' : 2 ≤ e'.card) :
    (P.filter (fun s => e' ⊆ s.1)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  by_contra hne
  refine hP ha.1 hb.1 ⟨fun h => hne (Subtype.ext h), ?_⟩
  calc 2 ≤ e'.card := he'
    _ ≤ (a.1 ∩ b.1).card := Finset.card_le_card (Finset.subset_inter ha.2 hb.2)

/-- **H2 / general ≤ 2.** For a feasible packing `P` of the copy graph `copyGraph G w z`
(`z ≠ w`) and any 2-edge `e` with `w ∉ e`, at most two triangles of `P` have image ⊇ `e`
(their images split into those containing `e` and those built from `w`). -/
lemma copy_count_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj] (w z : V)
    (P : Finset (triCS (copyGraph G w z)).O)
    (hP : CSFeasible (triCS (copyGraph G w z)) P) (e : Finset V) (he : e.card = 2)
    (hwe : w ∉ e) :
    (P.filter (fun s => e ⊆ copyMap w z s.1)).card ≤ 2 := by
  classical
  have hsub : (P.filter (fun s => e ⊆ copyMap w z s.1))
      ⊆ (P.filter (fun s => e ⊆ s.1)) ∪ (P.filter (fun s => insert w (e.erase z) ⊆ s.1)) := by
    intro s hs
    simp only [Finset.mem_filter] at hs
    obtain ⟨hsP, hsub⟩ := hs
    rw [Finset.mem_union]
    by_cases hes : e ⊆ s.1
    · exact Or.inl (Finset.mem_filter.mpr ⟨hsP, hes⟩)
    · refine Or.inr (Finset.mem_filter.mpr ⟨hsP, ?_⟩)
      -- some y₀ ∈ e, y₀ ∉ s ⟹ w ∈ s ∧ y₀ = z
      obtain ⟨y₀, hy₀e, hy₀s⟩ := Finset.not_subset.mp hes
      have hy₀img : y₀ ∈ copyMap w z s.1 := hsub hy₀e
      rw [mem_copyMap] at hy₀img
      have hws : w ∈ s.1 ∧ y₀ = z := by
        rcases hy₀img with ⟨h1, _⟩ | h
        · exact absurd h1 hy₀s
        · exact h
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact hws.1
      · have hyz : y ≠ z := (Finset.mem_erase.mp hy).1
        have hye : y ∈ e := (Finset.mem_erase.mp hy).2
        have := hsub hye
        rw [mem_copyMap] at this
        rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact h1
        · exact absurd h2 hyz
  calc (P.filter (fun s => e ⊆ copyMap w z s.1)).card
      ≤ ((P.filter (fun s => e ⊆ s.1)) ∪ (P.filter (fun s => insert w (e.erase z) ⊆ s.1))).card :=
        Finset.card_le_card hsub
    _ ≤ (P.filter (fun s => e ⊆ s.1)).card + (P.filter (fun s => insert w (e.erase z) ⊆ s.1)).card :=
        Finset.card_union_le _ _
    _ ≤ 1 + 1 := by
        refine Nat.add_le_add (feasible_edge_count_le_one G w z P hP e he.ge) ?_
        refine feasible_edge_count_le_one G w z P hP _ ?_
        -- |insert w (e.erase z)| = 2 : w ∉ e ⊇ e.erase z, |e.erase z| = 1 (z ∈ e) ... ≥ 2 always here
        rw [Finset.card_insert_of_notMem (fun h => hwe (Finset.mem_of_mem_erase h))]
        have : 1 ≤ (e.erase z).card := by
          by_cases hze : z ∈ e
          · rw [Finset.card_erase_of_mem hze]; omega
          · rw [Finset.erase_eq_of_notMem hze]; omega
        omega
    _ = 2 := rfl

/-- Fibre reduction: the `e`-restricted sum of `φ'`-fibre cardinalities counts exactly the
`P`-triangles whose image contains `e`. -/
lemma edgeLoad_fibre_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v)
    (P : Finset (triCS (copyGraph G v u)).O) (e : Finset V) :
    (∑ t : (triCS G).O,
        if e ⊆ t.1 then (P.filter (fun s => copyMap v u s.1 = t.1)).card else 0)
      = (P.filter (fun s => e ⊆ copyMap v u s.1)).card := by
  classical
  have hbij : (P.filter (fun s => e ⊆ copyMap v u s.1))
      = ((univ.filter (fun t : (triCS G).O => e ⊆ t.1)).biUnion
          (fun t => P.filter (fun s => copyMap v u s.1 = t.1))) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hsP, hes⟩
      exact ⟨⟨copyMap v u s.1, copyMap_mem_triangles G v u huv s.1 s.2⟩, hes, hsP, rfl⟩
    · intro ⟨t, het, hsP, hst⟩
      exact ⟨hsP, by rw [hst]; exact het⟩
  rw [hbij, Finset.card_biUnion]
  · rw [← Finset.sum_filter]
  · intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    simp only [Finset.mem_filter]
    intro s ⟨_, hsx⟩ ⟨_, hsy⟩
    exact hxy (Subtype.ext (hsx.symm.trans hsy))

/-- **H1 / ≤ 1 when the copy-target is off the edge.** If neither `w` nor `z` is in `e`, then
`e ⊆ φ(s) ↔ e ⊆ s`, so at most one triangle of a feasible `P` qualifies. -/
lemma copy_count_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (w z : V)
    (P : Finset (triCS (copyGraph G w z)).O)
    (hP : CSFeasible (triCS (copyGraph G w z)) P) (e : Finset V) (he : e.card = 2)
    (hwe : w ∉ e) (hze : z ∉ e) :
    (P.filter (fun s => e ⊆ copyMap w z s.1)).card ≤ 1 := by
  have heq : (P.filter (fun s => e ⊆ copyMap w z s.1)) = P.filter (fun s => e ⊆ s.1) := by
    apply Finset.filter_congr
    intro s _
    constructor
    · intro h y hy
      have hy' := h hy
      rw [mem_copyMap] at hy'
      rcases hy' with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · exact absurd (h2 ▸ hy) hze
    · intro h y hy
      rw [mem_copyMap]
      exact Or.inl ⟨h hy, fun hyw => hwe (hyw ▸ hy)⟩
  rw [heq]; exact feasible_edge_count_le_one G w z P hP e he.ge

/-- Claim 4.1a: the two copied packings put total multiplicity at most two on every
edge of the original graph. -/
lemma copy_integral_edgeLoad_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v)
    (P' : Finset (triCS (copyGraph G v u)).O)
    (P'' : Finset (triCS (copyGraph G u v)).O)
    (hP' : CSFeasible (triCS (copyGraph G v u)) P')
    (hP'' : CSFeasible (triCS (copyGraph G u v)) P'') :
    let T₂ : (triCS G).O → ℕ := fun t =>
      (P'.filter (fun s => copyMap v u s.1 = t.1)).card +
      (P''.filter (fun s => copyMap u v s.1 = t.1)).card
    ∀ e : Finset V, e.card = 2 →
      (∑ t : (triCS G).O, if e ⊆ t.1 then T₂ t else 0) ≤ 2 := by
  intro T₂ e he
  have hvu : ¬ G.Adj v u := fun h => huv h.symm
  -- reduce the sum to two image-counts
  have hred : (∑ t : (triCS G).O, if e ⊆ t.1 then T₂ t else 0)
      = (P'.filter (fun s => e ⊆ copyMap v u s.1)).card
        + (P''.filter (fun s => e ⊆ copyMap u v s.1)).card := by
    rw [← edgeLoad_fibre_eq G v u huv P' e, ← edgeLoad_fibre_eq G u v hvu P'' e,
        ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : e ⊆ t.1 <;> simp [T₂, h]
  rw [hred]
  by_cases hve : v ∈ e
  · -- v ∈ e ⟹ P'-count = 0 (v ∉ φ'-image needs u ≠ v, which v∈e,u∉e forces; if u∈e both 0)
    by_cases huve : u = v
    · -- u = v : both maps are the identity, each count ≤ 1
      subst huve
      have h1 : (P'.filter (fun s => e ⊆ copyMap u u s.1)).card ≤ 1 := by
        simp only [copyMap_self]; exact feasible_edge_count_le_one G u u P' hP' e he.ge
      have h2 : (P''.filter (fun s => e ⊆ copyMap u u s.1)).card ≤ 1 := by
        simp only [copyMap_self]; exact feasible_edge_count_le_one G u u P'' hP'' e he.ge
      omega
    · -- u ≠ v : v ∈ e ⟹ P'-count = 0
      have hP'0 : (P'.filter (fun s => e ⊆ copyMap v u s.1)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro s _ hsub
        exact w_notMem_copyMap v u huve s.1 (hsub hve)
      have hP''2 : (P''.filter (fun s => e ⊆ copyMap u v s.1)).card ≤ 2 := by
        by_cases hue : u ∈ e
        · rw [Finset.card_eq_zero.mpr]
          · norm_num
          · rw [Finset.filter_eq_empty_iff]
            intro s _ hsub
            exact w_notMem_copyMap u v (fun h => huve h.symm) s.1 (hsub hue)
        · exact copy_count_le_two G u v P'' hP'' e he hue
      omega
  · -- v ∉ e
    by_cases hue : u ∈ e
    · -- u ∈ e ⟹ P''-count = 0
      have huve : u ≠ v := fun h => hve (h ▸ hue)
      have hP''0 : (P''.filter (fun s => e ⊆ copyMap u v s.1)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro s _ hsub
        exact w_notMem_copyMap u v (fun h => huve h.symm) s.1 (hsub hue)
      have hP'2 : (P'.filter (fun s => e ⊆ copyMap v u s.1)).card ≤ 2 :=
        copy_count_le_two G v u P' hP' e he hve
      omega
    · -- neither u nor v in e : both ≤ 1
      have h1 : (P'.filter (fun s => e ⊆ copyMap v u s.1)).card ≤ 1 :=
        copy_count_le_one G v u P' hP' e he hve hue
      have h2 : (P''.filter (fun s => e ⊆ copyMap u v s.1)).card ≤ 1 :=
        copy_count_le_one G u v P'' hP'' e he hue hve
      omega


end PaperV
