/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Remark C1r, layer 1: a Steiner system S(2,4,n) on the complete graph gives a
half-integral triangle representation `X` that is load-optimal.

`IsSteinerK4 L`: the blocks `b ∈ L` are 4-sets and every pair of distinct vertices lies in exactly
one block. The complete graph `⊤` on `V` is then edge-decomposed into the cliques `b`.
`steinerX L`: the 1-multiset of all triangles contained in a block (the 4 faces of every `K₄`);
this is the `r = 2` scaling of the fractional packing "weight ½ on each face".

  * `multSize_steinerX`     : |X| = 4·|L|;
  * `card_blocks`           : 6·|L| = C(n,2)  (so |L| = n(n−1)/12);
  * `load_steinerX`         : every edge lies in exactly two triangles of `X` (load 2);
  * `load_two_bound`        : ANY multiset with edge-load ≤ 2 has 3·|Y| ≤ 2·C(n,2);
  * `steinerX_optimal`      : 3·|X| = 2·C(n,2) — `X` attains the bound, i.e. `x = X/2` is an
                              optimal (half-integral) fractional triangle packing.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.Copy

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.Tauto

@[expose] public section

open SimpleGraph Finset

namespace PaperV

namespace Steiner

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A Steiner system `S(2,4,|V|)`: 4-element blocks, every pair of distinct points in exactly one. -/
structure IsSteinerK4 (L : Finset (Finset V)) : Prop where
  card_block : ∀ b ∈ L, b.card = 4
  exists_block : ∀ x y : V, x ≠ y → ∃ b ∈ L, x ∈ b ∧ y ∈ b
  unique_block : ∀ b ∈ L, ∀ b' ∈ L, ∀ x y : V, x ≠ y → x ∈ b → y ∈ b → x ∈ b' → y ∈ b' → b = b'

variable {L : Finset (Finset V)}

/-- Two blocks sharing two points coincide (set form). -/
theorem IsSteinerK4.eq_of_two_le_inter (hL : IsSteinerK4 L) {b b' : Finset V} (hb : b ∈ L)
    (hb' : b' ∈ L) {s : Finset V} (hs : 2 ≤ s.card) (h1 : s ⊆ b) (h2 : s ⊆ b') : b = b' := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
  exact hL.unique_block b hb b' hb' x y hxy (h1 hx) (h1 hy) (h2 hx) (h2 hy)

/-- A 3-set lies in at most one block. -/
theorem IsSteinerK4.block_unique_of_tri (hL : IsSteinerK4 L) {t b b' : Finset V} (ht : t.card = 3)
    (hb : b ∈ L) (hb' : b' ∈ L) (h1 : t ⊆ b) (h2 : t ⊆ b') : b = b' :=
  hL.eq_of_two_le_inter hb hb' (by omega) h1 h2

/-- Two 3-sets sharing ≥ 2 points and lying in blocks lie in the same block. -/
theorem IsSteinerK4.same_block_of_share (hL : IsSteinerK4 L) {t t' b b' : Finset V}
    (hb : b ∈ L) (hb' : b' ∈ L) (h1 : t ⊆ b) (h2 : t' ⊆ b') (hsh : 2 ≤ (t ∩ t').card) : b = b' :=
  hL.eq_of_two_le_inter hb hb' hsh (Finset.inter_subset_left.trans h1)
    (Finset.inter_subset_right.trans h2)

/-! ### Counting blocks: `6·|L| = C(n,2)` -/

/-- The block containing a pair (noncomputable choice). -/
noncomputable def blockOf (hL : IsSteinerK4 L) (x y : V) (hxy : x ≠ y) : Finset V :=
  Classical.choose (hL.exists_block x y hxy)

theorem blockOf_spec (hL : IsSteinerK4 L) (x y : V) (hxy : x ≠ y) :
    blockOf hL x y hxy ∈ L ∧ x ∈ blockOf hL x y hxy ∧ y ∈ blockOf hL x y hxy :=
  Classical.choose_spec (hL.exists_block x y hxy)

/-- Every 2-set lies in exactly one block: the 2-subsets of `V` are partitioned by the blocks. -/
theorem card_blocks (hL : IsSteinerK4 L) : 6 * L.card = (Finset.univ : Finset V).card.choose 2 := by
  classical
  -- pairs = ⋃_{b ∈ L} (2-subsets of b), disjoint union
  have hcover : (Finset.univ : Finset V).powersetCard 2 = L.biUnion (fun b => b.powersetCard 2) := by
    ext s
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hs
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
      obtain ⟨b, hb, hxb, hyb⟩ := hL.exists_block x y hxy
      refine ⟨b, hb, ?_, hs⟩
      have : s = {x, y} := by
        symm; apply Finset.eq_of_subset_of_card_le
        · intro z hz; rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        · rw [Finset.card_pair hxy]; omega
      rw [this]; intro z hz; rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · rintro ⟨b, _, _, hs⟩; exact hs
  have hdisj : (L : Set (Finset V)).PairwiseDisjoint (fun b => b.powersetCard 2) := by
    intro b hb b' hb' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro s hs hs'
    rw [Finset.mem_powersetCard] at hs hs'
    exact hne (hL.eq_of_two_le_inter hb hb' hs.2.ge hs.1 hs'.1)
  have h1 := Finset.card_powersetCard 2 (Finset.univ : Finset V)
  rw [hcover, Finset.card_biUnion hdisj] at h1
  have h2 : ∀ b ∈ L, (b.powersetCard 2).card = 6 := by
    intro b hb; rw [Finset.card_powersetCard, hL.card_block b hb]; rfl
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm] at h1
  exact h1

/-! ### The half-integral representation `X` -/

/-- The complete graph's triangle conflict system. -/
abbrev triTop (V : Type*) [Fintype V] [DecidableEq V] : ConflictSystem := triCS (⊤ : SimpleGraph V)

/-- `X t = 1` iff the triangle `t` lies in a block. -/
def steinerX (L : Finset (Finset V)) : (triTop V).O → ℕ :=
  fun t => if ∃ b ∈ L, t.1 ⊆ b then 1 else 0

theorem steinerX_le_one (t : (triTop V).O) : steinerX L t ≤ 1 := by
  unfold steinerX; split_ifs <;> omega

theorem steinerX_eq_one_iff (t : (triTop V).O) : steinerX L t = 1 ↔ ∃ b ∈ L, t.1 ⊆ b := by
  unfold steinerX; split_ifs with h <;> simp [h]

theorem steinerX_isQMultiset : IsQMultiset (triTop V) (steinerX L) 2 :=
  fun t => (steinerX_le_one t).trans (by norm_num)

/-- Every 3-set is a triangle of `⊤`. -/
theorem mem_cliqueFinset_top_iff (t : Finset V) : t ∈ (⊤ : SimpleGraph V).cliqueFinset 3 ↔ t.card = 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; refine ⟨?_, h⟩; intro x _ y _ hxy; exact hxy

/-- `|X| = 4·|L|`: each block contributes its four faces, and faces determine their block. -/
theorem multSize_steinerX (hL : IsSteinerK4 L) : multSize (triTop V) (steinerX L) = 4 * L.card := by
  classical
  -- |X| = number of triangles t with X t = 1 = number of 3-sets contained in some block
  have hsum : multSize (triTop V) (steinerX L) =
      (Finset.univ.filter (fun t : (triTop V).O => steinerX L t = 1)).card := by
    unfold multSize
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _
    have := steinerX_le_one (L := L) t
    split_ifs with h <;> omega
  rw [hsum]
  -- map to underlying 3-sets
  have hinj : Set.InjOn (fun t : (triTop V).O => t.1)
      ((Finset.univ.filter (fun t : (triTop V).O => steinerX L t = 1)) : Set (triTop V).O) :=
    fun a _ b _ h => Subtype.ext h
  rw [← Finset.card_image_of_injOn hinj]
  have himg : (Finset.univ.filter (fun t : (triTop V).O => steinerX L t = 1)).image
      (fun t : (triTop V).O => t.1) = L.biUnion (fun b => b.powersetCard 3) := by
    ext s
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨b, hb, hsub⟩ := (steinerX_eq_one_iff t).mp ht
      exact ⟨b, hb, hsub, (mem_cliqueFinset_top_iff t.1).mp t.2⟩
    · rintro ⟨b, hb, hsub, hcard⟩
      refine ⟨⟨s, (mem_cliqueFinset_top_iff s).mpr hcard⟩, ?_, rfl⟩
      exact (steinerX_eq_one_iff _).mpr ⟨b, hb, hsub⟩
  rw [himg]
  have hdisj : (L : Set (Finset V)).PairwiseDisjoint (fun b => b.powersetCard 3) := by
    intro b hb b' hb' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro s hs hs'
    rw [Finset.mem_powersetCard] at hs hs'
    exact hne (hL.block_unique_of_tri hs.2 hb hb' hs.1 hs'.1)
  rw [Finset.card_biUnion hdisj]
  have h4 : ∀ b ∈ L, (b.powersetCard 3).card = 4 := by
    intro b hb; rw [Finset.card_powersetCard, hL.card_block b hb]; rfl
  rw [Finset.sum_congr rfl h4, Finset.sum_const, smul_eq_mul, mul_comm]

/-! ### Edge load -/

/-- Edge load of a multiset `Y` at a 2-set `e`: total multiplicity of the triangles containing `e`. -/
def edgeLoad (Y : (triTop V).O → ℕ) (e : Finset V) : ℕ :=
  ∑ t ∈ Finset.univ.filter (fun t : (triTop V).O => e ⊆ t.1), Y t

/-- **Load-2 bound.** If every edge has load ≤ 2 then `3·|Y| ≤ 2·C(n,2)`: the (half-integral)
fractional packing value cannot exceed `|E|/3`. -/
theorem load_two_bound (Y : (triTop V).O → ℕ)
    (hload : ∀ e ∈ (Finset.univ : Finset V).powersetCard 2, edgeLoad Y e ≤ 2) :
    3 * multSize (triTop V) Y ≤ 2 * (Finset.univ : Finset V).card.choose 2 := by
  classical
  -- double count: Σ_e load(e) = Σ_t Y t · #(2-subsets of t) = 3 |Y|
  have hdc : ∑ e ∈ (Finset.univ : Finset V).powersetCard 2, edgeLoad Y e =
      3 * multSize (triTop V) Y := by
    unfold edgeLoad multSize
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun t : (triTop V).O => t.1.powersetCard 2)]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard,
        (mem_cliqueFinset_top_iff t.1).mp t.2]
      rfl
    · intro e t
      simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.mem_filter,
        Finset.mem_univ]
      tauto
  rw [← hdc]
  calc ∑ e ∈ (Finset.univ : Finset V).powersetCard 2, edgeLoad Y e
      ≤ ∑ _e ∈ (Finset.univ : Finset V).powersetCard 2, 2 := Finset.sum_le_sum hload
    _ = 2 * (Finset.univ : Finset V).card.choose 2 := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, mul_comm]

/-- The triangles of `X` through an edge `e` are exactly the two faces of its block through `e`. -/
theorem load_steinerX (hL : IsSteinerK4 L) (e : Finset V) (he : e.card = 2) :
    edgeLoad (steinerX L) e = 2 := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < e.card)
  obtain ⟨b, hb, hxb, hyb⟩ := hL.exists_block x y hxy
  have heb : e ⊆ b := by
    have : e = {x, y} := by
      symm; apply Finset.eq_of_subset_of_card_le
      · intro z hz; rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      · rw [Finset.card_pair hxy]; omega
    rw [this]; intro z hz; rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  -- the triangles of X containing e are the 3-sets t with e ⊆ t ⊆ b, i.e. e ∪ {z}, z ∈ b \ e
  unfold edgeLoad
  have hsum : ∑ t ∈ Finset.univ.filter (fun t : (triTop V).O => e ⊆ t.1), steinerX L t =
      (Finset.univ.filter (fun t : (triTop V).O => e ⊆ t.1 ∧ t.1 ⊆ b)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h1 : e ⊆ t.1
    · simp only [h1, true_and, if_true]
      by_cases h2 : t.1 ⊆ b
      · rw [if_pos h2]; exact (steinerX_eq_one_iff t).mpr ⟨b, hb, h2⟩
      · rw [if_neg h2]
        unfold steinerX
        rw [if_neg]
        rintro ⟨b', hb', hsub⟩
        -- t ⊆ b' and e ⊆ t ⊆ b', e ⊆ b ⇒ b = b'
        have : b = b' := hL.eq_of_two_le_inter hb hb' (by omega : 2 ≤ e.card) heb (h1.trans hsub)
        exact h2 (this ▸ hsub)
    · simp [h1]
  rw [hsum]
  -- bijection with b \ e via t ↦ t \ e (a singleton) ... count directly: image of val = {t | e ⊆ t ⊆ b, |t|=3}
  have hinj : Set.InjOn (fun t : (triTop V).O => t.1)
      ((Finset.univ.filter (fun t : (triTop V).O => e ⊆ t.1 ∧ t.1 ⊆ b)) : Set (triTop V).O) :=
    fun a _ c _ h => Subtype.ext h
  rw [← Finset.card_image_of_injOn hinj]
  have himg : (Finset.univ.filter (fun t : (triTop V).O => e ⊆ t.1 ∧ t.1 ⊆ b)).image
      (fun t : (triTop V).O => t.1) = (b \ e).image (fun z => insert z e) := by
    ext s
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      have hc := (mem_cliqueFinset_top_iff t.1).mp t.2
      have hdiff : (t.1 \ e).card = 1 := by rw [Finset.card_sdiff_of_subset h1, hc, he]
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hdiff
      have hzmem : z ∈ t.1 \ e := hz ▸ Finset.mem_singleton_self z
      rw [Finset.mem_sdiff] at hzmem
      refine ⟨z, ⟨h2 hzmem.1, hzmem.2⟩, ?_⟩
      -- t = insert z e
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        rw [Finset.mem_insert] at hw
        rcases hw with rfl | hw
        · exact hzmem.1
        · exact h1 hw
      · rw [Finset.card_insert_of_notMem hzmem.2, he, hc]
    · rintro ⟨z, ⟨hzb, hze⟩, rfl⟩
      have hc : (insert z e).card = 3 := by rw [Finset.card_insert_of_notMem hze, he]
      refine ⟨⟨insert z e, (mem_cliqueFinset_top_iff _).mpr hc⟩, ⟨Finset.subset_insert z e, ?_⟩, rfl⟩
      intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · exact hzb
      · exact heb hw
  rw [himg, Finset.card_image_of_injOn, Finset.card_sdiff_of_subset heb, hL.card_block b hb, he]
  intro z hz z' hz' h
  simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe] at hz hz'
  have h' : insert z e = insert z' e := h
  have : z ∈ insert z' e := by rw [← h']; exact Finset.mem_insert_self z e
  rw [Finset.mem_insert] at this
  rcases this with h' | h'
  · exact h'
  · exact absurd h' hz.2

/-- The load hypothesis of `load_two_bound` holds for `X`. -/
theorem steinerX_load_le (hL : IsSteinerK4 L) :
    ∀ e ∈ (Finset.univ : Finset V).powersetCard 2, edgeLoad (steinerX L) e ≤ 2 := by
  intro e he
  rw [Finset.mem_powersetCard] at he
  rw [load_steinerX hL e he.2]

/-- **Optimality.** `3·|X| = 2·C(n,2)`: `X` attains the load-2 bound, so `x = X/2` is an optimal
fractional triangle packing of `K_n` (value `|E|/3`). -/
theorem steinerX_optimal (hL : IsSteinerK4 L) :
    3 * multSize (triTop V) (steinerX L) = 2 * (Finset.univ : Finset V).card.choose 2 := by
  rw [multSize_steinerX hL, ← card_blocks hL]; ring

end Steiner

end PaperV
