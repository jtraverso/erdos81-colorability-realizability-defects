/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Remark C1r, layer 2: the conflict graph of the Steiner representation is a disjoint
union of `|L|` copies of `K₄`, hence `oct(H[X]) = 2·|L| = C(n,2)/3` — quadratic in `n`.

  * copies of `X` ↔ triangles lying in a block; two copies are adjacent iff they share an edge,
    iff they are two distinct faces of the SAME block;
  * lower bound: a 2-colourable remainder keeps ≤ 2 faces per block (three faces form a `K₃`);
  * upper bound: keep exactly two faces per block; the remainder is a perfect matching, 2-colourable.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.SteinerK4

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

namespace Steiner

variable {V : Type*} [Fintype V] [DecidableEq V] {L : Finset (Finset V)}

/-- The copies of the Steiner representation. -/
abbrev Cp (L : Finset (Finset V)) := Copies (triTop V) (steinerX L)

/-- Its conflict graph `H[X]`. -/
abbrev HX (L : Finset (Finset V)) := Hgraph (triTop V) (steinerX L)

theorem X_eq_one_of_copy (c : Cp L) : steinerX L c.1 = 1 := by
  have hpos : 0 < steinerX L c.1 := Fin.pos c.2
  have hle := steinerX_le_one (L := L) c.1
  omega

/-- Copies are determined by their triangle (multiplicities are ≤ 1). -/
theorem copy_ext {a b : Cp L} (h : a.1 = b.1) : a = b := by
  obtain ⟨t, i⟩ := a
  obtain ⟨t', j⟩ := b
  simp only at h
  subst h
  have h1 : steinerX L t = 1 := X_eq_one_of_copy (L := L) ⟨t, i⟩
  congr 1
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem copy_ext_iff {a b : Cp L} : a = b ↔ a.1.1 = b.1.1 :=
  ⟨fun h => h ▸ rfl, fun h => copy_ext (Subtype.ext h)⟩

/-- Adjacency in `H[X]`: distinct triangles sharing an edge. -/
theorem adj_iff {a b : Cp L} : (HX L).Adj a b ↔ a.1.1 ≠ b.1.1 ∧ 2 ≤ (a.1.1 ∩ b.1.1).card := by
  show (a ≠ b ∧ (a.1 = b.1 ∨ (triTop V).K a.1 b.1)) ↔ _
  constructor
  · rintro ⟨hne, h⟩
    rcases h with h | h
    · exact absurd (copy_ext h) hne
    · exact h
  · rintro ⟨hne, hsh⟩
    refine ⟨fun h => hne (congrArg (fun c : Cp L => c.1.1) h), Or.inr ⟨hne, hsh⟩⟩

/-- The block of a copy. -/
noncomputable def blockOfCopy (c : Cp L) : Finset V :=
  Classical.choose ((steinerX_eq_one_iff c.1).mp (X_eq_one_of_copy c))

theorem blockOfCopy_spec (c : Cp L) : blockOfCopy c ∈ L ∧ c.1.1 ⊆ blockOfCopy c :=
  Classical.choose_spec ((steinerX_eq_one_iff c.1).mp (X_eq_one_of_copy c))

theorem tri_card (c : Cp L) : c.1.1.card = 3 := (mem_cliqueFinset_top_iff c.1.1).mp c.1.2

theorem blockOfCopy_eq (hL : IsSteinerK4 L) (c : Cp L) {b : Finset V} (hb : b ∈ L)
    (hsub : c.1.1 ⊆ b) : blockOfCopy c = b :=
  hL.block_unique_of_tri (tri_card c) (blockOfCopy_spec c).1 hb (blockOfCopy_spec c).2 hsub

/-- Two distinct faces of one block are adjacent. -/
theorem adj_of_same_block (hL : IsSteinerK4 L) {a b : Cp L} {blk : Finset V} (hblk : blk ∈ L)
    (ha : a.1.1 ⊆ blk) (hb : b.1.1 ⊆ blk) (hne : a ≠ b) : (HX L).Adj a b := by
  rw [adj_iff]
  refine ⟨fun h => hne (copy_ext_iff.mpr h), ?_⟩
  have hu : (a.1.1 ∪ b.1.1).card ≤ 4 := by
    have := Finset.card_le_card (Finset.union_subset ha hb)
    rwa [hL.card_block blk hblk] at this
  have := Finset.card_union_add_card_inter a.1.1 b.1.1
  have h1 := tri_card a
  have h2 := tri_card b
  omega

/-- Adjacent copies lie in the same block. -/
theorem block_eq_of_adj (hL : IsSteinerK4 L) {a b : Cp L} (h : (HX L).Adj a b) :
    blockOfCopy a = blockOfCopy b := by
  rw [adj_iff] at h
  exact hL.same_block_of_share (blockOfCopy_spec a).1 (blockOfCopy_spec b).1
    (blockOfCopy_spec a).2 (blockOfCopy_spec b).2 h.2

/-- Copies (faces) of a block. -/
def copiesOf (L : Finset (Finset V)) (b : Finset V) : Finset (Cp L) :=
  Finset.univ.filter (fun c : Cp L => c.1.1 ⊆ b)

theorem mem_copiesOf {b : Finset V} {c : Cp L} : c ∈ copiesOf L b ↔ c.1.1 ⊆ b := by
  simp [copiesOf]

/-- A copy whose triangle lies in a block `b ∈ L`. -/
def mkCopy (L : Finset (Finset V)) (t : Finset V) (ht : t.card = 3) {b : Finset V} (hb : b ∈ L)
    (hsub : t ⊆ b) : Cp L :=
  ⟨⟨t, (mem_cliqueFinset_top_iff t).mpr ht⟩,
    ⟨0, by
      have : steinerX L ⟨t, (mem_cliqueFinset_top_iff t).mpr ht⟩ = 1 :=
        (steinerX_eq_one_iff _).mpr ⟨b, hb, hsub⟩
      rw [this]; exact Nat.one_pos⟩⟩

@[simp] theorem mkCopy_val (t : Finset V) (ht : t.card = 3) {b : Finset V} (hb : b ∈ L)
    (hsub : t ⊆ b) : (mkCopy L t ht hb hsub).1.1 = t := rfl

/-- Each block has exactly four copies (its faces). -/
theorem card_copiesOf (hL : IsSteinerK4 L) {b : Finset V} (hb : b ∈ L) :
    (copiesOf L b).card = 4 := by
  classical
  have hinj : Set.InjOn (fun c : Cp L => c.1.1) ((copiesOf L b : Finset (Cp L)) : Set (Cp L)) :=
    fun a _ c _ h => copy_ext_iff.mpr h
  rw [← Finset.card_image_of_injOn hinj]
  have himg : (copiesOf L b).image (fun c : Cp L => c.1.1) = b.powersetCard 3 := by
    ext s
    simp only [Finset.mem_image, mem_copiesOf, Finset.mem_powersetCard]
    constructor
    · rintro ⟨c, hc, rfl⟩; exact ⟨hc, tri_card c⟩
    · rintro ⟨hs, hcard⟩
      exact ⟨mkCopy L s hcard hb hs, hs, rfl⟩
  rw [himg, Finset.card_powersetCard, hL.card_block b hb]; rfl

theorem copiesOf_disjoint (hL : IsSteinerK4 L) :
    (L : Set (Finset V)).PairwiseDisjoint (copiesOf L) := by
  intro b hb b' hb' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro c hc hc'
  rw [mem_copiesOf] at hc hc'
  exact hne (hL.block_unique_of_tri (tri_card c) hb hb' hc hc')

/-- `|V(H[X])| = 4·|L|`. -/
theorem card_Cp (hL : IsSteinerK4 L) : Fintype.card (Cp L) = 4 * L.card := by
  rw [card_copies, multSize_steinerX hL]

/-! ### Lower bound -/

/-- A 2-colourable remainder keeps at most two faces of every block. -/
theorem two_le_deleted (hL : IsSteinerK4 L) (O : Finset (Cp L))
    (hcol : ((HX L).induce ((O : Set (Cp L))ᶜ)).Colorable 2) {b : Finset V} (hb : b ∈ L) :
    2 ≤ (O ∩ copiesOf L b).card := by
  classical
  by_contra hlt
  push_neg at hlt
  have hsurv : 2 < (copiesOf L b \ O).card := by
    have h1 := Finset.card_sdiff_add_card_inter (copiesOf L b) O
    rw [card_copiesOf hL hb] at h1
    rw [Finset.inter_comm] at hlt
    omega
  obtain ⟨c₁, c₂, c₃, hc₁, hc₂, hc₃, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp hsurv
  have mem : ∀ c ∈ copiesOf L b \ O, c ∈ ((O : Set (Cp L))ᶜ) := by
    intro c hc; rw [Finset.mem_sdiff] at hc; exact hc.2
  have sub : ∀ c ∈ copiesOf L b \ O, c.1.1 ⊆ b := by
    intro c hc; rw [Finset.mem_sdiff, mem_copiesOf] at hc; exact hc.1
  let col := hcol.some
  let v₁ : ↥((O : Set (Cp L))ᶜ) := ⟨c₁, mem c₁ hc₁⟩
  let v₂ : ↥((O : Set (Cp L))ᶜ) := ⟨c₂, mem c₂ hc₂⟩
  let v₃ : ↥((O : Set (Cp L))ᶜ) := ⟨c₃, mem c₃ hc₃⟩
  have a12 : (HX L).Adj c₁ c₂ := adj_of_same_block hL hb (sub c₁ hc₁) (sub c₂ hc₂) h12
  have a13 : (HX L).Adj c₁ c₃ := adj_of_same_block hL hb (sub c₁ hc₁) (sub c₃ hc₃) h13
  have a23 : (HX L).Adj c₂ c₃ := adj_of_same_block hL hb (sub c₂ hc₂) (sub c₃ hc₃) h23
  have n12 : col v₁ ≠ col v₂ := col.valid (SimpleGraph.induce_adj.mpr a12)
  have n13 : col v₁ ≠ col v₃ := col.valid (SimpleGraph.induce_adj.mpr a13)
  have n23 : col v₂ ≠ col v₃ := col.valid (SimpleGraph.induce_adj.mpr a23)
  -- three pairwise distinct values in `Fin 2`: impossible
  have := col v₁; have := col v₂; have := col v₃
  omega

theorem two_mul_card_le_defect (hL : IsSteinerK4 L) (O : Finset (Cp L))
    (hcol : ((HX L).induce ((O : Set (Cp L))ᶜ)).Colorable 2) : 2 * L.card ≤ O.card := by
  classical
  have hdisj : (L : Set (Finset V)).PairwiseDisjoint (fun b => O ∩ copiesOf L b) := by
    intro b hb b' hb' hne
    exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right (copiesOf_disjoint hL hb hb' hne))
  calc 2 * L.card = ∑ b ∈ L, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ b ∈ L, (O ∩ copiesOf L b).card := Finset.sum_le_sum (fun b hb => two_le_deleted hL O hcol hb)
    _ = (L.biUnion (fun b => O ∩ copiesOf L b)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ O.card := Finset.card_le_card (Finset.biUnion_subset.mpr (fun b _ => Finset.inter_subset_left))

theorem two_mul_card_le_oct (hL : IsSteinerK4 L) : 2 * L.card ≤ oct (HX L) := by
  unfold oct Dq
  apply le_csInf (defectSet_nonempty _ (by norm_num))
  rintro n ⟨O, hO, rfl⟩
  exact two_mul_card_le_defect hL O hO

/-! ### Upper bound -/

/-- Two distinct points of a block (noncomputable choice). -/
noncomputable def pick (hL : IsSteinerK4 L) (b : Finset V) (hb : b ∈ L) :
    {p : V × V // p.1 ∈ b ∧ p.2 ∈ b ∧ p.1 ≠ p.2} :=
  Classical.choice (by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by rw [hL.card_block b hb]; norm_num : 1 < b.card)
    exact ⟨⟨(x, y), hx, hy, hxy⟩⟩)

omit [Fintype V] in
theorem erase_card_three (hL : IsSteinerK4 L) {b : Finset V} (hb : b ∈ L) {x : V} (hx : x ∈ b) :
    (b.erase x).card = 3 := by
  rw [Finset.card_erase_of_mem hx, hL.card_block b hb]

/-- The face of `b` opposite to `x ∈ b`, as a copy. -/
noncomputable def face (hL : IsSteinerK4 L) (b : Finset V) (hb : b ∈ L) (x : V) (hx : x ∈ b) : Cp L :=
  mkCopy L (b.erase x) (erase_card_three hL hb hx) hb (Finset.erase_subset x b)

theorem face_val (hL : IsSteinerK4 L) (b : Finset V) (hb : b ∈ L) (x : V) (hx : x ∈ b) :
    (face hL b hb x hx).1.1 = b.erase x := rfl

/-- The first kept face of every block. -/
noncomputable def S₁ (hL : IsSteinerK4 L) : Finset (Cp L) :=
  L.attach.image (fun b => face hL b.1 b.2 (pick hL b.1 b.2).1.1 (pick hL b.1 b.2).2.1)

/-- The second kept face of every block. -/
noncomputable def S₂ (hL : IsSteinerK4 L) : Finset (Cp L) :=
  L.attach.image (fun b => face hL b.1 b.2 (pick hL b.1 b.2).1.2 (pick hL b.1 b.2).2.2.1)

/-- A face of `b` determines `b`. -/
theorem block_of_face (hL : IsSteinerK4 L) {b b' : Finset V} (hb : b ∈ L) (hb' : b' ∈ L)
    {x x' : V} (hx : x ∈ b) (hx' : x' ∈ b') (h : b.erase x = b'.erase x') : b = b' :=
  hL.block_unique_of_tri (erase_card_three hL hb hx) hb hb' (Finset.erase_subset x b)
    (h ▸ Finset.erase_subset x' b')

theorem erase_inj_of_mem {b : Finset V} {x x' : V} (hx : x ∈ b) (hx' : x' ∈ b)
    (h : b.erase x = b.erase x') : x = x' := by
  by_contra hne
  have : x ∈ b.erase x' := Finset.mem_erase.mpr ⟨hne, hx⟩
  rw [← h] at this
  exact (Finset.mem_erase.mp this).1 rfl

theorem card_S₁ (hL : IsSteinerK4 L) : (S₁ hL).card = L.card := by
  unfold S₁
  rw [Finset.card_image_of_injective, Finset.card_attach]
  intro b b' h
  have h' := congrArg (fun c : Cp L => c.1.1) h
  simp only [face_val] at h'
  exact Subtype.ext (block_of_face hL b.2 b'.2 (pick hL b.1 b.2).2.1 (pick hL b'.1 b'.2).2.1 h')

theorem card_S₂ (hL : IsSteinerK4 L) : (S₂ hL).card = L.card := by
  unfold S₂
  rw [Finset.card_image_of_injective, Finset.card_attach]
  intro b b' h
  have h' := congrArg (fun c : Cp L => c.1.1) h
  simp only [face_val] at h'
  exact Subtype.ext (block_of_face hL b.2 b'.2 (pick hL b.1 b.2).2.2.1 (pick hL b'.1 b'.2).2.2.1 h')

theorem disjoint_S₁_S₂ (hL : IsSteinerK4 L) : Disjoint (S₁ hL) (S₂ hL) := by
  rw [Finset.disjoint_left]
  intro c h1 h2
  unfold S₁ at h1; unfold S₂ at h2
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨b', _, h⟩ := Finset.mem_image.mp h2
  have h' := congrArg (fun c : Cp L => c.1.1) h
  simp only [face_val] at h'
  have hbb : b'.1 = b.1 := block_of_face hL b'.2 b.2 (pick hL b'.1 b'.2).2.2.1 (pick hL b.1 b.2).2.1 h'
  have hb : b' = b := Subtype.ext hbb
  subst hb
  have := erase_inj_of_mem (pick hL b'.1 b'.2).2.2.1 (pick hL b'.1 b'.2).2.1 h'
  exact (pick hL b'.1 b'.2).2.2.2 this.symm

/-- Members of `S₁ ∪ S₂` from the same block are equal or are the two chosen faces. -/
theorem mem_S₁_block (hL : IsSteinerK4 L) {c : Cp L} (h : c ∈ S₁ hL) :
    ∃ b : {b // b ∈ L}, c = face hL b.1 b.2 (pick hL b.1 b.2).1.1 (pick hL b.1 b.2).2.1 := by
  unfold S₁ at h
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
  exact ⟨b, rfl⟩

theorem mem_S₂_block (hL : IsSteinerK4 L) {c : Cp L} (h : c ∈ S₂ hL) :
    ∃ b : {b // b ∈ L}, c = face hL b.1 b.2 (pick hL b.1 b.2).1.2 (pick hL b.1 b.2).2.2.1 := by
  unfold S₂ at h
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
  exact ⟨b, rfl⟩

theorem blockOfCopy_face (hL : IsSteinerK4 L) (b : Finset V) (hb : b ∈ L) (x : V) (hx : x ∈ b) :
    blockOfCopy (face hL b hb x hx) = b :=
  blockOfCopy_eq hL _ hb (by rw [face_val]; exact Finset.erase_subset x b)

/-- No two distinct members of `S₁` are adjacent (they lie in different blocks). -/
theorem not_adj_S₁ (hL : IsSteinerK4 L) {a c : Cp L} (ha : a ∈ S₁ hL) (hc : c ∈ S₁ hL)
    (h : (HX L).Adj a c) : False := by
  obtain ⟨b, rfl⟩ := mem_S₁_block hL ha
  obtain ⟨b', rfl⟩ := mem_S₁_block hL hc
  have hblk := block_eq_of_adj hL h
  rw [blockOfCopy_face, blockOfCopy_face] at hblk
  have : b = b' := Subtype.ext hblk
  subst this
  exact (HX L).irrefl h

theorem not_adj_S₂ (hL : IsSteinerK4 L) {a c : Cp L} (ha : a ∈ S₂ hL) (hc : c ∈ S₂ hL)
    (h : (HX L).Adj a c) : False := by
  obtain ⟨b, rfl⟩ := mem_S₂_block hL ha
  obtain ⟨b', rfl⟩ := mem_S₂_block hL hc
  have hblk := block_eq_of_adj hL h
  rw [blockOfCopy_face, blockOfCopy_face] at hblk
  have : b = b' := Subtype.ext hblk
  subst this
  exact (HX L).irrefl h

/-- The deletion set: everything except the two kept faces per block. -/
noncomputable def delSet (hL : IsSteinerK4 L) : Finset (Cp L) := Finset.univ \ (S₁ hL ∪ S₂ hL)

theorem card_delSet (hL : IsSteinerK4 L) : (delSet hL).card = 2 * L.card := by
  unfold delSet
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, card_Cp hL,
    Finset.card_union_of_disjoint (disjoint_S₁_S₂ hL), card_S₁, card_S₂]
  omega

/-- The remainder is 2-colourable: colour `S₁` with `0` and `S₂` with `1`. -/
theorem delSet_colorable (hL : IsSteinerK4 L) :
    ((HX L).induce ((delSet hL : Set (Cp L))ᶜ)).Colorable 2 := by
  classical
  have hmem : ∀ v : ↥((delSet hL : Set (Cp L))ᶜ), v.1 ∈ S₁ hL ∨ v.1 ∈ S₂ hL := by
    intro v
    have hv := v.2
    simp only [delSet, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ,
      true_and, not_not, Finset.mem_union] at hv
    exact hv
  refine ⟨SimpleGraph.Coloring.mk (fun v => if v.1 ∈ S₁ hL then (0 : Fin 2) else 1) ?_⟩
  intro v w hvw heq
  have hadj : (HX L).Adj v.1 w.1 := SimpleGraph.induce_adj.mp hvw
  by_cases hv : v.1 ∈ S₁ hL <;> by_cases hw : w.1 ∈ S₁ hL
  · exact not_adj_S₁ hL hv hw hadj
  · simp [hv, hw] at heq
  · simp [hv, hw] at heq
  · have hv2 := (hmem v).resolve_left hv
    have hw2 := (hmem w).resolve_left hw
    exact not_adj_S₂ hL hv2 hw2 hadj

theorem oct_le_two_mul_card (hL : IsSteinerK4 L) : oct (HX L) ≤ 2 * L.card := by
  unfold oct Dq
  rw [← card_delSet hL]
  exact Nat.sInf_le ⟨delSet hL, delSet_colorable hL, rfl⟩

/-- **`oct(H[X]) = 2·|L|`.** -/
theorem oct_steinerX (hL : IsSteinerK4 L) : oct (HX L) = 2 * L.card :=
  le_antisymm (oct_le_two_mul_card hL) (two_mul_card_le_oct hL)

/-- **Remark C1r, abstract form.** For a Steiner system `S(2,4,n)` on `n` points, the half-integral
representation `X` (weight ½ on each face of each block) is a load-2 multiset attaining the
fractional bound `|E|/3`, and its conflict graph has `oct(H[X]) = C(n,2)/3`, i.e.
`3·oct(H[X]) = n(n−1)/2` — quadratic in `n`. -/
theorem quadratic_defect (hL : IsSteinerK4 L) :
    IsQMultiset (triTop V) (steinerX L) 2 ∧
    (∀ e ∈ (Finset.univ : Finset V).powersetCard 2, edgeLoad (steinerX L) e ≤ 2) ∧
    3 * multSize (triTop V) (steinerX L) = 2 * (Fintype.card V).choose 2 ∧
    3 * oct (HX L) = (Fintype.card V).choose 2 := by
  refine ⟨steinerX_isQMultiset, steinerX_load_le hL, ?_, ?_⟩
  · rw [steinerX_optimal hL, Finset.card_univ]
  · rw [oct_steinerX hL, ← Finset.card_univ, ← card_blocks hL]; ring

end Steiner

end PaperV
