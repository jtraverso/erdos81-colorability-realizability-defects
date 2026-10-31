/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Remark C1r, layer 3: existence of Steiner systems `S(2,4,4^d)` via affine geometry.

Points = `Fin d → F` for a finite field `F` with `|F| = 4`; blocks = affine lines
`{p + t•(q − p) : t ∈ F}`. Any two distinct points lie on exactly one line, and every line has
`|F| = 4` points. Instantiated with `F = GaloisField 2 2` this gives, for every `d`, an `n = 4^d`
point instance of `quadratic_defect`: an optimal half-integral triangle representation of `K_n`
whose conflict graph has `oct = n(n−1)/6`.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.SteinerK4Oct
public import Mathlib.FieldTheory.Finite.GaloisField

import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

@[expose] public section

open Finset

namespace PaperV

namespace Steiner

section Affine

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}

/-- Affine points. -/
abbrev Pt (F : Type*) (d : ℕ) := Fin d → F

/-- The affine line through `p` and `q`. -/
def line (p q : Pt F d) : Finset (Pt F d) := Finset.univ.image (fun t : F => p + t • (q - p))

theorem mem_line_iff {p q x : Pt F d} : x ∈ line p q ↔ ∃ t : F, p + t • (q - p) = x := by
  simp [line]

theorem left_mem_line (p q : Pt F d) : p ∈ line p q :=
  mem_line_iff.mpr ⟨0, by simp⟩

theorem right_mem_line (p q : Pt F d) : q ∈ line p q :=
  mem_line_iff.mpr ⟨1, by simp⟩

theorem card_line {p q : Pt F d} (h : p ≠ q) : (line p q).card = Fintype.card F := by
  unfold line
  rw [Finset.card_image_of_injective, Finset.card_univ]
  intro s t hst
  have hv : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have : (s - t) • (q - p) = 0 := by
    have h' : s • (q - p) = t • (q - p) := add_left_cancel hst
    rw [sub_smul, h', sub_self]
  rcases smul_eq_zero.mp this with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 hv

/-- Two distinct points of a line span the same line. -/
theorem line_eq_of_mem {p q p' q' : Pt F d} (h : p ≠ q) (hp' : p' ∈ line p q) (hq' : q' ∈ line p q)
    (h' : p' ≠ q') : line p' q' = line p q := by
  obtain ⟨a, rfl⟩ := mem_line_iff.mp hp'
  obtain ⟨b, rfl⟩ := mem_line_iff.mp hq'
  have hab : b - a ≠ 0 := by
    intro hba
    apply h'
    have : a = b := by linear_combination -hba
    rw [this]
  ext x
  rw [mem_line_iff, mem_line_iff]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨a + t * (b - a), ?_⟩
    simp only [add_smul, mul_smul, smul_sub, add_sub_add_left_eq_sub, ← sub_smul]
    abel_nf
    module
  · rintro ⟨s, rfl⟩
    refine ⟨(s - a) / (b - a), ?_⟩
    have hk : (s - a) / (b - a) * (b - a) = s - a := div_mul_cancel₀ _ hab
    simp only [add_sub_add_left_eq_sub, ← sub_smul, smul_smul, hk]
    module

/-- All affine lines. -/
def affineLines (F : Type*) [Field F] [Fintype F] [DecidableEq F] (d : ℕ) :
    Finset (Finset (Pt F d)) :=
  (Finset.univ.filter (fun pq : Pt F d × Pt F d => pq.1 ≠ pq.2)).image (fun pq => line pq.1 pq.2)

theorem mem_affineLines_iff {b : Finset (Pt F d)} :
    b ∈ affineLines F d ↔ ∃ p q : Pt F d, p ≠ q ∧ line p q = b := by
  unfold affineLines
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]

/-- **Affine lines over a 4-element field form a Steiner system `S(2,4,4^d)`.** -/
theorem affine_isSteinerK4 (hF : Fintype.card F = 4) : IsSteinerK4 (affineLines F d) where
  card_block := by
    intro b hb
    obtain ⟨p, q, hpq, rfl⟩ := mem_affineLines_iff.mp hb
    rw [card_line hpq, hF]
  exists_block := by
    intro x y hxy
    exact ⟨line x y, mem_affineLines_iff.mpr ⟨x, y, hxy, rfl⟩, left_mem_line x y, right_mem_line x y⟩
  unique_block := by
    intro b hb b' hb' x y hxy hxb hyb hxb' hyb'
    obtain ⟨p, q, hpq, rfl⟩ := mem_affineLines_iff.mp hb
    obtain ⟨p', q', hpq', rfl⟩ := mem_affineLines_iff.mp hb'
    rw [← line_eq_of_mem hpq hxb hyb hxy, ← line_eq_of_mem hpq' hxb' hyb' hxy]

theorem card_Pt (F : Type*) [Fintype F] [DecidableEq F] (d : ℕ) :
    Fintype.card (Pt F d) = Fintype.card F ^ d := by
  rw [Fintype.card_fun, Fintype.card_fin]

/-- **Remark C1r over `F`, `|F| = 4`:** on `n = 4^d` points, the affine Steiner representation is a
load-2 multiset attaining the fractional bound `|E|/3` with `3·oct(H[X]) = C(n,2)`. -/
theorem quadratic_defect_affine (hF : Fintype.card F = 4) (d : ℕ) :
    Fintype.card (Pt F d) = 4 ^ d ∧
    IsQMultiset (triTop (Pt F d)) (steinerX (affineLines F d)) 2 ∧
    (∀ e ∈ (Finset.univ : Finset (Pt F d)).powersetCard 2,
      edgeLoad (steinerX (affineLines F d)) e ≤ 2) ∧
    3 * multSize (triTop (Pt F d)) (steinerX (affineLines F d)) = 2 * (4 ^ d).choose 2 ∧
    3 * oct (HX (affineLines F d)) = (4 ^ d).choose 2 := by
  have hn : Fintype.card (Pt F d) = 4 ^ d := by rw [card_Pt, hF]
  obtain ⟨h1, h2, h3, h4⟩ := quadratic_defect (affine_isSteinerK4 (d := d) hF)
  rw [hn] at h3 h4
  exact ⟨hn, h1, h2, h3, h4⟩

end Affine

/-! ### Instantiation: the field with four elements -/

/-- A concrete field with four elements exists (`GaloisField 2 2`). -/
theorem exists_field_card_four :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F), Fintype.card F = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  haveI : Finite (GaloisField 2 2) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  refine ⟨GaloisField 2 2, inferInstance, inferInstance, Classical.decEq _, ?_⟩
  rw [← Nat.card_eq_fintype_card, hcard]

/-- **Remark C1r (existence form).** For every `d` there is an `n = 4^d`-point complete graph and a
half-integral optimal triangle representation `X` (load ≤ 2, `3|X| = 2·C(n,2)`) whose conflict graph
satisfies `3·oct(H[X]) = C(n,2)`, i.e. `oct(H[X]) = n(n−1)/6 = Θ(n²)`. -/
theorem exists_quadratic_defect (d : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (L : Finset (Finset V)),
      Fintype.card V = 4 ^ d ∧ IsSteinerK4 L ∧
      IsQMultiset (triTop V) (steinerX L) 2 ∧
      (∀ e ∈ (Finset.univ : Finset V).powersetCard 2, edgeLoad (steinerX L) e ≤ 2) ∧
      3 * multSize (triTop V) (steinerX L) = 2 * (4 ^ d).choose 2 ∧
      3 * oct (HX L) = (4 ^ d).choose 2 := by
  obtain ⟨F, _, _, _, hF⟩ := exists_field_card_four
  obtain ⟨hn, h1, h2, h3, h4⟩ := quadratic_defect_affine (F := F) hF d
  exact ⟨Pt F d, inferInstance, inferInstance, affineLines F d, hn, affine_isSteinerK4 hF, h1, h2, h3, h4⟩

end Steiner

end PaperV
