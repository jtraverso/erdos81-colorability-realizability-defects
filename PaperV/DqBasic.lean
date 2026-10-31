/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Basic structural facts about the colourability defect `D_q` (v0.9.15 candidate).

`Dq_antitone`: the defect family `q ↦ D_q(H)` is antitone — allowing more colours never requires
a larger deletion. In particular `D_q(H) ≤ D_2(H) = oct(H)` for every `q ≥ 2`, so every bound
proved through `oct` propagates up the hierarchy. Immediate from `Colorable.mono` plus monotonicity
of `sInf` on the (nonempty) defect-size set.
-/
module

public import PaperV.Core

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The defect `D_q` is antitone in `q`.** More colours never need a larger deletion:
every `q`-defect set is also a `q'`-defect set for `q ≤ q'`, so the infima are ordered. -/
theorem Dq_antitone (H : SimpleGraph V) [DecidableRel H.Adj] {q q' : ℕ}
    (hq : 1 ≤ q) (hqq : q ≤ q') : Dq H q' ≤ Dq H q := by
  classical
  apply csInf_le_csInf (OrderBot.bddBelow _) (defectSet_nonempty H hq)
  rintro n ⟨O, hO, rfl⟩
  exact ⟨O, hO.mono hqq, rfl⟩

/-- Specialisation: for `q ≥ 2` the general defect is dominated by `oct = D_2`. -/
theorem Dq_le_oct (H : SimpleGraph V) [DecidableRel H.Adj] {q : ℕ} (hq : 2 ≤ q) :
    Dq H q ≤ oct H :=
  Dq_antitone H (by norm_num) hq

/-- Colourability transfers across the identity induced subgraph `H⟦univ⟧ ≃g H`. -/
theorem colorable_induce_univ_iff (H : SimpleGraph V) (q : ℕ) :
    (H.induce Set.univ).Colorable q ↔ H.Colorable q := by
  constructor
  · rintro ⟨C⟩; exact ⟨C.comp H.induceUnivIso.symm.toHom⟩
  · rintro ⟨C⟩; exact ⟨C.comp H.induceUnivIso.toHom⟩

/-- **Zero-defect characterisation (extremal at `D_q = 0`).** For `q ≥ 1`, the defect vanishes exactly
when `H` is already `q`-colourable — no deletion is needed. -/
theorem Dq_eq_zero_iff (H : SimpleGraph V) [DecidableRel H.Adj] {q : ℕ} (hq : 1 ≤ q) :
    Dq H q = 0 ↔ H.Colorable q := by
  have hset : (((∅ : Finset V) : Set V)ᶜ) = (Set.univ : Set V) := by simp
  rw [Dq, Nat.sInf_eq_zero]
  constructor
  · rintro (h0 | hemp)
    · obtain ⟨O, hO, hO0⟩ := h0
      rw [Finset.card_eq_zero] at hO0; subst hO0
      rw [IsDefectSet, hset] at hO
      exact (colorable_induce_univ_iff H q).mp hO
    · exact absurd (defectSet_nonempty H hq) (by rw [hemp]; exact fun h => Set.not_nonempty_empty h)
  · intro hcol
    left
    exact ⟨∅, by rw [IsDefectSet, hset]; exact (colorable_induce_univ_iff H q).mpr hcol,
      Finset.card_empty⟩

/-- `oct(H) = 0` iff `H` is bipartite (2-colourable). Specialisation of `Dq_eq_zero_iff` at `q = 2`. -/
theorem oct_eq_zero_iff (H : SimpleGraph V) [DecidableRel H.Adj] :
    oct H = 0 ↔ H.Colorable 2 :=
  Dq_eq_zero_iff H (by norm_num)

/-- **Chromatic threshold (extremal).** The defect vanishes exactly at and above the chromatic number:
`D_q(H) = 0 ↔ χ(H) ≤ q`. Together with `Dq_antitone`, `q ↦ D_q(H)` is a decreasing sequence of
naturals that first reaches `0` precisely at `q = χ(H)` — a graded refinement of the chromatic number. -/
theorem Dq_eq_zero_iff_chromatic (H : SimpleGraph V) [DecidableRel H.Adj] {q : ℕ} (hq : 1 ≤ q) :
    Dq H q = 0 ↔ H.chromaticNumber ≤ (q : ℕ∞) := by
  rw [Dq_eq_zero_iff H hq]
  exact chromaticNumber_le_iff_colorable.symm

/-- Below the chromatic number the defect is strictly positive: `0 < D_q(H) ↔ q < χ(H)`. -/
theorem Dq_pos_iff_lt_chromatic (H : SimpleGraph V) [DecidableRel H.Adj] {q : ℕ} (hq : 1 ≤ q) :
    0 < Dq H q ↔ (q : ℕ∞) < H.chromaticNumber := by
  rw [Nat.pos_iff_ne_zero, ne_eq, Dq_eq_zero_iff_chromatic H hq, not_le]

/-- **Monotonicity of the defect under edge addition.** A subgraph has no larger defect: every
defect set of `H'` is a defect set of `H ≤ H'` (colourability of the sparser induced subgraph follows
by `Colorable.mono_left`). Complements `Dq_antitone` (monotone in the number of colours). -/
theorem Dq_mono_left (H H' : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel H'.Adj] {q : ℕ}
    (hq : 1 ≤ q) (hle : H ≤ H') : Dq H q ≤ Dq H' q := by
  classical
  apply csInf_le_csInf (OrderBot.bddBelow _) (defectSet_nonempty H' hq)
  rintro n ⟨O, hO, rfl⟩
  refine ⟨O, ?_, rfl⟩
  rw [IsDefectSet] at hO ⊢
  have hsub : H.induce ((O : Set V)ᶜ) ≤ H'.induce ((O : Set V)ᶜ) := fun a b hab => hle hab
  exact Colorable.mono_left hsub hO

end PaperV
