/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — exportable corollaries of the transfer theorem (editorial review §12.3–12.4).

All follow from `PaperV.transfer_q` (`multSize C X ≤ q * nu C + Dq (Hgraph C X) q`):
  * A (constructive ceiling)         `nu_ge_ceil`
  * B (arbitrary / non-optimal rep.) `nu_ge_frac`   (rational form)
  * C (best representation)          `transfer_min_representation`
  * normalisation                    `defq H q = D_q(H)/q`

These do not touch the core proofs; they repackage the transfer bound as the review recommends.
-/
module

public import PaperV.ConflictGraph

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable (C : ConflictSystem)

/-- Normalised colourability defect `def_q(H) = D_q(H)/q` (§12.4). -/
noncomputable def defq {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (q : ℕ) : ℚ :=
  (Dq H q : ℚ) / q

/-- **Corollary A (constructive form, §12.3.A).** Deleting an optimal `D_q`-set and `q`-colouring
the rest, some colour class has at least `⌈(|X| − D_q(H[X]))/q⌉` objects; hence
`ν ≥ ⌈(|X| − D_q(H[X]))/q⌉`. (In ℕ, `⌈a/q⌉ = (a + q − 1)/q`.) -/
theorem nu_ge_ceil (X : C.O → ℕ) (q : ℕ) (hq : 1 ≤ q) (hX : IsQMultiset C X q) :
    (multSize C X - Dq (Hgraph C X) q + (q - 1)) / q ≤ nu C := by
  have htransfer := transfer_q C X q hq hX
  have hsub : multSize C X - Dq (Hgraph C X) q ≤ q * nu C := by
    omega
  apply (Nat.div_le_iff_le_mul_add_pred (by omega)).2
  simpa [add_comm] using add_le_add_right hsub (q - 1)

/-- **Corollary B (arbitrary/non-optimal fractional representation, §12.3.B).** For any
`q`-multiset `X` (not necessarily from an LP optimum), `ν ≥ |X|/q − D_q(H[X])/q` over `ℚ`. -/
theorem nu_ge_frac (X : C.O → ℕ) (q : ℕ) (hq : 1 ≤ q) (hX : IsQMultiset C X q) :
    (multSize C X : ℚ) / q - (Dq (Hgraph C X) q : ℚ) / q ≤ (nu C : ℚ) := by
  have htransfer := transfer_q C X q hq hX
  have htransferQ : (multSize C X : ℚ) ≤
      (q : ℚ) * (nu C : ℚ) + (Dq (Hgraph C X) q : ℚ) := by
    exact_mod_cast htransfer
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  rw [← sub_div]
  apply (div_le_iff₀ hqQ).2
  linarith

/-- **Corollary C (best representation, §12.3.C).** Over a nonempty finite family of `q`-multiset
representations that all realise the same size `M`, the transfer bound holds with the *minimum*
defect in the family: `M ≤ q·ν + min_{X} D_q(H[X])`. So the relevant obstruction is the least
defect among representations, not that of an arbitrary one. -/
theorem transfer_min_representation (q : ℕ) (M : ℕ) (hq : 1 ≤ q)
    (reps : Finset (C.O → ℕ)) (hne : reps.Nonempty)
    (hrep : ∀ X ∈ reps, IsQMultiset C X q ∧ multSize C X = M) :
    M ≤ q * nu C + reps.inf' hne (fun X => Dq (Hgraph C X) q) := by
  classical
  obtain ⟨X₀, hX₀mem, hmin⟩ :=
    Finset.exists_mem_eq_inf' hne (fun X => Dq (Hgraph C X) q)
  obtain ⟨hX₀, hsize⟩ := hrep X₀ hX₀mem
  rw [hmin]
  rw [← hsize]
  exact transfer_q C X₀ q hq hX₀

end PaperV
