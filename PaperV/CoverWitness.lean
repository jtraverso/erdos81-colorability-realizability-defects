/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Corollary 3.2a/3.2b interface: cover-to-private-witness specialization.

Abstract layer (any conflict system `C`): a cover-side certificate is an index set `Cov` with a
witness map `wit : ι → C.O` that is injective on `Cov` ("private witnesses are distinct").
  * `witnessMultiset Cov wit`  = the 1-multiset with one copy of each witness;
  * `multSize_witnessMultiset` : |X_C| = |C|;
  * `witness_feasible_compat`  : an independent set of `H[X_C]` is (in bijection with) a feasible
                                 set of witnesses of the same size, hence ≤ ν;
  * `cover_witness_defect`     : |C| ≤ q·ν + D_q(H[X_C])   (= Cor 3.2a, |C| − qν ≤ D_q);
  * `conflict_rigidity`        : Cor 3.2b on the conflict graph `H[X]` (node cited by §3.6).
Triangle layer (`triCS G`): an edge set `E` covering all triangles with a private witness triangle
per edge (`PrivateWitnessCover`) gives  |E| ≤ 2·ν₃(G) + oct(H[X_C]); for a minimum cover |E| = τ₃.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.Copy
public import PaperV.CoverDefect

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

section Abstract

variable (C : ConflictSystem) {ι : Type*} [DecidableEq ι]

/-- The private-witness multiset `X_C`: one copy of each witness `wit i`, `i ∈ Cov`. -/
def witnessMultiset (Cov : Finset ι) (wit : ι → C.O) : C.O → ℕ :=
  fun o => if o ∈ Cov.image wit then 1 else 0

theorem witnessMultiset_le_one (Cov : Finset ι) (wit : ι → C.O) (o : C.O) :
    witnessMultiset C Cov wit o ≤ 1 := by
  unfold witnessMultiset; split_ifs <;> omega

theorem witnessMultiset_isQMultiset (Cov : Finset ι) (wit : ι → C.O) {q : ℕ} (hq : 1 ≤ q) :
    IsQMultiset C (witnessMultiset C Cov wit) q :=
  fun o => (witnessMultiset_le_one C Cov wit o).trans hq

/-- `|X_C| = |C|` when the witnesses are pairwise distinct (private). -/
theorem multSize_witnessMultiset (Cov : Finset ι) (wit : ι → C.O)
    (hinj : Set.InjOn wit (Cov : Set ι)) :
    multSize C (witnessMultiset C Cov wit) = Cov.card := by
  unfold multSize witnessMultiset
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]
  exact Finset.card_image_of_injOn hinj

/-- **Feasibility compatibility.** An independent set `S` of `H[X_C]` projects injectively to a
feasible set of witnesses `T ⊆ wit(Cov)` with `|T| = |S|`; in particular `|S| ≤ ν(C)`. -/
theorem witness_feasible_compat (Cov : Finset ι) (wit : ι → C.O)
    (S : Finset (Copies C (witnessMultiset C Cov wit)))
    (hS : Feasible (Hgraph C (witnessMultiset C Cov wit)) S) :
    ∃ T : Finset C.O, CSFeasible C T ∧ T ⊆ Cov.image wit ∧ T.card = S.card ∧ S.card ≤ nu C := by
  classical
  refine ⟨S.image (objOf (C := C)), ?_, ?_, ?_, indep_le_nu C _ S hS⟩
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := by
      intro heq; subst heq; exact C.Kirrefl a.1 hxy
    exact hS ha hb ⟨hab, Or.inr hxy⟩
  · intro o ho
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp ho
    have hpos : 0 < witnessMultiset C Cov wit c.1 := Fin.pos c.2
    by_contra hno
    change c.1 ∉ Cov.image wit at hno
    have hzero : witnessMultiset C Cov wit c.1 = 0 := by
      unfold witnessMultiset; rw [if_neg hno]
    omega
  · apply Finset.card_image_of_injOn
    intro a ha b hb hab
    by_contra hne
    exact hS ha hb ⟨hne, Or.inl hab⟩

/-- **Corollary 3.2a (abstract).** `|C| ≤ q·ν(C) + D_q(H[X_C])`, i.e. `|C| − qν ≤ D_q(H[X_C])`. -/
theorem cover_witness_defect (Cov : Finset ι) (wit : ι → C.O)
    (hinj : Set.InjOn wit (Cov : Set ι)) {q : ℕ} (hq : 1 ≤ q) :
    Cov.card ≤ q * nu C + Dq (Hgraph C (witnessMultiset C Cov wit)) q := by
  have := transfer_q C (witnessMultiset C Cov wit) q hq (witnessMultiset_isQMultiset C Cov wit hq)
  rwa [multSize_witnessMultiset C Cov wit hinj] at this

/-- Half-integral form: `|C| ≤ 2ν + oct(H[X_C])`. -/
theorem cover_witness_oct (Cov : Finset ι) (wit : ι → C.O)
    (hinj : Set.InjOn wit (Cov : Set ι)) :
    Cov.card ≤ 2 * nu C + oct (Hgraph C (witnessMultiset C Cov wit)) :=
  cover_witness_defect C Cov wit hinj (by norm_num)

/-- **Corollary 3.2b on the conflict graph** (the `conflict_rigidity` node cited in §3.6): if `q`
independent sets of `H[X]` have sizes summing to `q·ν` with `ν` bounding every independent set,
all of them have size exactly `ν`. -/
theorem conflict_rigidity (X : C.O → ℕ) {ν q : ℕ}
    (hν : ∀ S : Finset (Copies C X), Feasible (Hgraph C X) S → S.card ≤ ν)
    (S : Fin q → Finset (Copies C X)) (hfeas : ∀ i, Feasible (Hgraph C X) (S i))
    (hsum : (∑ i, (S i).card) = q * ν) : ∀ i, (S i).card = ν :=
  rigidity_at_equality (Hgraph C X) hν S hfeas hsum

end Abstract

section Triangle

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An edge set `E` (2-subsets of `V`) that covers every triangle of `G`, together with a
**private witness** triangle `wit e ⊇ e` for each `e ∈ E`: no other cover edge lies in `wit e`. -/
structure PrivateWitnessCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset (Finset V)) (wit : Finset V → Finset V) : Prop where
  cover : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ⊆ t
  wit_tri : ∀ e ∈ E, wit e ∈ G.cliqueFinset 3
  wit_contains : ∀ e ∈ E, e ⊆ wit e
  private_ : ∀ e ∈ E, ∀ e' ∈ E, e' ⊆ wit e → e' = e

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The witness map into the triangle conflict system, indexed by the cover edges. -/
def triWit {E : Finset (Finset V)} {wit : Finset V → Finset V} (pw : PrivateWitnessCover G E wit) :
    {e // e ∈ E} → (triCS G).O :=
  fun e => ⟨wit e.1, pw.wit_tri e.1 e.2⟩

/-- Private witnesses are pairwise distinct. -/
theorem triWit_injective {E : Finset (Finset V)} {wit : Finset V → Finset V}
    (pw : PrivateWitnessCover G E wit) : Function.Injective (triWit G pw) := by
  intro e e' h
  have h1 : wit e.1 = wit e'.1 := congrArg Subtype.val h
  have : e'.1 ⊆ wit e.1 := h1 ▸ pw.wit_contains e'.1 e'.2
  exact Subtype.ext (pw.private_ e.1 e.2 e'.1 e'.2 this).symm

/-- The private-witness multiset of a triangle cover, as a multiset on `triCS G`. -/
def triWitnessMultiset {E : Finset (Finset V)} {wit : Finset V → Finset V}
    (pw : PrivateWitnessCover G E wit) : (triCS G).O → ℕ :=
  witnessMultiset (triCS G) (Finset.univ : Finset {e // e ∈ E}) (triWit G pw)

theorem multSize_triWitnessMultiset {E : Finset (Finset V)} {wit : Finset V → Finset V}
    (pw : PrivateWitnessCover G E wit) : multSize (triCS G) (triWitnessMultiset G pw) = E.card := by
  unfold triWitnessMultiset
  rw [multSize_witnessMultiset _ _ _ (fun a _ b _ h => triWit_injective G pw h)]
  simp

/-- **Corollary 3.2a, triangle case.** For an edge cover `E` of the triangles with private witnesses,
`|E| ≤ 2·ν₃(G) + oct(H[X_C])`; for a minimum cover `|E| = τ₃(G)`, this is
`τ₃(G) − 2ν₃(G) ≤ oct(H[X_C])`. -/
theorem triangle_cover_defect {E : Finset (Finset V)} {wit : Finset V → Finset V}
    (pw : PrivateWitnessCover G E wit) :
    E.card ≤ 2 * nu3 G + oct (Hgraph (triCS G) (triWitnessMultiset G pw)) := by
  have := cover_witness_oct (triCS G) (Finset.univ : Finset {e // e ∈ E}) (triWit G pw)
    (fun a _ b _ h => triWit_injective G pw h)
  unfold triWitnessMultiset nu3
  simpa using this

/-- `q`-colour form of the triangle case. -/
theorem triangle_cover_defect_q {E : Finset (Finset V)} {wit : Finset V → Finset V}
    (pw : PrivateWitnessCover G E wit) {q : ℕ} (hq : 1 ≤ q) :
    E.card ≤ q * nu3 G + Dq (Hgraph (triCS G) (triWitnessMultiset G pw)) q := by
  have := cover_witness_defect (triCS G) (Finset.univ : Finset {e // e ∈ E}) (triWit G pw)
    (fun a _ b _ h => triWit_injective G pw h) hq
  unfold triWitnessMultiset nu3
  simpa using this

end Triangle

end PaperV
