/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — §4.1 tightness of the integral copy inequality (Theorem 4.2). Ledger node L-6.
For `G = K₄ ⊔ K₄` with `u,v` in different components: `ν₃(G)=2`, `ν₃(G_{v→u})=ν₃(G_{u→v})=3`,
`|T₂|=6`, and the conflict graph `H[T₂]` is two disjoint triangles (K₃ ⊔ K₃) on 6 vertices,
so `oct(H[T₂]) = 2`. Hence Theorem 4.2 is tight: `3 + 3 = 2·2 + 2`.

We encode the concrete conflict graph `Htight` and prove `oct Htight = 2`.
- Lower bound: the two vertex-disjoint triangles {0,4,5}, {1,2,3} force oct ≥ 2.
- Upper bound: deleting {0,1} leaves a bipartite graph (classes {2,4}/{3,5}), so oct ≤ 2.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.Core

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

open SimpleGraph Finset

namespace PaperV

/-- The edges of `H[T₂]` for the `K₄ ⊔ K₄` tightness instance: two disjoint triangles. -/
def tightRaw : List (Fin 6 × Fin 6) := [(0,4),(0,5),(1,2),(1,3),(2,3),(4,5)]

/-- The tightness conflict graph `H[T₂] = K₃ ⊔ K₃` on `Fin 6`. -/
def Htight : SimpleGraph (Fin 6) where
  Adj a b := (a, b) ∈ tightRaw ∨ (b, a) ∈ tightRaw
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel Htight.Adj := fun a b => by unfold Htight; infer_instance

private lemma defect_hits_triangle (O : Finset (Fin 6)) (a b d : Fin 6)
    (hab : Htight.Adj a b) (had : Htight.Adj a d) (hbd : Htight.Adj b d)
    (hcol : (Htight.induce ((O : Set (Fin 6))ᶜ)).Colorable 2) :
    a ∈ O ∨ b ∈ O ∨ d ∈ O := by
  by_contra h
  simp only [not_or] at h
  obtain ⟨c, hc⟩ := hcol
  let a' : ↥((O : Set (Fin 6))ᶜ) := ⟨a, by simpa using h.1⟩
  let b' : ↥((O : Set (Fin 6))ᶜ) := ⟨b, by simpa using h.2.1⟩
  let d' : ↥((O : Set (Fin 6))ᶜ) := ⟨d, by simpa using h.2.2⟩
  have hab' : c a' ≠ c b' := SimpleGraph.Adj.ne (hc hab)
  have had' : c a' ≠ c d' := SimpleGraph.Adj.ne (hc had)
  have hbd' : c b' ≠ c d' := SimpleGraph.Adj.ne (hc hbd)
  have ha_lt := (c a').isLt
  have hb_lt := (c b').isLt
  have hd_lt := (c d').isLt
  simp only [Fin.ne_iff_vne] at hab' had' hbd'
  omega

private lemma tight_upper_coloring :
    (Htight.induce (((({0, 1} : Finset (Fin 6)) : Set (Fin 6)))ᶜ)).Colorable 2 := by
  let A : Finset (Fin 6) := {2, 4}
  refine ⟨SimpleGraph.Coloring.mk (fun w => if (w : Fin 6) ∈ A then 0 else 1) ?_⟩
  intro v w hvw
  change Htight.Adj (v : Fin 6) (w : Fin 6) at hvw
  fin_cases v <;> fin_cases w <;> simp_all [A, Htight, tightRaw]

private lemma two_disjoint_hits_card
    (O T1 T2 : Finset (Fin 6)) (hdisj : Disjoint T1 T2)
    (h1 : (O ∩ T1).Nonempty) (h2 : (O ∩ T2).Nonempty) :
    2 ≤ O.card := by
  obtain ⟨x1, hx1O⟩ := h1
  obtain ⟨x2, hx2O⟩ := h2
  simp only [Finset.mem_inter] at hx1O hx2O
  have hx12 : x1 ≠ x2 := fun h => by
    subst x2
    exact Finset.disjoint_left.mp hdisj hx1O.2 hx2O.2
  have hsub : {x1, x2} ⊆ O := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hx1O.1
    · exact hx2O.1
  have hc := Finset.card_le_card hsub
  simpa [hx12] using hc

/-- **Tightness of Theorem 4.2 (§4.1).** `oct(H[T₂]) = 2` for `K₄ ⊔ K₄`, giving equality
`ν₃(G_{v→u}) + ν₃(G_{u→v}) = 2·ν₃(G) + oct(H[T₂])`  (concretely `3 + 3 = 2·2 + 2`). -/
theorem tight_oct : oct Htight = 2 := by
  apply Nat.le_antisymm
  · unfold oct Dq
    let O : Finset (Fin 6) := {0, 1}
    apply Nat.sInf_le
    refine ⟨O, ?_, by decide⟩
    simpa [IsDefectSet, O] using tight_upper_coloring
  · unfold oct Dq
    let S : Set ℕ := {n | ∃ O : Finset (Fin 6), IsDefectSet Htight 2 O ∧ O.card = n}
    have hne : S.Nonempty := defectSet_nonempty Htight (by norm_num)
    have hmin : sInf S ∈ S := Nat.sInf_mem hne
    obtain ⟨O, hcol, hcard⟩ := hmin
    rw [← hcard]
    unfold IsDefectSet at hcol
    let T1 : Finset (Fin 6) := {0, 4, 5}
    let T2 : Finset (Fin 6) := {1, 2, 3}
    have hit1 := defect_hits_triangle O 0 4 5 (by decide) (by decide) (by decide) hcol
    have hit2 := defect_hits_triangle O 1 2 3 (by decide) (by decide) (by decide) hcol
    have h1 : (O ∩ T1).Nonempty := by
      rcases hit1 with h | h | h
      · exact ⟨0, by simp [T1, h]⟩
      · exact ⟨4, by simp [T1, h]⟩
      · exact ⟨5, by simp [T1, h]⟩
    have h2 : (O ∩ T2).Nonempty := by
      rcases hit2 with h | h | h
      · exact ⟨1, by simp [T2, h]⟩
      · exact ⟨2, by simp [T2, h]⟩
      · exact ⟨3, by simp [T2, h]⟩
    exact two_disjoint_hits_card O T1 T2 (by decide) h1 h2

end PaperV
