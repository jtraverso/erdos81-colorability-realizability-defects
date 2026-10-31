/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — reusable, kernel-checkable certificates for the packing number `ν` of a conflict
system (Def 2.1, `PaperV.ConflictSystem`).

Two ways of certifying an upper bound on the size of a feasible (= conflict-free) object set,
both of which a concrete instance can discharge by `decide`:

* **clique cover** (`card_le_of_colouring`, `nu_le_of_colouring`): a colouring of the objects by
  `m` colours in which any two distinct objects of the same colour conflict.  A feasible set meets
  each colour class at most once, so it has at most `m` elements.  The certificate is linear in the
  number of objects and is checked in a single pass;
* **pruned branch-and-bound** (`NoPacking`, `card_lt_of_noPacking`, `nu_lt_of_noPacking`): the
  standard "exclude / include the head object" recursion, with the cardinality cut-off `|l| < k`.
  `NoPacking conf fuel k l = true` certifies that no feasible set of size `k` is drawn from `l`.

Both are stated for an arbitrary Boolean *over-approximation* `conf` of the conflict relation, read
through a labelling `f : ι → C.O` of the objects.  Only soundness of `conf` is required — two
objects that the certificate treats as non-conflicting really are non-conflicting — so a concrete
instance may replace the mathematical conflict relation by a packed bit table that the kernel
evaluates with machine-backed `Nat` arithmetic, while the statements stay at the level of
`ConflictSystem`.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.ConflictGraph

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Set

@[expose] public section

open Finset

namespace PaperV
namespace PackingCert

variable {C : ConflictSystem} {ι : Type*}

/-! ### Generalities -/

/-- A feasible set drawn from a list of labels is no larger than the list. -/
theorem card_le_length {f : ι → C.O} {l : List ι} {S : Finset C.O}
    (hsub : ∀ o ∈ S, o ∈ l.map f) : S.card ≤ l.length := by
  classical
  have hss : S ⊆ (l.map f).toFinset := fun o ho => List.mem_toFinset.mpr (hsub o ho)
  calc S.card ≤ (l.map f).toFinset.card := Finset.card_le_card hss
    _ ≤ (l.map f).length := List.toFinset_card_le _
    _ = l.length := by simp

/-! ### Clique-cover certificates -/

/-- **Clique-cover bound.**  If the objects labelled by `l` carry colours `< m` such that any two
of them with distinct labels and the same colour conflict, then every feasible object set drawn
from `l` has at most `m` elements. -/
theorem card_le_of_colouring {f : ι → C.O} {l : List ι} {col : ι → ℕ} {m : ℕ}
    (hlt : ∀ i ∈ l, col i < m)
    (hcol : ∀ i ∈ l, ∀ j ∈ l, f i ≠ f j → col i = col j → C.K (f i) (f j))
    {S : Finset C.O} (hsub : ∀ o ∈ S, o ∈ l.map f) (hS : CSFeasible C S) :
    S.card ≤ m := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨o₀, ho₀⟩
  · simp
  · have hex : ∀ o ∈ S, ∃ i, i ∈ l ∧ f i = o := fun o ho => List.mem_map.mp (hsub o ho)
    have : Nonempty ι := ⟨(hex o₀ ho₀).choose⟩
    choose! g hgl hgf using hex
    have hinj : Set.InjOn (fun o => col (g o)) ↑S := by
      intro x hx y hy hxy
      by_contra hne
      have hfx : f (g x) = x := hgf x hx
      have hfy : f (g y) = y := hgf y hy
      have hK : C.K (f (g x)) (f (g y)) :=
        hcol (g x) (hgl x hx) (g y) (hgl y hy) (by rw [hfx, hfy]; exact hne) hxy
      rw [hfx, hfy] at hK
      exact hS hx hy hK
    calc S.card = (S.image fun o => col (g o)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range m).card := by
          refine Finset.card_le_card ?_
          intro c hc
          obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hc
          exact Finset.mem_range.mpr (hlt (g o) (hgl o ho))
      _ = m := Finset.card_range m

/-- **Clique-cover bound for `ν`.**  A cover of all the objects by `m` conflict-cliques bounds the
packing number by `m`. -/
theorem nu_le_of_colouring {f : ι → C.O} {l : List ι} {col : ι → ℕ} {m : ℕ}
    (hl : ∀ o : C.O, o ∈ l.map f)
    (hlt : ∀ i ∈ l, col i < m)
    (hcol : ∀ i ∈ l, ∀ j ∈ l, f i ≠ f j → col i = col j → C.K (f i) (f j)) :
    nu C ≤ m := by
  classical
  refine Finset.sup_le ?_
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  exact card_le_of_colouring hlt hcol (fun o _ => hl o) hS

/-- A clique cover matching a feasible set in size computes `ν` exactly. -/
theorem nu_eq_of_colouring_of_feasible {f : ι → C.O} {l : List ι} {col : ι → ℕ} {m : ℕ}
    (hl : ∀ o : C.O, o ∈ l.map f)
    (hlt : ∀ i ∈ l, col i < m)
    (hcol : ∀ i ∈ l, ∀ j ∈ l, f i ≠ f j → col i = col j → C.K (f i) (f j))
    {S : Finset C.O} (hS : CSFeasible C S) (hcard : S.card = m) :
    nu C = m := by
  classical
  refine le_antisymm (nu_le_of_colouring hl hlt hcol) ?_
  have hle : S.card ≤ nu C := Finset.le_sup (f := Finset.card) (by simp [hS])
  omega

/-! ### Branch-and-bound certificates -/

/-- `NoPacking conf fuel k l` is the pruned branch-and-bound search certifying that the objects
labelled by `l` carry no feasible set of size `k` (see `card_lt_of_noPacking`; `fuel` must bound
`l.length`).  Besides the recursion on the head object it uses the cardinality cut-off
`|l| < k`, which is what keeps a kernel evaluation of the certificate small. -/
def NoPacking (conf : ι → ι → Bool) : ℕ → ℕ → List ι → Bool
  | _, 0, _ => false
  | 0, _ + 1, _ => true
  | _ + 1, _ + 1, [] => true
  | fuel + 1, k + 1, i :: is =>
      decide (is.length + 1 < k + 1) ||
        (NoPacking conf fuel (k + 1) is && NoPacking conf fuel k (is.filter fun j => !conf i j))

/-- **Soundness of the branch-and-bound certificate.**  `conf` need only over-approximate the
conflict relation on the ambient list `L`: whenever it reports a conflict between differently
labelled objects, they really do conflict. -/
theorem card_lt_of_noPacking {f : ι → C.O} {conf : ι → ι → Bool} {L : List ι}
    (hconf : ∀ i ∈ L, ∀ j ∈ L, f i ≠ f j → conf i j = true → C.K (f i) (f j)) (fuel : ℕ) :
    ∀ (k : ℕ) (l : List ι), l ⊆ L → ∀ S : Finset C.O, l.length ≤ fuel →
      (∀ o ∈ S, o ∈ l.map f) → CSFeasible C S → NoPacking conf fuel k l = true → S.card < k := by
  classical
  induction fuel with
  | zero =>
      intro k l _ S hlen hsub _ h
      match k with
      | 0 => simp [NoPacking] at h
      | k + 1 =>
          have hnil : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
          subst hnil
          have := card_le_length hsub
          simp only [List.length_nil] at this
          omega
  | succ fuel ih =>
      intro k l hlL S hlen hsub hS h
      match k, l with
      | 0, _ => simp [NoPacking] at h
      | k + 1, [] =>
          have := card_le_length hsub
          simp only [List.length_nil] at this
          omega
      | k + 1, i :: is =>
          have hiL : i ∈ L := hlL (List.mem_cons_self ..)
          have hisL : is ⊆ L := fun _ hx => hlL (List.mem_cons_of_mem _ hx)
          simp only [List.length_cons] at hlen
          have hlen' : is.length ≤ fuel := by omega
          simp only [NoPacking, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
          rcases h with hcut | ⟨hA, hB⟩
          · have := card_le_length hsub
            simp only [List.length_cons] at this
            omega
          · by_cases hiS : f i ∈ S
            · -- the head object is used: recurse on its non-neighbours
              have hSe : CSFeasible C (S.erase (f i)) := fun a ha b hb =>
                hS (mem_of_mem_erase ha) (mem_of_mem_erase hb)
              have hsube : ∀ o ∈ S.erase (f i), o ∈ (is.filter fun j => !conf i j).map f := by
                intro o ho
                have hoS : o ∈ S := mem_of_mem_erase ho
                have hoi : o ≠ f i := ne_of_mem_erase ho
                obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (hsub o hoS)
                have hji : f i ≠ f j := fun hEq => hoi hEq.symm
                have hjis : j ∈ is := by
                  rcases List.mem_cons.mp hj with rfl | hj'
                  · exact absurd rfl hji
                  · exact hj'
                have hnk : ¬ C.K (f i) (f j) := hS hiS hoS
                have hcf : conf i j = false := by
                  rcases Bool.eq_false_or_eq_true (conf i j) with hc | hc
                  · exact absurd (hconf i hiL j (hisL hjis) hji hc) hnk
                  · exact hc
                exact List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨hjis, by simp [hcf]⟩, rfl⟩
              have hflen : (is.filter fun j => !conf i j).length ≤ fuel :=
                le_trans (List.length_filter_le _ _) hlen'
              have hlt := ih k _ (fun _ hx => hisL (List.mem_of_mem_filter hx)) (S.erase (f i))
                hflen hsube hSe hB
              have := card_erase_add_one hiS
              omega
            · -- the head object is unused
              have hsub' : ∀ o ∈ S, o ∈ is.map f := by
                intro o ho
                obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (hsub o ho)
                rcases List.mem_cons.mp hj with rfl | hj'
                · exact absurd ho hiS
                · exact List.mem_map.mpr ⟨j, hj', rfl⟩
              exact ih (k + 1) is hisL S hlen' hsub' hS hA

/-- **Branch-and-bound bound for `ν`.**  If the search over a list labelling all objects reports
that no feasible set of size `k` exists, then `ν < k`. -/
theorem nu_lt_of_noPacking {f : ι → C.O} {conf : ι → ι → Bool} {l : List ι} {k : ℕ}
    (hl : ∀ o : C.O, o ∈ l.map f)
    (hconf : ∀ i ∈ l, ∀ j ∈ l, f i ≠ f j → conf i j = true → C.K (f i) (f j))
    (h : NoPacking conf l.length k l = true) :
    nu C < k := by
  classical
  have hk : k ≠ 0 := by rintro rfl; simp [NoPacking] at h
  refine (Finset.sup_lt_iff (Nat.pos_of_ne_zero hk)).mpr ?_
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  exact card_lt_of_noPacking hconf l.length k l (fun _ hx => hx) S le_rfl (fun o _ => hl o) hS h

end PackingCert
end PaperV
