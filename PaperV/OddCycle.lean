/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Brooks B, surgery core: odd-cycle extraction (¬bipartite ⇒ odd cycle).

Mathlib lists `IsBipartite ↔ no odd cycle` as a TODO (Combinatorics/SimpleGraph/Bipartite). Here is
the hard direction, hand-built and combined with Mathlib's `two_colorable_iff_forall_loop_even`:
* `exists_split_of_not_cycle` — a non-cycle closed walk (length ≥ 3) splits into two nonempty closed
  walks (crux; via take_spec/dropUntil at a repeated vertex, no rotation);
* `exists_odd_cycle_of_odd_closed_walk` — strong induction: an odd closed walk yields a simple odd
  cycle;
* `exists_odd_cycle_of_not_colorable_two` — `¬ G.Colorable 2 ⇒ ∃ odd cycle`.

Exactly the fact Rabern's odd-cycle surgery needs (the residual of the Rabern route to Brooks Δ=3).
Supersedes the earlier `OddWalk.lean` (whose statement is subsumed by the Mathlib iff used here).
-/
module

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set
public import Mathlib.Combinatorics.SimpleGraph.Coloring
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

open SimpleGraph Finset Walk List

namespace PaperV.Brooks

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma exists_split_of_not_cycle {v : V} (c : G.Walk v v) (hnc : ¬ c.IsCycle) (h3 : 3 ≤ c.length) :
    ∃ (y z : V) (c₁ : G.Walk y y) (c₂ : G.Walk z z),
      1 ≤ c₁.length ∧ 1 ≤ c₂.length ∧ c₁.length + c₂.length = c.length := by
  classical
  have hcnn : ¬ c.Nil := fun hn => by simp [Walk.nil_iff_length_eq.mp hn] at h3
  obtain ⟨s, e, t, rfl⟩ := Walk.not_nil_iff.mp hcnn
  have htp : ¬ t.support.Nodup := by
    rw [← isPath_def]; intro hp
    exact hnc (isCycle_iff_isPath_tail_and_le_length.mpr ⟨by simpa using hp, by simpa using h3⟩)
  obtain ⟨x, hxdup⟩ := List.exists_duplicate_iff_not_nodup.mpr htp
  have hxt : x ∈ t.support := hxdup.mem
  set tu := t.takeUntil x hxt
  set r := t.dropUntil x hxt
  have hspec : tu.append r = t := t.take_spec hxt
  have hcount_t : 2 ≤ t.support.count x := List.duplicate_iff_two_le_count.mp hxdup
  have hcount_tu : tu.support.count x = 1 := count_support_takeUntil_eq_one t hxt
  have hsupp : t.support = tu.support ++ r.support.tail := by
    conv_lhs => rw [← hspec, support_append]
  have hxrtail : x ∈ r.support.tail := by
    have hc2 : t.support.count x = tu.support.count x + r.support.tail.count x := by
      rw [hsupp, List.count_append]
    rw [hcount_tu] at hc2
    exact List.count_pos_iff.mp (by omega)
  have hrlen1 : 1 ≤ r.length := by
    have h1 : 0 < r.support.tail.length := List.length_pos_of_mem hxrtail
    have h2 : r.support.length = r.length + 1 := r.length_support
    rw [List.length_tail, h2] at h1; omega
  have hrnn : ¬ r.Nil := fun hn => by simp [Walk.nil_iff_length_eq.mp hn] at hrlen1
  obtain ⟨s2, er, rt, hrcons⟩ := Walk.not_nil_iff.mp hrnn
  have hxrt : x ∈ rt.support := by
    have hst : r.support.tail = rt.support := by rw [hrcons]; simp [support_cons]
    rw [← hst]; exact hxrtail
  set ru := rt.takeUntil x hxrt
  set rd := rt.dropUntil x hxrt
  have hspecr : ru.append rd = rt := rt.take_spec hxrt
  refine ⟨v, x, Walk.cons e (tu.append rd), Walk.cons er ru, by simp, by simp, ?_⟩
  have ht : (tu.append r).length = t.length := by rw [hspec]
  have hrl : r.length = rt.length + 1 := by rw [hrcons]; simp
  have hrtl : (ru.append rd).length = rt.length := by rw [hspecr]
  simp only [Walk.length_cons, Walk.length_append] at ht hrtl ⊢
  omega

/-- **¬2-colourable ⇒ ∃ odd cycle**, core extraction: an odd closed walk yields a simple odd cycle.
Strong induction on length; the split lemma peels shorter closed walks, one of which stays odd. -/
theorem exists_odd_cycle_of_odd_closed_walk :
    ∀ (n : ℕ) {u : V} (w : G.Walk u u), w.length = n → Odd n →
      ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ Odd c.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u w hlen hodd
    subst hlen
    by_cases hcyc : w.IsCycle
    · exact ⟨u, w, hcyc, hodd⟩
    · have hne1 : w.length ≠ 1 := by
        intro h1
        have hadj : G.Adj (w.getVert 0) (w.getVert 1) := w.adj_getVert_succ (by omega)
        have e0 : w.getVert 0 = u := w.getVert_zero
        have e1 : w.getVert 1 = u := by
          rw [show (1:ℕ) = w.length from h1.symm]; exact w.getVert_length
        rw [e0, e1] at hadj
        exact hadj.ne rfl
      have h3 : 3 ≤ w.length := by
        have hwodd : w.length % 2 = 1 := Nat.odd_iff.mp hodd
        omega
      obtain ⟨y, z, c₁, c₂, h1, h2, hsum⟩ := exists_split_of_not_cycle w hcyc h3
      have hwodd : w.length % 2 = 1 := Nat.odd_iff.mp hodd
      rcases Nat.even_or_odd c₁.length with he1 | ho1
      · have e1 : c₁.length % 2 = 0 := Nat.even_iff.mp he1
        exact ih c₂.length (by omega) c₂ rfl (Nat.odd_iff.mpr (by omega))
      · exact ih c₁.length (by omega) c₁ rfl ho1

/-- **¬ 2-colourable ⇒ ∃ odd cycle** (the `¬bipartite ⇒ odd cycle` direction; Mathlib lists the
`IsBipartite ↔ no odd cycle` characterisation as a TODO). Combines Mathlib's
`two_colorable_iff_forall_loop_even` with the extraction above. Exactly the fact Rabern's
odd-cycle surgery needs. -/
theorem exists_odd_cycle_of_not_colorable_two (hnc : ¬ G.Colorable 2) :
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ Odd c.length := by
  rw [two_colorable_iff_forall_loop_even] at hnc
  push_neg at hnc
  obtain ⟨u, w, hw⟩ := hnc
  exact exists_odd_cycle_of_odd_closed_walk w.length w rfl (Nat.not_even_iff_odd.mp hw)

/-- A maximal independent set (antichain for `G.Adj`) exists — the starting point of Rabern's
surgery (a maximal `I` gives `maxDegree (G − I) ≤ 2`). -/
theorem exists_maximal_independent (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ I : Finset V, Maximal (fun J : Finset V => IsAntichain G.Adj (J : Set V)) I := by
  classical
  set 𝒮 := Finset.univ.filter (fun J : Finset V => IsAntichain G.Adj (J : Set V)) with h𝒮
  have hne : 𝒮.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [h𝒮, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun a ha => absurd ha (by simp)⟩
  obtain ⟨m, hmMax⟩ := 𝒮.exists_maximal hne
  have hmS : m ∈ 𝒮 := hmMax.1
  rw [h𝒮, Finset.mem_filter] at hmS
  refine ⟨m, hmS.2, ?_⟩
  intro J hJ hmJ
  exact hmMax.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩) hmJ

end PaperV.Brooks
