/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperV.GalvinMultigraph

/-!
# Kőnig's and Galvin's theorems for simple bipartite graphs

A simple bipartite graph is a set `B : Finset (U × R)` of pairs. Both theorems are the case
`E = B` of the multigraph theorems of `PaperV.GalvinMultigraph`, which come from the registered
Palomar entry `jtraverso/galvin-dinitz`.
-/

@[expose] public section

namespace PaperV
namespace Galvin

variable {U R : Type*} [Fintype U] [Fintype R] [DecidableEq U] [DecidableEq R]

omit [Fintype U] [Fintype R] [DecidableEq R] in
theorem degL_subtype (B : Finset (U × R)) (u : U) :
    degL (fun e : {e // e ∈ B} => e.1.1) u = (B.filter fun e => e.1 = u).card := by
  unfold degL
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext e
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, hx⟩
  · rintro ⟨he, hx⟩; exact ⟨⟨e, he⟩, hx, rfl⟩

omit [Fintype U] [Fintype R] [DecidableEq U] in
theorem degR_subtype (B : Finset (U × R)) (r : R) :
    degR (fun e : {e // e ∈ B} => e.1.2) r = (B.filter fun e => e.2 = r).card := by
  unfold degR
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext e
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, hx⟩
  · rintro ⟨he, hx⟩; exact ⟨⟨e, he⟩, hx, rfl⟩

/-- **Galvin's theorem** (maximum-degree case) for simple bipartite graphs: degrees at most `Δ`
and lists of size at least `Δ` on `B` give a proper list edge colouring. -/
theorem galvin_max_degree (B : Finset (U × R)) (Δ : ℕ)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ)
    (L : U × R → Finset ℕ) (hL : ∀ e ∈ B, Δ ≤ (L e).card) :
    ∃ φ : U × R → ℕ, (∀ e ∈ B, φ e ∈ L e) ∧
      ∀ e ∈ B, ∀ f ∈ B, e ≠ f → (e.1 = f.1 ∨ e.2 = f.2) → φ e ≠ φ f := by
  obtain ⟨φ, hmem, hprop⟩ := galvin_multigraph_max_degree (fun e : {e // e ∈ B} => e.1.1)
    (fun e => e.1.2) Δ (fun u => (degL_subtype B u).trans_le (hdegU u))
    (fun r => (degR_subtype B r).trans_le (hdegR r)) (fun e => L e.1) (fun e => hL e.1 e.2)
  refine ⟨fun e => if h : e ∈ B then φ ⟨e, h⟩ else 0, fun e he => ?_, fun e he f hf hef h => ?_⟩
  · simp only [he, dite_true]; exact hmem _
  · simp only [he, hf, dite_true]
    exact hprop ⟨e, he⟩ ⟨f, hf⟩ (fun h' => hef (congrArg Subtype.val h')) h

/-- **Kőnig's edge colouring** for simple bipartite graphs: degrees at most `Δ` give a proper edge
colouring with colours `< Δ`. -/
theorem konig_edge_coloring (B : Finset (U × R)) (Δ : ℕ)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ) :
    ∃ φ : U × R → ℕ, (∀ e ∈ B, φ e < Δ) ∧
      ∀ e ∈ B, ∀ f ∈ B, e ≠ f → (e.1 = f.1 ∨ e.2 = f.2) → φ e ≠ φ f := by
  obtain ⟨φ, hmem, hprop⟩ := galvin_max_degree B Δ hdegU hdegR (fun _ => Finset.range Δ)
    (fun _ _ => (Finset.card_range Δ).ge)
  exact ⟨φ, fun e he => Finset.mem_range.mp (hmem e he), hprop⟩

end Galvin
end PaperV
