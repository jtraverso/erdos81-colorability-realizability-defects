/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GalvinMultigraph
public import Mathlib.Data.Fintype.Card

/-!
# Galvin's theorem and its local form for bipartite multigraphs

A bipartite multigraph is an edge type `E` with endpoint maps `left : E → U` and `right : E → R`;
distinct edges are adjacent when they share an endpoint. Both theorems are obtained from the
registered Palomar entry `jtraverso/galvin-dinitz` (PALOMAR-2026-10-18-000029, version 2):
`GalvinMultigraph.galvin_of_degree_bound` (Galvin, 1995) and `GalvinMultigraph.galvin_local`
(Borodin–Kostochka–Woodall, 1997).
-/

@[expose] public section

namespace PaperV
namespace Galvin

variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E] [DecidableEq U] [DecidableEq R]
  [DecidableEq E]

/-- Left degree of the vertex `u`. -/
def degL (left : E → U) (u : U) : ℕ := (Finset.univ.filter fun e => left e = u).card

/-- Right degree of the vertex `r`. -/
def degR (right : E → R) (r : R) : ℕ := (Finset.univ.filter fun e => right e = r).card

omit [Fintype U] [Fintype R] [DecidableEq R] [DecidableEq E] in
theorem natCard_left (left : E → U) (u : U) : Nat.card {e // left e = u} = degL left u := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl

omit [Fintype U] [Fintype R] [DecidableEq U] [DecidableEq E] in
theorem natCard_right (right : E → R) (r : R) : Nat.card {e // right e = r} = degR right r := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl

/-- **Galvin's theorem for bipartite multigraphs.** Degrees at most `Δ` and lists of size at least
`Δ` give a proper list edge colouring. -/
theorem galvin_multigraph_max_degree (left : E → U) (right : E → R) (Δ : ℕ)
    (hdegU : ∀ u, degL left u ≤ Δ) (hdegR : ∀ r, degR right r ≤ Δ)
    (L : E → Finset ℕ) (hL : ∀ e, Δ ≤ (L e).card) :
    ∃ φ : E → ℕ, (∀ e, φ e ∈ L e) ∧
      ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f :=
  GalvinMultigraph.galvin_of_degree_bound left right Δ
    (fun u => (natCard_left left u).trans_le (hdegU u))
    (fun r => (natCard_right right r).trans_le (hdegR r)) L hL

/-- **Borodin–Kostochka–Woodall.** Lists of size at least `max(d(u), d(r))` on every edge `ur` of a
bipartite multigraph give a proper list edge colouring. -/
theorem galvin_bkw_local (left : E → U) (right : E → R)
    (L : E → Finset ℕ) (hL : ∀ e, max (degL left (left e)) (degR right (right e)) ≤ (L e).card) :
    ∃ φ : E → ℕ, (∀ e, φ e ∈ L e) ∧
      ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f :=
  GalvinMultigraph.galvin_local left right L (fun e => by
    rw [natCard_left, natCard_right]; exact hL e)

end Galvin
end PaperV
