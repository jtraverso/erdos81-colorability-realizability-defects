# Colorability and realizability defects (Erdős #81, Paper V) in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of the main results of the preprint *Colorability and
Realizability Defects in Resource-Dominated Packing Relaxations* (Erdős #81 series, Paper V,
preprint 1.0, 18 October 2026; series repository
[jtraverso/erdos-81-chordal-clique-partitions](https://github.com/jtraverso/erdos-81-chordal-clique-partitions),
file `preprints/PAPER_V/01_manuscript/PAPER_V_preprint_v1.0_en.pdf`; series collection on Zenodo,
[doi:10.5281/zenodo.23479507](https://doi.org/10.5281/zenodo.23479507)).

A *conflict system* is a finite set of objects with a symmetric irreflexive conflict relation; its
packing number `ν` is the largest size of a conflict-free set. For a multiset `X` of objects,
`H[X]` is the conflict graph on the copies of `X` (copies of one object are adjacent), and
`D_q(H)` is the least number of vertices whose deletion makes `H` `q`-colourable (`oct = D_2`).
The paper bounds the loss between fractional and integral packings by such defects, extends the
bound to classes realized in another target system, and applies it to host assignments (list edge
colouring of bipartite graphs) and to vertex copies of triangle packings.

| Lean (namespace `ErdosPaperV`) | Paper | Statement |
|---|---|---|
| `lemma_3_1` | Lemma 3.1 | Two disjoint independent sets cover all but `oct(H)` vertices. |
| `corollary_3_2` | Corollary 3.2 | `ν ≥ ⌈(|X| − D_q(H[X]))/q⌉` for every `q`-multiset `X`. |
| `theorem_3_3`, `theorem_3_4` | Theorems 3.3, 3.4 | For a `1/2`- or `1/q`-integral optimum `x*` of a resource-dominated relaxation: `μ* − ν ≤ D_q(H[X])/q`. |
| `theorem_3_4w` | Theorem 3.4w | `|X|_w ≤ q ν_w + D_q^w(H[X])`. |
| `theorem_4_2`, `theorem_4_2_nu` | Theorem 4.2 | Realizable-class transfer: some class satisfies `|X|_w ≤ q w_T(R(C_i)) + cost`; hence `|X|_w ≤ q ν_{w_T}(T) + cost`. |
| `theorem_4_4` | Theorem 4.4 | The identity realizers give exactly the weighted colourability defect. |
| `theorem_5_2_galvin`, `theorem_5_2_bkw` | Theorem 5.2 | List edge colouring of bipartite multigraphs: Galvin (lists of size `Δ`) and Borodin–Kostochka–Woodall (lists of size `max(d(u), d(v))`). |
| `corollary_5_3_galvin`, `corollary_5_3_bkw` | Corollary 5.3 | Under either hypothesis the host system restricted to the requested bases `B` has packing number `|B|`. |
| `example_5_5` | Example 5.5 | On `K_{r,r}`: `D_1 = r² − r`, host realizability defect `0`, `ν(hostCS) = r²`. |
| `theorem_6_1` | Theorem 6.1 | `ν₃*(G_{v→u}) + ν₃*(G_{u→v}) ≤ 2ν₃*(G)` for nonadjacent `u, v`. |
| `theorem_6_2` | Theorem 6.2 | For maximum triangle packings `P'`, `P''` of `G_{v→u}`, `G_{u→v}` and `T₂` their image in `G` (`mappedTri`): `ν₃(G_{v→u}) + ν₃(G_{u→v}) = |T₂| ≤ 2ν₃(G) + oct(H[T₂])`. |
| `corollary_6_2a` | Corollary 6.2a | `ν₃(G_{v→u}) + ν₃(G_{u→v}) ≤ 3ν₃(G)`. |
| `proposition_7_1` | Proposition 7.1 | The pure-profile packing number is `min(m⌊s/2⌋, C(s,2))`. |
| `theorem_7_3_fractional`, `theorem_7_3_integral` | Theorem 7.3 | The copy inequalities for mixed triangle/`K₄` packings with size-dependent gains; the integral form for the image `X` in `G` of maximum-weight mixed packings of the two copies (`mappedMixed`): `ν_w(G_{v→u}) + ν_w(G_{u→v}) = |X|_w ≤ 2ν_w(G) + D_2^w(H[X])`. |

Here `G_{v→u}` replaces the neighbourhood of `v` by that of `u`, `ν₃` is the triangle packing
number and `ν₃*` its fractional relaxation.

## Files

- [`PaperVChallenge.lean`](PaperVChallenge.lean): the definitions and the 19 statements; it imports only
  Mathlib. `edgesIn`, `IsTrianglePacking` and `IsFracTrianglePacking` are copied verbatim from
  [PALOMAR-2026-10-15-000011](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000011&version=2)
  and `nu3` from [PALOMAR-2026-10-29-000006](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-29-000006&version=1)
  (Paper III); the other definitions are copied from the Paper V library.
- [`PaperVSolution.lean`](PaperVSolution.lean): the same definitions, conversions of the structures
  (`ConflictSystem`, `ResourceRelaxation`, `ClassRealizer`, `RealCert`) to those of the library,
  proofs that the registered `ν₃` and `ν₃*` equal the library's, and the 19 theorems.
- [`PaperV/`](PaperV): the library (63 modules), the import closure of the numbered results of
  the paper in the author's Lean freeze.
- [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml).

## Dependencies on registered entries

- [`jtraverso/galvin-dinitz`](https://github.com/jtraverso/galvin-dinitz) @ `84dcda4`
  (PALOMAR-2026-10-18-000029, version 2): Galvin's theorem and the Borodin–Kostochka–Woodall
  theorem for bipartite multigraphs. `PaperV/GalvinMultigraph.lean` and `PaperV/Galvin.lean` derive
  from them the forms used in the paper; they replace the freeze's own modules (simple-graph
  Galvin, stable matchings, Kőnig colourings and rank engine), from which the multigraph modules of
  that entry were taken.
- [`jtraverso/brooks`](https://github.com/jtraverso/brooks) @ `b99e6f5`
  (PALOMAR-2026-10-16-000003, version 2): Brooks' theorem, used for the subcubic copy conflict graph
  in Corollary 6.2a. It replaces the freeze's Brooks modules.

## How the proofs go

The transfer bounds (§3–4) are averaging arguments over the colour classes of `H[X]` after
deleting a defect set, or over the classes of a realizability certificate. Host completion (§5)
realizes requested bases as edge-disjoint host triangles through a proper list host assignment,
which Galvin's and the Borodin–Kostochka–Woodall theorems provide. The copy inequalities (§6–7) map
optimal packings of the two copies back to `G`; every edge of `G` then carries load at most two,
so the copy conflict graph is subcubic, and the integral bounds follow from splitting and Brooks'
theorem.

## Not included

Proved in the library but not stated in the Challenge: Corollaries 3.2a, 3.2b, 4.6, 7.3a, Lemmas 3.5
and 6.2k, Propositions 5.1, 7.1a, 7.1b, the SEAL statements of Section 8 (Propositions 8.1, 8.2,
Theorem 8.3) and Proposition 9.3. The SEAL implementation, its benchmarks and runtime model, and
the enumeration of maximum packings in Section 9 are computations outside the formalization.

## Provenance and checks

The library is the author's Lean freeze of Paper V (version 1.10, Lean 4.35.0, Mathlib
`56a0058`), ported to Lean `v4.35.0-rc3` and the module system (imports made `public`,
`@[expose] public section`), with the Brooks and Galvin modules replaced by the registered entries
above. Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```
lake exe cache get
lake build
```

No `sorry`; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound` for the 19
theorems; the elaborated statements and definitions of `PaperVChallenge.lean` and `PaperVSolution.lean` are
identical (`pp.all`).
