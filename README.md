# Lean 4 proof for "The σ⁻-game on grids with all sides odd, in every dimension"

This repository has the Lean 4 formalization, with mathlib, of the main theorem of my note (https://doi.org/10.5281/zenodo.24167505).

## The theorem

In the σ⁻ game, pressing a cell flips its neighbours but not the cell itself. Take a grid with all sides odd, in any dimension, with either the edge or the king neighbourhood. Then the all-on configuration, and every completely symmetric configuration, is reachable if and only if some value of a(n_i) = v_2(n_i + 1), among the sides n_i ≡ 3 mod 4, appears an odd number of times.

## Where to look

- `SigmaMeno/Enunciato.lean` has the definitions and the statement `TeoremaPrincipale`. It was written before the proofs.
- `SigmaMeno/Globale/Simmetriche.lean` has `teorema_principale`, the proof of that statement.
- `Verifica.lean` prints the axioms used. Only `propext`, `Classical.choice` and `Quot.sound` appear.

## How to build

Install [elan](https://github.com/leanprover/elan), then run:

```
lake exe cache get
lake build
lake env lean Verifica.lean
```

`lake exe cache get` downloads a compiled mathlib, so you do not have to build it yourself.

Versions: Lean 4.35.0 and mathlib v4.35.0, as set in `lean-toolchain` and `lake-manifest.json`.

## Notes

The Lean statement also covers the trivial case of dimension 0. It uses coordinates from 0 to n−1.

The names in the code are in Italian:

| Italian | English |
| --- | --- |
| Enunciato | statement |
| TeoremaPrincipale | main theorem |
| Griglia | grid |
| Locale / Globale | local / global |

## Author and license

Emanuele Rizzan. Apache-2.0, see `LICENSE`.
