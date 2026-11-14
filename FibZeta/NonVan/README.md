# FibZeta/NonVan — Proposition 5 (nonvanishing)

Main results (`FibZeta/NonVan/Nonvanishing.lean`):

* `FibZeta.NonVan.nonvanishing : Nonvanishing`, proved with no hypothesis.
* `FibZeta.NonVan.nonvanishing_of_entry (_hE : EntryIdentity) : Nonvanishing`, the requested interface
  form. It does not use the hypothesis.

Axioms: `propext, Classical.choice, Quot.sound`.

## Why `EntryIdentity` is not needed

The argument works directly with the formal Hankel matrix of `Defs.lean` at `τ = t`, `X = Ξ`. Its
entries are `Ln n (s^k)`, where `Ln n P = Lpoly(P /ₘ F_n) + ∑_a P(x_a)/F_n'(x_a) · 2t^a(S_a − Ξ)`
is the linear map `L_Ξ(P/F_n)` (`Ln_X_pow`). The only place a "real" fact enters is the value of the
Cauchy transform at the nodes, `𝓕(x_a) = 2t^a(Ξ − S_a)` (`cauchyF_node`), proved directly from the
series. So the real functional `Lfun`, with its derivatives, never appears.

## Map to PROOF.md §5

| PROOF §5 step | Lean |
|---|---|
| `Δ_n(Ξ) = 0` gives a kernel polynomial `Q_n ≠ 0`, `deg < n` | `Delta_eval`, `exists_orthogonal_polynomial` (Algebra) |
| `𝓕(z) = Σ ρⁿ 2wⁿz/(z−wⁿ)³`, analytic at ∞, `= Σ ν_k z^{−k−1}` | `cauchyF`, `cauchyF_inv_eq`, `meromorphicAt_cauchyF_inv` (Cauchy) |
| `E_n = 𝓕Q_n − T_n = O(1/z)` (`T_n` is the polynomial part at ∞) | `cauchyPart`, `tendsto_cauchyPart_error` (Interp) |
| `E_n(x_a) = 0`, `1 ≤ a ≤ n` | `Ln_cofactor_mul`, `cauchyPart_interpolates` (Interp) |
| cubic poles at `wⁿ`; `𝓕` not rational | `cauchyF_cubic_pole`, `meromorphicOn_cauchyF_pos`, `cauchyF_nonrational` (Pole) |
| consecutive zeros give `T_n/Q_n = T_{n+1}/Q_{n+1}`; one reduced `T/Q`; `E = c z^{−h}(1+o(1))`; too many zeros of `U_n` | `no_tail_of_interpolants`, `exists_laurent_limit_of_meromorphic_inv` (Algebra) |

The nodes `x_a = w^{−a}` alternate in sign. So the normality algebra (adapted from the uplift) asks
only for `x_a⁻¹ → 0` through nonzero values. The error `E` is shown to be eventually nonzero near ∞
from its meromorphic germ (the uplift uses `x_a → +∞`). The rational-germ exclusion uses only the
positive poles `w^{2j+2}`, together with the identity theorem on `(0, ∞)`.

Files: `Algebra.lean` (normality argument), `Cauchy.lean` (𝓕 at ∞, node values), `Pole.lean` (poles,
nonrationality), `Interp.lean` (formal functional, interpolation), `Nonvanishing.lean` (assembly).
Numerical checks: `scripts/nonvan/check.py`. Each file takes about 20–35 s with `lake env lean`,
mostly the Mathlib import.
