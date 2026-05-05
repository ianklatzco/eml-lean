# lean-eml

Lean 4 formalization of the EML (Exp-Minus-Log) operator from [Odrzywołek, "All Elementary Functions from a Single Operator"](https://arxiv.org/html/2603.21852v2).

## The EML Operator

A single binary operator + the constant 1 generates all elementary functions:

```
eml(x, y) = exp(x) - ln(y)
```

Analogous to NAND for Boolean logic — one primitive suffices for everything.

## Approach

The paper requires extended reals (`ln(0) = -∞`, `exp(-∞) = 0`), but Lean 4 requires total functions and Mathlib's `EReal.exp` maps to `ℝ≥0∞` rather than `EReal`.

We axiomatize `eexp : EReal → EReal` and `elog : EReal → EReal` with the properties the paper needs, then define `eml` concretely and prove identities from the axioms.

## What's proven

- `eml_recovers_exp`: `eml(x, 1) = exp(x)`
- `eml_zero`: `eml(0, y) = 1 - log(y)`
- `eml_one`: `eml(0, 1) = 1`
- `eml_compose_exp`: `eml(eml(a,1), 1) = exp(exp(a))`
- `eml_e`: `eml(eml(0,1), 1) = exp(1) = e`

## Building

```bash
lake update    # fetches mathlib + cache
lake build
```

## Status

Early stage. The deeper paper results (negation at depth 57, multiplication at depth 41) require chaining many nested eml calls and fighting EReal subtraction arithmetic.
