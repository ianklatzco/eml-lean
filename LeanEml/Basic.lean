import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# EML: Exp-Minus-Log

A single binary operator that generates all elementary functions.
Based on: Odrzywołek, "All Elementary Functions from a Single Operator" (arXiv:2603.21852v2)

## Approach

We axiomatize extended-real exp and log with the properties the paper needs:
  - exp(-∞) = 0,  exp(∞) = ∞
  - log(0) = -∞,  log(∞) = ∞
  - exp(log(x)) = x for x > 0
  - log(exp(x)) = x

Then define eml(x, y) = exp(x) - log(y) and derive the paper's results.

We use `EReal` as the carrier but axiomatize our own exp/log on it,
since Mathlib's `EReal.exp` maps to `ℝ≥0∞` rather than `EReal`.
-/

noncomputable section

open Real EReal

/-! ### Axiomatized extended exp and log -/

/-- Extended exponential: EReal → EReal -/
axiom eexp : EReal → EReal

/-- Extended logarithm: EReal → EReal -/
axiom elog : EReal → EReal

-- Core properties
axiom eexp_bot : eexp ⊥ = (0 : EReal)
axiom eexp_top : eexp ⊤ = (⊤ : EReal)
axiom eexp_coe (x : ℝ) : eexp (x : EReal) = (Real.exp x : ℝ)

axiom elog_zero : elog (0 : EReal) = ⊥
axiom elog_top : elog (⊤ : EReal) = ⊤
axiom elog_coe {x : ℝ} (hx : 0 < x) : elog (x : EReal) = (Real.log x : ℝ)
axiom elog_one : elog (1 : EReal) = (0 : EReal)
axiom eexp_zero : eexp (0 : EReal) = (1 : EReal)

-- Inverse relationship
axiom elog_eexp (x : EReal) : elog (eexp x) = x
axiom eexp_elog {x : EReal} (hx : (0 : EReal) < x) : eexp (elog x) = x

/-! ### The EML operator -/

/-- The EML operator: eml(x, y) = eexp(x) - elog(y) -/
def eml (x y : EReal) : EReal := eexp x - elog y

/-! ### Recovering exp and log from eml -/

/-- exp(x) = eml(x, 1) -/
theorem eml_recovers_exp (x : EReal) : eml x 1 = eexp x := by
  simp [eml, elog_one, sub_zero]

/-- eml(0, y) = 1 - log(y), i.e. log is embedded in eml -/
theorem eml_zero (y : EReal) : eml 0 y = 1 - elog y := by
  simp [eml, eexp_zero]

/-- eml(0, 1) = 1 -/
theorem eml_one : eml 0 1 = (1 : EReal) := by
  simp [eml, elog_one, sub_zero, eexp_zero]

/-! ### Composing EML

The paper's key constructions:
- Negation: neg(x) requires depth ~57 in RPN
- Addition/multiplication: built from nested eml calls
- For now we prove simpler composition identities.
-/

/-- Composing eml: eml(eml(a,1), 1) = eexp(eexp(a)) since log(1)=0 -/
theorem eml_compose_exp (a : EReal) : eml (eml a 1) 1 = eexp (eexp a) := by
  simp [eml, elog_one, sub_zero]

/-- The constant e from eml: e = eml(eml(0,1), 1) = eexp(1) -/
theorem eml_e : eml (eml 0 1) 1 = eexp 1 := by
  rw [eml_one]
  simp [eml, elog_one, sub_zero]

end
