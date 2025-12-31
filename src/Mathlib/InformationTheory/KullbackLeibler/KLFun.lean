import VerifiedAgora.tagger
/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# The real function `fun x ↦ x * log x + 1 - x`

We define `klFun x = x * log x + 1 - x`. That function is notable because the Kullback-Leibler
divergence is an f-divergence for `klFun`. That is, the Kullback-Leibler divergence is an integral
of `klFun` composed with a Radon-Nikodym derivative.

For probability measures, any function `f` that differs from `klFun` by an affine function of the
form `x ↦ a * (x - 1)` would give the same value for the integral
`∫ x, f (μ.rnDeriv ν x).toReal ∂ν`.
However, `klFun` is the particular choice among those that satisfies `klFun 1 = 0` and
`deriv klFun 1 = 0`, which ensures that desirable properties of the Kullback-Leibler divergence
extend to other finite measures: it is nonnegative and zero iff the two measures are equal.

## Main definitions

* `klFun`: the function `fun x : ℝ ↦ x * log x + 1 - x`.

This is a continuous nonnegative, strictly convex function on [0,∞), with minimum value 0 at 1.

## Main statements

* `integrable_klFun_rnDeriv_iff`: For two finite measures `μ ≪ ν`, the function
  `x ↦ klFun (μ.rnDeriv ν x).toReal` is integrable with respect to `ν` iff the log-likelihood ratio
  `llr μ ν` is integrable with respect to `μ`.
* `integral_klFun_rnDeriv`: For two finite measures `μ ≪ ν` such that `llr μ ν` is integrable with
  respect to `μ`,
  `∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν = ∫ x, llr μ ν x ∂μ + (ν univ).toReal - (μ univ).toReal`.

-/

open Real MeasureTheory Filter Set

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {x : ℝ}

/-- The function `x : ℝ ↦ x * log x + 1 - x`.
The Kullback-Leibler divergence is an f-divergence for this function. -/
noncomputable def klFun (x : ℝ) : ℝ := x * log x + 1 - x

@[target]
lemma klFun_apply (x : ℝ) : klFun x = x * log x + 1 - x := by sorry

lemma klFun_zero : klFun 0 = 1 := by simp [klFun]

@[target]
lemma klFun_one : klFun 1 = 0 := by sorry

/-- `klFun` is strictly convex on [0,∞). -/
lemma strictConvexOn_klFun : StrictConvexOn ℝ (Ici 0) klFun :=
  (strictConvexOn_mul_log.add_convexOn (convexOn_const _ (convex_Ici _))).sub_concaveOn
    (concaveOn_id (convex_Ici _))

/-- `klFun` is convex on [0,∞). -/
lemma convexOn_klFun : ConvexOn ℝ (Ici 0) klFun := strictConvexOn_klFun.convexOn

/-- `klFun` is convex on (0,∞).
This is an often useful consequence of `convexOn_klFun`, which states convexity on [0, ∞). -/
@[target]
lemma convexOn_Ioi_klFun : ConvexOn ℝ (Ioi 0) klFun := by sorry

/-- `klFun` is continuous. -/
@[continuity, fun_prop]
lemma continuous_klFun : Continuous klFun := by unfold klFun; fun_prop

/-- `klFun` is measurable. -/
@[target, measurability, fun_prop]
lemma measurable_klFun : Measurable klFun := by sorry

/-- `klFun` is strongly measurable. -/
@[measurability]
lemma stronglyMeasurable_klFun : StronglyMeasurable klFun := measurable_klFun.stronglyMeasurable

section Derivatives

/-- The derivative of `klFun` at `x ≠ 0` is `log x`. -/
lemma hasDerivAt_klFun (hx : x ≠ 0) : HasDerivAt klFun (log x) x := by
  convert ((hasDerivAt_mul_log hx).add (hasDerivAt_const x 1)).sub (hasDerivAt_id x) using 1
  ring

lemma not_differentiableAt_klFun_zero : ¬ DifferentiableAt ℝ klFun 0 := by
  unfold klFun; simpa using not_DifferentiableAt_log_mul_zero

/-- The derivative of `klFun` is `log x`. This also holds at `x = 0` although `klFun` is not
differentiable there since the default value of `deriv` in that case is 0. -/
@[target, simp]
lemma deriv_klFun : deriv klFun = log := by sorry

@[target]
lemma not_differentiableWithinAt_klFun_Ioi_zero : ¬ DifferentiableWithinAt ℝ klFun (Ioi 0) 0 := by sorry

@[target]
lemma not_differentiableWithinAt_klFun_Iio_zero : ¬ DifferentiableWithinAt ℝ klFun (Iio 0) 0 := by sorry

/-- The right derivative of `klFun` is `log x`. This also holds at `x = 0` although `klFun` is not
differentiable there since the default value of `derivWithin` in that case is 0. -/
@[target, simp]
lemma rightDeriv_klFun : derivWithin klFun (Ioi x) x = log x := by sorry

/-- The left derivative of `klFun` is `log x`. This also holds at `x = 0` although `klFun` is not
differentiable there since the default value of `derivWithin` in that case is 0. -/
@[target, simp]
lemma leftDeriv_klFun : derivWithin klFun (Iio x) x = log x := by sorry

lemma rightDeriv_klFun_one : derivWithin klFun (Ioi 1) 1 = 0 := by simp

lemma leftDeriv_klFun_one : derivWithin klFun (Iio 1) 1 = 0 := by simp

@[target]
lemma tendsto_rightDeriv_klFun_atTop :
    Tendsto (fun x ↦ derivWithin klFun (Ioi x) x) atTop atTop := by sorry

end Derivatives

@[target]
lemma isMinOn_klFun : IsMinOn klFun (Ici 0) 1 := by sorry

/-- The function `klFun` is nonnegative on `[0,∞)`. -/
@[target]
lemma klFun_nonneg (hx : 0 ≤ x) : 0 ≤ klFun x := by sorry

@[target]
lemma klFun_eq_zero_iff (hx : 0 ≤ x) : klFun x = 0 ↔ x = 1 := by sorry

lemma tendsto_klFun_atTop : Tendsto klFun atTop atTop := by
  have : klFun = (fun x ↦ x * (log x - 1) + 1) := by unfold klFun; ext; ring
  rw [this]
  refine Tendsto.atTop_add ?_ tendsto_const_nhds
  refine tendsto_id.atTop_mul_atTop₀ ?_
  exact tendsto_log_atTop.atTop_add tendsto_const_nhds

section Integral

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- For two finite measures `μ ≪ ν`, the function `x ↦ klFun (μ.rnDeriv ν x).toReal` is integrable
with respect to `ν` iff `llr μ ν` is integrable with respect to `μ`. -/
@[target]
lemma integrable_klFun_rnDeriv_iff (hμν : μ ≪ ν) :
    Integrable (fun x ↦ klFun (μ.rnDeriv ν x).toReal) ν ↔ Integrable (llr μ ν) μ := by sorry

@[target]
lemma integral_klFun_rnDeriv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν
      = ∫ x, llr μ ν x ∂μ + (ν univ).toReal - (μ univ).toReal := by sorry

end Integral

end InformationTheory
