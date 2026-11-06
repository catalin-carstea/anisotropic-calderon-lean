import Calderon.PhysicalDensityProductsConcreteSectionsModular
import Calderon.ActualFiniteHarmonicModelHorizontalProfileComparison
import Calderon.PhysicalDensityProductsFiniteCoreProjection
import Calderon.PhysicalDensityProductsConcreteWeightedSums
import Calderon.PhysicalDensityProductsPredicateTransport
import Calderon.PhysicalDensityProductsOperatorSmoothness
import Calderon.SupportedOperatorSection
import Calderon.PhysicalDensityProductsProfileOpenRoom
import Calderon.PhysicalDensityProductsFiniteCorePairing
import Calderon.PhysicalDensityProductsNegativeGraph
import Calderon.SphereSobolevHalfToL2
import Calderon.WeightedIntegralCongruence
import Calderon.SupportedOperatorSectionsOfPairing
import Calderon.PhysicalDensityProductsWeightedSumsSmoothness
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Generic integration argument, independent of the physical Products function.
Full upfront: /tmp/ProductsProfileConditionalAssembly-v003/UPFRONT.md.
Internal numerical prerequisites are discharged by actual producers at callers.
-/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsProfileIntegral
open SphereHarmonic

/-- Integrate a weighted pointwise profile estimate for an arbitrary compact field. -/
theorem integrable_weighted_norm_sq_and_integral_bound
    (density : R3 → ℝ) (V : R3 → SphereL2) (energy : R3 → ℝ) (B c : ℝ)
    (hDensity : Continuous density) (hDensity_nonneg : ∀ y, 0 ≤ density y)
    (hV : ContDiff ℝ ∞ V) (hVcompact : HasCompactSupport V)
    (hright : Integrable (fun y : R3 => c * (density y * energy y))
      (volume : Measure R3))
    (hpointwise : ∀ y : R3, B^9 * ‖V y‖^2 ≤ c * energy y) :
    Integrable (fun y : R3 => density y * ‖V y‖^2) (volume : Measure R3) ∧
      B^9 * (∫ y : R3, density y * ‖V y‖^2) ≤
        c * (∫ y : R3, density y * energy y) := by
  have hcV : Continuous V := ContDiff.continuous (f := V) hV
  have hcVsq : Continuous (fun y : R3 => ‖V y‖^2) := hcV.norm.pow 2
  have hsVsq : HasCompactSupport (fun y : R3 => ‖V y‖^2) := by
    have hs := hVcompact.comp_left (g := fun v : SphereL2 => ‖v‖^2) (by simp)
    exact hs
  have hcf : Continuous (fun y : R3 => density y * ‖V y‖^2) := hDensity.mul hcVsq
  have hsf : HasCompactSupport (fun y : R3 => density y * ‖V y‖^2) := hsVsq.mul_left
  have hfi : Integrable (fun y : R3 => density y * ‖V y‖^2)
      (volume : Measure R3) := hcf.integrable_of_hasCompactSupport hsf
  have hleft : Integrable (fun y : R3 => B^9 * (density y * ‖V y‖^2))
      (volume : Measure R3) :=
    (continuous_const.mul hcf).integrable_of_hasCompactSupport hsf.mul_left
  have hweighted : ∀ y : R3,
      B^9 * (density y * ‖V y‖^2) ≤ c * (density y * energy y) := by
    intro y
    calc
      _ = density y * (B^9 * ‖V y‖^2) := by ring
      _ ≤ density y * (c * energy y) :=
        mul_le_mul_of_nonneg_left (hpointwise y) (hDensity_nonneg y)
      _ = _ := by ring
  have hintegral := MeasureTheory.integral_mono hleft hright hweighted
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hintegral
  exact ⟨hfi, hintegral⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsProfileIntegral

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsProfileIntegral.integrable_weighted_norm_sq_and_integral_bound
