import Calderon.ActualNativeDensityWeightedLp
import Calderon.FiniteCoverSourceTaylorBounds
import Calderon.ProfileDivergence
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology Distributions
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource ConnectionError MetricVolume MetricOperator
  ConformalDepth ReferenceWeightedApproximation DirichletFamily.DriftBootstrap SphereHarmonic

/-- The covered actual moment bound supplies its scalar a.e. inputs on the cylinder. -/
theorem memLp_covered_native_source_moment_and_eLpNorm_le
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hPsi : ContDiff ℝ ∞ Psi) (hCompact : HasCompactSupport Psi)
    (μ : Measure R3) [IsFiniteMeasureOnCompacts μ]
    (chi F : R3 → ℝ) (hChi : Continuous chi) (hF : ContinuousOn F cylinder)
    (delta Rstar : ℝ) (p : ℕ) (hDelta : 0 < delta) (hRstar : 0 < Rstar)
    (C : ℝ) (hC : 0 ≤ C)
    (hMoment : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      |F y| ≤ C * (referenceRadius delta Rstar p L y)^2 *
        ‖(sphereSobolevZeroEquiv hO hD).symm
          (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖) :
    let w : R3 → SphereL2 := fun y => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))
    MemLp (fun y => chi y * F y / (referenceRadius delta Rstar p L y)^2)
      2 (μ.restrict cylinder) ∧
      eLpNorm (fun y => chi y * F y / (referenceRadius delta Rstar p L y)^2)
        2 (μ.restrict cylinder) ≤
        ENNReal.ofReal C * eLpNorm (fun y => chi y • w y) 2 (μ.restrict cylinder) := by
  have hCyl : MeasurableSet (cylinder : Set R3) :=
    isCompact_native_center_cylinder.isClosed.measurableSet
  have hRadius : Continuous (fun y : R3 => referenceRadius delta Rstar p L y) :=
    (contDiff_const.mul
      ((contDiff_softplus_comp delta (referenceDepth L) (contDiff_referenceDepth L)).pow p)).continuous
  have hScalar : ContinuousOn
      (fun y => chi y * F y / (referenceRadius delta Rstar p L y)^2) cylinder :=
    (hChi.continuousOn.mul hF).div (hRadius.pow 2).continuousOn
      (fun y _ => pow_ne_zero 2 (referenceRadius_pos delta Rstar p L y hDelta hRstar).ne')
  have hBound : ∀ᵐ y ∂μ.restrict cylinder,
      |F y| ≤ C * (referenceRadius delta Rstar p L y)^2 *
        ‖(sphereSobolevZeroEquiv hO hD).symm
          (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖ := by
    filter_upwards [ae_restrict_mem hCyl] with y hy
    obtain ⟨i,hi⟩ := cover.covers_cylinder y hy
    exact hMoment i y ⟨hy,hi⟩
  exact memLp_weighted_native_source_moment_and_eLpNorm_le
    hO hD Psi hPsi hCompact (μ.restrict cylinder) chi hChi F
    (fun y => referenceRadius delta Rstar p L y) C hC
    (hScalar.aestronglyMeasurable hCyl)
    (Filter.Eventually.of_forall (fun y => referenceRadius_pos delta Rstar p L y hDelta hRstar))
    hBound

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
