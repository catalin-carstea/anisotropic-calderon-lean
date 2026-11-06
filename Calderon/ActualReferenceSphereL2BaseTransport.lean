import Calderon.ActualReferenceMetricVolumeComparison
import Calderon.SphereSobolevInclusion
import Calderon.WeightedBaseSpectral

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic ExteriorSource WeightedBaseSpectral ConformalDepth

/-- The selected fixed-frame weighted-base measure is literally the volume
measure of the conformal reference metric. -/
theorem referenceBaseMeasure_eq_radiusTwoMetricVolumeMeasure
    (g : MatrixField) (L lam : ℝ) :
    referenceBaseMeasure g L lam =
      radiusTwoMetricVolumeMeasure (referenceMetric (dilatedMetric g lam) L) := by
  rfl

/-- One fixed base-volume constant controls the actual fixed-frame sphere L²
field on the original cylinder, uniformly over the dilation parameter. -/
theorem exists_uniform_Euclidean_sphereL2_eLpNorm_le_referenceMetric_volume
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ U : R3 → SphereL2,
        eLpNorm U 2 ((volume : Measure R3).restrict cylinder) ≤
          C * eLpNorm U 2
            ((radiusTwoMetricVolumeMeasure
              (referenceMetric (dilatedMetric g lam) L)).restrict cylinder) := by
  obtain ⟨c, hc, hMeasure⟩ :=
    exists_uniform_Euclidean_restrict_le_referenceMetric_volume g hg L
  let C : ℝ≥0∞ := c ^ ((1 / (2 : ℝ≥0∞)).toReal)
  have hC : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hc
  refine ⟨C, hC, ?_⟩
  intro lam hLam U
  simpa only [C, smul_eq_mul] using
    (eLpNorm_le_of_measure_le_smul (hMeasure lam hLam) (f := U) (p := (2 : ℝ≥0∞)))

/-- The source-matched cutoff times the *same* H⁰ density field used by the
five-source H8 consumer obeys the preceding fixed-frame base comparison. -/
theorem exists_uniform_Euclidean_cutoff_density_eLpNorm_le_referenceMetric_volume
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ chi : R3 → ℝ,
        ∀ Psi : R3 → SphereSobolev (3/2 : ℝ),
        eLpNorm (fun y : R3 => chi y •
          (sphereSobolevZeroEquiv hO hD).symm
            (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)))
          2 ((volume : Measure R3).restrict cylinder) ≤
          C * eLpNorm (fun y : R3 => chi y •
            (sphereSobolevZeroEquiv hO hD).symm
              (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)))
            2 ((radiusTwoMetricVolumeMeasure
              (referenceMetric (dilatedMetric g lam) L)).restrict cylinder) := by
  obtain ⟨C, hC, hAll⟩ :=
    exists_uniform_Euclidean_sphereL2_eLpNorm_le_referenceMetric_volume g hg L
  refine ⟨C, hC, ?_⟩
  intro lam hLam chi Psi
  exact hAll lam hLam _

/-- For the actual smooth compact density and the same source-matched cutoff,
the reference base seminorm is the norm of the already selected weighted-base
`Lp SphereL2` lift.  The comparison constant was chosen before lambda. -/
theorem exists_uniform_cutoff_density_Euclidean_le_referenceBaseLift
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ chi : R3 → ℝ,
        Continuous chi → HasCompactSupport chi →
        ∀ Psi : R3 → SphereSobolev (3/2 : ℝ),
          ContDiff ℝ ∞ Psi →
          let V : R3 → SphereL2 := fun y => chi y •
            (sphereSobolevZeroEquiv hO hD).symm
              (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))
          ∃ hV : Continuous V, ∃ hVc : HasCompactSupport V,
            eLpNorm V 2 ((volume : Measure R3).restrict cylinder) ≤
              C * ‖referenceBaseLift g hg L lam V hV hVc‖ₑ := by
  obtain ⟨C, hC, hAll⟩ :=
    exists_uniform_Euclidean_sphereL2_eLpNorm_le_referenceMetric_volume g hg L
  refine ⟨C, hC, ?_⟩
  intro lam hLam chi hChi hChiCompact Psi hPsi V
  have hH0 : Continuous (fun y : R3 =>
      (sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))) :=
    (sphereSobolevZeroEquiv hO hD).symm.continuous.comp
      ((sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)).continuous.comp
        hPsi.continuous)
  have hV : Continuous V := hChi.smul hH0
  have hVc : HasCompactSupport V := hChiCompact.smul_right
  refine ⟨hV, hVc, ?_⟩
  have hMeasure : referenceBaseMeasure g L lam =
      radiusTwoMetricVolumeMeasure (referenceMetric (dilatedMetric g lam) L) :=
    referenceBaseMeasure_eq_radiusTwoMetricVolumeMeasure g L lam
  have hNorm : eLpNorm V 2 (referenceBaseMeasure g L lam) =
      ‖referenceBaseLift g hg L lam V hV hVc‖ₑ := by
    exact (Lp.enorm_toLp (memLp_referenceBase g hg L lam V hV hVc)).symm
  calc
    eLpNorm V 2 ((volume : Measure R3).restrict cylinder) ≤
        C * eLpNorm V 2
          ((radiusTwoMetricVolumeMeasure
            (referenceMetric (dilatedMetric g lam) L)).restrict cylinder) :=
      hAll lam hLam V
    _ ≤ C * eLpNorm V 2
          (radiusTwoMetricVolumeMeasure
            (referenceMetric (dilatedMetric g lam) L)) := by
      gcongr
      exact Measure.restrict_le_self
    _ = C * ‖referenceBaseLift g hg L lam V hV hVc‖ₑ := by
      rw [← hMeasure, hNorm]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
