import Calderon.ReferenceDensityBounds
import Calderon.ActualTwoMetricPhysicalVolumeNormalization
import Calderon.ActualMixedKernelGlobalSurfaceExtension
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConformalDepth ReferenceDensityBounds EnergyBridge ExteriorSource

/-- The genuine conformal reference metric has one positive volume-density
lower bound on the fixed parameter strip and original closed cylinder. -/
theorem exists_uniform_referenceMetric_volume_lower_on_cylinder
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) :
    ∃ m : ℝ, 0 < m ∧
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ y ∈ cylinder,
        m ≤ vol (referenceMetric (dilatedMetric g lam) L) y := by
  let K : Set (ℝ × R3) := Icc (0 : ℝ) 1 ×ˢ cylinder
  have hK : IsCompact K := isCompact_Icc.prod isCompact_native_center_cylinder
  have hCont : ContinuousOn (referenceDensityFamily g L) K :=
    (contDiff_referenceDensityFamily g hg L).continuous.continuousOn
  obtain ⟨m,hm,hLower⟩ := hK.exists_forall_le' hCont
    (fun z _ => referenceDensityFamily_pos g hg L z)
  refine ⟨m,hm,?_⟩
  intro lam hLam y hy
  change m ≤ referenceDensityFamily g L (lam,y)
  exact hLower (lam,y) ⟨hLam,hy⟩

/-- Euclidean base volume on the selected cylinder is uniformly dominated by
the actual conformal reference-metric volume after one fixed scalar factor. -/
theorem exists_uniform_Euclidean_restrict_le_referenceMetric_volume
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧
      ∀ lam ∈ Icc (0 : ℝ) 1,
        (volume : Measure R3).restrict cylinder ≤
          c • (radiusTwoMetricVolumeMeasure
            (referenceMetric (dilatedMetric g lam) L)).restrict cylinder := by
  obtain ⟨m,hm,hLower⟩ :=
    exists_uniform_referenceMetric_volume_lower_on_cylinder g hg L
  let c : ℝ≥0∞ := ENNReal.ofReal m⁻¹
  have hcFinite : c ≠ ⊤ := by simp [c]
  refine ⟨c,hcFinite,?_⟩
  intro lam hLam
  let d : R3 → ℝ := fun y => vol (referenceMetric (dilatedMetric g lam) L) y
  have hCyl : MeasurableSet (cylinder : Set R3) :=
    isCompact_native_center_cylinder.isClosed.measurableSet
  have hAE : (fun _ : R3 => (1 : ℝ≥0∞)) ≤ᵐ[(volume : Measure R3).restrict cylinder]
      (fun y => c * ENNReal.ofReal (d y)) := by
    filter_upwards [ae_restrict_mem hCyl] with y hy
    have hmd : m ≤ d y := hLower lam hLam y hy
    have hReal : 1 ≤ m⁻¹ * d y := by
      have hh := mul_le_mul_of_nonneg_left hmd (inv_nonneg.mpr hm.le)
      have hcancel : m⁻¹ * m = 1 := inv_mul_cancel₀ hm.ne'
      linarith
    have hENN := ENNReal.ofReal_le_ofReal hReal
    simpa [c, ENNReal.ofReal_mul (inv_nonneg.mpr hm.le)] using hENN
  have hM := withDensity_mono hAE
  have hRhs : ((volume : Measure R3).restrict cylinder).withDensity
        (fun y => c * ENNReal.ofReal (d y)) =
      c • (radiusTwoMetricVolumeMeasure
        (referenceMetric (dilatedMetric g lam) L)).restrict cylinder := by
    calc
      _ = ((volume : Measure R3).restrict cylinder).withDensity
          (c • fun y : R3 => ENNReal.ofReal (d y)) := by
            congr 1
      _ = c • ((volume : Measure R3).restrict cylinder).withDensity
          (fun y : R3 => ENNReal.ofReal (d y)) :=
        withDensity_smul' c _ hcFinite
      _ = _ := by
        rw [← restrict_withDensity hCyl]
        rfl
  simpa [hRhs] using hM

/-- The same fixed base-volume comparison controls every L² seminorm on the
selected cylinder; no sphere-fiber measure is identified here. -/
theorem exists_uniform_Euclidean_eLpNorm_le_referenceMetric_volume
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ lam ∈ Icc (0 : ℝ) 1,
        ∀ F : R3 → ℝ,
          eLpNorm F 2 ((volume : Measure R3).restrict cylinder) ≤
            C * eLpNorm F 2
              ((radiusTwoMetricVolumeMeasure
                (referenceMetric (dilatedMetric g lam) L)).restrict cylinder) := by
  obtain ⟨c,hc,hMeasure⟩ :=
    exists_uniform_Euclidean_restrict_le_referenceMetric_volume g hg L
  let C : ℝ≥0∞ := c ^ ((1 / (2 : ℝ≥0∞)).toReal)
  have hC : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hc
  refine ⟨C,hC,?_⟩
  intro lam hLam F
  simpa only [C, smul_eq_mul] using
    (eLpNorm_le_of_measure_le_smul (hMeasure lam hLam) (f := F) (p := (2 : ℝ≥0∞)))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
