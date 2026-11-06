import Calderon.RegularizedInverseNormPotential
import Calderon.PrivateNewtonianDominatedConvergence
import Calderon.PrivateNewtonianRegularization
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ConnectionError

theorem tendsto_regularizedInverseNormPotential (c0 : ℝ) (z : R3) (hz : z ≠ 0) :
    Tendsto (fun t : ℝ => regularizedInverseNormPotential c0 t z) (𝓝[>] 0)
      (𝓝 (inverseNormPotential c0 z)) := by
  have h := (TauCeti.tendsto_sq_add_rpow (norm_ne_zero_iff.mpr hz) (-1/2 : ℝ)).const_mul c0
  change Tendsto (fun t : ℝ => regularizedInverseNormPotential c0 t z) (𝓝[>] 0)
    (𝓝 (regularizedInverseNormPotential c0 0 z)) at h
  rwa [regularizedInverseNormPotential_zero] at h

theorem abs_regularizedInverseNormPotential_le (c0 t : ℝ) (ht : 0 ≤ t)
    (z : R3) (hz : z ≠ 0) :
    |regularizedInverseNormPotential c0 t z| ≤ |inverseNormPotential c0 z| := by
  have h := TauCeti.sq_add_rpow_le (norm_ne_zero_iff.mpr hz) ht (show (-1/2 : ℝ) ≤ 0 by norm_num)
  have hNonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ (‖z‖^2+s)^(-1/2 : ℝ) :=
    Real.rpow_nonneg (add_nonneg (sq_nonneg _) hs) _
  have hZero : |regularizedInverseNormPotential c0 0 z| = |inverseNormPotential c0 z| :=
    congrArg abs (regularizedInverseNormPotential_zero c0 z)
  rw [← hZero]
  simp only [regularizedInverseNormPotential,abs_mul,abs_of_nonneg (hNonneg t ht),
    abs_of_nonneg (hNonneg 0 le_rfl)]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg c0)

theorem locallyIntegrable_inverseNormPotential (c0 : ℝ) :
    LocallyIntegrable (inverseNormPotential c0) (volume : Measure R3) := by
  apply locallyIntegrable_of_norm_le_rpow (μ := (volume : Measure R3))
    (show 1 ≤ Module.finrank ℝ R3 by norm_num [R3])
    (α := (1 : ℝ)) (C := |c0|) (by norm_num [R3])
  · exact Filter.Eventually.of_forall fun z => by
      simp only [inverseNormPotential,Real.norm_eq_abs,abs_div,abs_norm,
        Real.rpow_neg_one]
      exact le_of_eq (div_eq_mul_inv _ _)
  · exact (measurable_const.div measurable_norm).aestronglyMeasurable

theorem integrable_inverseNormPotential_mul_continuous_compact
    (c0 : ℝ) (w : R3 → ℝ) (hw : Continuous w) (hCompact : HasCompactSupport w) :
    Integrable (fun z : R3 => inverseNormPotential c0 z * w z) := by
  exact (locallyIntegrable_inverseNormPotential c0).integrable_smul_right_of_hasCompactSupport hw hCompact

theorem tendsto_integral_regularizedInverseNormPotential_mul_continuous_compact
    (c0 : ℝ) (w : R3 → ℝ) (hw : Continuous w) (hCompact : HasCompactSupport w) :
    Tendsto (fun t : ℝ => ∫ z : R3, regularizedInverseNormPotential c0 t z * w z)
      (𝓝[>] 0) (𝓝 (∫ z : R3, inverseNormPotential c0 z * w z)) := by
  apply TauCeti.tendsto_integral_mul_of_dominated_away (0 : R3) hw
    (K := fun t z => regularizedInverseNormPotential c0 t z)
    (K₀ := inverseNormPotential c0)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (contDiff_regularizedInverseNormPotential c0 t ht).continuous
  · exact integrable_inverseNormPotential_mul_continuous_compact c0 w hw hCompact
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact fun z hz => abs_regularizedInverseNormPotential_le c0 t ht.le z hz
  · exact fun z hz => tendsto_regularizedInverseNormPotential c0 z hz

end OAI.AnisotropicCalderon.ConnectionError
