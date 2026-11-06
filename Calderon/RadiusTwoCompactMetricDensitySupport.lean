import Calderon.RadiusTwoCompactMetricTestSource

/-! EXPANSION.json precedes literal support locality of the actual metric test density. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge MetricVolume

theorem radiusTwoCompactMetricTestDensity_eq_zero_of_notMem_tsupport
    (g : MatrixField) (hg : IsAdmissibleMetric g) (φ : 𝓓(radiusTwoOpens, ℝ))
    (x : R3) (hx : x ∉ tsupport (φ : R3 → ℝ)) :
    (radiusTwoCompactMetricTestDensity g hg φ).1 x = 0 := by
  have hFluxSupport (i : Fin 3) :
      tsupport (radiusTwoCompactMetricFlux g φ i) ⊆ tsupport (φ : R3 → ℝ) := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro y hy
    change radiusTwoCompactMetricFlux g φ i y ≠ 0 at hy
    by_contra hyφ
    have hD : fderiv ℝ (φ : R3 → ℝ) y = 0 := fderiv_of_notMem_tsupport ℝ hyφ
    exact hy (by simp only [radiusTwoCompactMetricFlux,hD,ContinuousLinearMap.zero_apply,mul_zero,Finset.sum_const_zero])
  change -(∑ i : Fin 3, fderiv ℝ (radiusTwoCompactMetricFlux g φ i) x (coordinateVector i)) = 0
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro i hi
  have hNot : x ∉ tsupport (radiusTwoCompactMetricFlux g φ i) := fun h => hx (hFluxSupport i h)
  rw [fderiv_of_notMem_tsupport ℝ hNot,ContinuousLinearMap.zero_apply]

theorem tsupport_radiusTwoCompactMetricTestDensity_subset
    (g : MatrixField) (hg : IsAdmissibleMetric g) (φ : 𝓓(radiusTwoOpens, ℝ)) :
    tsupport (radiusTwoCompactMetricTestDensity g hg φ).1 ⊆ tsupport (φ : R3 → ℝ) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  change (radiusTwoCompactMetricTestDensity g hg φ).1 x ≠ 0 at hx
  by_contra h
  exact hx (radiusTwoCompactMetricTestDensity_eq_zero_of_notMem_tsupport g hg φ x h)

end OAI.AnisotropicCalderon.ExteriorSource
