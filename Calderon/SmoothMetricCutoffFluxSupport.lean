import Calderon.SmoothMetricCutoffFlux

/-! Full EXPANSION.json precedes actual full-Ag support locality. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge MetricVolume

theorem tsupport_smoothMetricCutoffFlux_subset
    (g : MatrixField) (η : SmoothData) (i : Fin 3) :
    tsupport (smoothMetricCutoffFlux g η i) ⊆ tsupport η.1 := by
  apply closure_minimal ?_ (isClosed_tsupport η.1)
  intro x hx
  by_contra hNot
  have hD := fderiv_of_notMem_tsupport ℝ hNot
  apply hx
  simp only [smoothMetricCutoffFlux,hD,ContinuousLinearMap.zero_apply,mul_zero,Finset.sum_const_zero]

theorem tsupport_smoothMetricCutoffFluxDivergence_subset
    (g : MatrixField) (hg : IsAdmissibleMetric g) (η : SmoothData) :
    tsupport (smoothMetricCutoffFluxDivergence g hg η).1 ⊆ tsupport η.1 := by
  apply closure_minimal ?_ (isClosed_tsupport η.1)
  intro x hx
  by_contra hNot
  apply hx
  change (∑ i : Fin 3, fderiv ℝ (smoothMetricCutoffFlux g η i) x (coordinateVector i)) = 0
  apply Finset.sum_eq_zero
  intro i hi
  have hJi : x ∉ tsupport (smoothMetricCutoffFlux g η i) :=
    fun h => hNot (tsupport_smoothMetricCutoffFlux_subset g η i h)
  rw [fderiv_of_notMem_tsupport ℝ hJi]
  rfl

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.tsupport_smoothMetricCutoffFlux_subset
#print axioms OAI.AnisotropicCalderon.ExteriorSource.tsupport_smoothMetricCutoffFluxDivergence_subset
