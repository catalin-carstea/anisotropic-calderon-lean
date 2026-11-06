import Calderon.RadiusTwoNativeSourceFoundation
import Calderon.MetricHessianDivergence

/-! EXPANSION.json precedes literal full-metric cutoff flux/divergence fields. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge MetricVolume

def smoothMetricCutoffFlux (g : MatrixField) (χ : SmoothData) (i : Fin 3) (x : R3) : ℝ :=
  ∑ j : Fin 3, principalCoefficient g x i j * fderiv ℝ χ.1 x (coordinateVector j)

theorem contDiff_smoothMetricCutoffFlux (g : MatrixField) (hg : IsAdmissibleMetric g)
    (χ : SmoothData) (i : Fin 3) : ContDiff ℝ ∞ (smoothMetricCutoffFlux g χ i) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ χ.1) := χ.2.fderiv_right (by simp)
  exact ContDiff.sum (fun j _ => (contDiff_principalCoefficient_entry g hg i j).mul
    (hD.clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => coordinateVector j))))

def smoothMetricCutoffFluxDivergence (g : MatrixField) (hg : IsAdmissibleMetric g)
    (χ : SmoothData) : SmoothData :=
  ⟨fun x => ∑ i : Fin 3, fderiv ℝ (smoothMetricCutoffFlux g χ i) x (coordinateVector i),by
    have hD (i : Fin 3) : ContDiff ℝ ∞ (fderiv ℝ (smoothMetricCutoffFlux g χ i)) :=
      (contDiff_smoothMetricCutoffFlux g hg χ i).fderiv_right (by simp)
    exact ContDiff.sum (fun i _ =>
      (hD i).clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => coordinateVector i)))⟩

theorem smoothMetricCutoffFlux_eq_gradient_sum (g : MatrixField) (χ : SmoothData)
    (i : Fin 3) (x : R3) :
    smoothMetricCutoffFlux g χ i x =
      ∑ j : Fin 3, principalCoefficient g x i j * (gradient χ.1 x : R3) j := by
  unfold smoothMetricCutoffFlux
  apply Finset.sum_congr rfl
  intro j hj
  rw [gradient_coordinate]

end OAI.AnisotropicCalderon.ExteriorSource
