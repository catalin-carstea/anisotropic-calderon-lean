import Calderon.RadiusTwoNativeSourceFoundation

/-! EXPANSION.json precedes the actual compact metric-test divergence density. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open MetricVolume
open EnergyBridge

def radiusTwoCompactMetricFlux (g : MatrixField) (ψ : 𝓓(radiusTwoOpens, ℝ))
    (i : Fin 3) (x : R3) : ℝ :=
  ∑ j : Fin 3, principalCoefficient g x i j *
    fderiv ℝ (ψ : R3 → ℝ) x (coordinateVector j)

theorem contDiff_radiusTwoCompactMetricFlux (g : MatrixField) (hg : IsAdmissibleMetric g)
    (ψ : 𝓓(radiusTwoOpens, ℝ)) (i : Fin 3) :
    ContDiff ℝ ∞ (radiusTwoCompactMetricFlux g ψ i) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ (ψ : R3 → ℝ)) :=
    ψ.contDiff.fderiv_right (by simp)
  exact ContDiff.sum (fun j _ =>
    (contDiff_principalCoefficient_entry g hg i j).mul
      (hD.clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => coordinateVector j))))

def radiusTwoCompactMetricTestDensity (g : MatrixField) (hg : IsAdmissibleMetric g)
    (ψ : 𝓓(radiusTwoOpens, ℝ)) : SmoothData :=
  ⟨fun x => -(∑ i : Fin 3, fderiv ℝ (radiusTwoCompactMetricFlux g ψ i) x (coordinateVector i)),by
    have hD (i : Fin 3) : ContDiff ℝ ∞ (fderiv ℝ (radiusTwoCompactMetricFlux g ψ i)) :=
      (contDiff_radiusTwoCompactMetricFlux g hg ψ i).fderiv_right (by simp)
    exact (ContDiff.sum (fun i _ =>
      (hD i).clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => coordinateVector i)))).neg⟩

end OAI.AnisotropicCalderon.ExteriorSource
