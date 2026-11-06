import Calderon.LocalSmoothFluxDivergence

/-! EXPANSION.json precedes the literal compact-test flux integration identity. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ContDiff Distributions
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open MetricVolume
open EnergyBridge

theorem smoothFlux_compactTest_integration
    (Ω : Opens R3) (J : Fin 3 → R3 → ℝ)
    (hJ : ∀ i : Fin 3, ContDiffOn ℝ ∞ (J i) Ω) (φ : 𝓓(Ω, ℝ)) :
    (∫ x : R3, (∑ i : Fin 3, lineDeriv ℝ (φ : R3 → ℝ) x (coordinateVector i) * J i x)
      ∂(volume : Measure R3)) =
        -(∫ x : R3, φ x * (∑ i : Fin 3, fderiv ℝ (J i) x (coordinateVector i))
          ∂(volume : Measure R3)) := by
  have hClassical (i : Fin 3) : TauCeti.HasWeakFDerivOn (volume : Measure R3) Ω
      (J i) (fderiv ℝ (J i)) :=
    TauCeti.hasWeakFDerivOn_of_differentiableOn
      ((hJ i).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
      (((hJ i).continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).locallyIntegrableOn
        Ω.isOpen.measurableSet)
      (fun x hx => ((hJ i).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp))
  have hLeftInt (i : Fin 3) : Integrable
      (fun x => lineDeriv ℝ (φ : R3 → ℝ) x (coordinateVector i) * J i x)
      (volume : Measure R3) := by
    simpa only [smul_eq_mul] using
      TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
        ((hClassical i (coordinateVector i)).locallyIntegrableOn) φ (coordinateVector i)
  have hRightInt (i : Fin 3) : Integrable
      (fun x => φ x * fderiv ℝ (J i) x (coordinateVector i)) (volume : Measure R3) := by
    simpa only [smul_eq_mul] using
      TauCeti.integrable_smul_of_locallyIntegrableOn
        ((hClassical i (coordinateVector i)).locallyIntegrableOn_deriv) φ
  have hIbP (i : Fin 3) :
      (∫ x, lineDeriv ℝ (φ : R3 → ℝ) x (coordinateVector i) * J i x
        ∂(volume : Measure R3)) =
          -(∫ x, φ x * fderiv ℝ (J i) x (coordinateVector i) ∂(volume : Measure R3)) := by
    simpa only [smul_eq_mul] using
      (hClassical i (coordinateVector i)).integral_lineDeriv_smul_eq_neg_integral_smul φ
  have hLeftSum :
      (∫ x, (∑ i : Fin 3, lineDeriv ℝ (φ : R3 → ℝ) x (coordinateVector i) * J i x)
        ∂(volume : Measure R3)) =
      ∑ i : Fin 3, ∫ x, lineDeriv ℝ (φ : R3 → ℝ) x (coordinateVector i) * J i x
        ∂(volume : Measure R3) := integral_finsetSum Finset.univ (fun i _ => hLeftInt i)
  have hRightSum :
      (∫ x, φ x * (∑ i : Fin 3, fderiv ℝ (J i) x (coordinateVector i))
        ∂(volume : Measure R3)) =
      ∑ i : Fin 3, ∫ x, φ x * fderiv ℝ (J i) x (coordinateVector i)
        ∂(volume : Measure R3) := by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum Finset.univ (fun i _ => hRightInt i)
  rw [hLeftSum,hRightSum]
  simp_rw [hIbP]
  rw [Finset.sum_neg_distrib]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
