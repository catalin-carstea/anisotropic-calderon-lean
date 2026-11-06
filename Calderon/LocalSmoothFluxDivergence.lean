import Calderon.PositiveCoefficientInnerClassicalWeakEquation
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Actual local scalar flux integration by parts.
The generic weak-test condition is discharged by the actual solver in the next specialization. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace Topology Distributions
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

theorem lineDeriv_smoothData_coordinate_eq_gradient
    (φ : SmoothData) (x : R3) (i : Fin 3) :
    lineDeriv ℝ φ.1 x (coordinateVector i) = (gradient φ.1 x : R3) i := by
  have hd : DifferentiableAt ℝ φ.1 x := φ.2.differentiable (by simp) x
  rw [hd.lineDeriv_eq_fderiv,hd.hasGradientAt.fderiv_apply]
  simpa only [coordinateVector,EuclideanSpace.basisFun_apply] using
    EuclideanSpace.inner_basisFun_real (Fin 3) (gradient φ.1 x : R3) i

theorem coordinateFluxRows_divergence_zero_of_smooth_weakEquation
    (Ω : Opens R3) (F : Fin 3 → R3 → ℝ)
    (hF : ∀ i : Fin 3, ContDiffOn ℝ ∞ (F i) Ω)
    (hWeak : ∀ φ : SmoothData, HasCompactSupport φ.1 → tsupport φ.1 ⊆ (Ω : Set R3) →
      ∫ x : R3, (∑ i : Fin 3, lineDeriv ℝ φ.1 x (coordinateVector i) * F i x)
        ∂(volume : Measure R3) = 0) :
    ∀ x ∈ (Ω : Set R3), ∑ i : Fin 3, fderiv ℝ (F i) x (coordinateVector i) = 0 := by
  have hCont (i : Fin 3) : ContinuousOn (fun x => fderiv ℝ (F i) x (coordinateVector i)) Ω :=
    ((hF i).continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply continuousOn_const
  have hDcont : ContinuousOn (fun x => ∑ i : Fin 3,
      fderiv ℝ (F i) x (coordinateVector i)) Ω :=
    continuousOn_finsetSum Finset.univ (fun i _ => hCont i)
  have hClassical (i : Fin 3) : TauCeti.HasWeakFDerivOn (volume : Measure R3) Ω
      (F i) (fderiv ℝ (F i)) :=
    TauCeti.hasWeakFDerivOn_of_differentiableOn
      ((hF i).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
      (((hF i).continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).locallyIntegrableOn
        Ω.isOpen.measurableSet)
      (fun x hx => ((hF i).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp))
  have hFundamental : ∀ᵐ x ∂(volume : Measure R3), x ∈ (Ω : Set R3) →
      (∑ i : Fin 3, fderiv ℝ (F i) x (coordinateVector i)) = 0 := by
    apply Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hDcont.locallyIntegrableOn Ω.isOpen.measurableSet)
    intro g hg hCompact hSupport
    let φ : 𝓓(Ω, ℝ) := ⟨g,hg,hCompact,hSupport⟩
    have hLeftInt (i : Fin 3) : Integrable
        (fun x => lineDeriv ℝ g x (coordinateVector i) * F i x) (volume : Measure R3) := by
      simpa only [smul_eq_mul,φ,TestFunction.coe_mk] using
        TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
          ((hClassical i (coordinateVector i)).locallyIntegrableOn) φ (coordinateVector i)
    have hRightInt (i : Fin 3) : Integrable
        (fun x => g x * fderiv ℝ (F i) x (coordinateVector i)) (volume : Measure R3) := by
      simpa only [smul_eq_mul,φ,TestFunction.coe_mk] using
        TauCeti.integrable_smul_of_locallyIntegrableOn
          ((hClassical i (coordinateVector i)).locallyIntegrableOn_deriv) φ
    have hIbP (i : Fin 3) :
        (∫ x, lineDeriv ℝ g x (coordinateVector i) * F i x ∂(volume : Measure R3)) =
          -(∫ x, g x * fderiv ℝ (F i) x (coordinateVector i) ∂(volume : Measure R3)) := by
      simpa only [smul_eq_mul,φ,TestFunction.coe_mk] using
        (hClassical i (coordinateVector i)).integral_lineDeriv_smul_eq_neg_integral_smul φ
    have hReverse (i : Fin 3) :
        (∫ x, g x * fderiv ℝ (F i) x (coordinateVector i) ∂(volume : Measure R3)) =
          -(∫ x, lineDeriv ℝ g x (coordinateVector i) * F i x ∂(volume : Measure R3)) := by
      linarith [hIbP i]
    have hLeftSum :
        (∫ x, (∑ i : Fin 3, lineDeriv ℝ g x (coordinateVector i) * F i x)
          ∂(volume : Measure R3)) =
        ∑ i : Fin 3, ∫ x, lineDeriv ℝ g x (coordinateVector i) * F i x ∂(volume : Measure R3) :=
      integral_finsetSum Finset.univ (fun i _ => hLeftInt i)
    have hRightSum :
        (∫ x, g x * (∑ i : Fin 3, fderiv ℝ (F i) x (coordinateVector i))
          ∂(volume : Measure R3)) =
        ∑ i : Fin 3, ∫ x, g x * fderiv ℝ (F i) x (coordinateVector i) ∂(volume : Measure R3) := by
      simp_rw [Finset.mul_sum]
      exact integral_finsetSum Finset.univ (fun i _ => hRightInt i)
    have hZero : (∑ i : Fin 3, ∫ x, lineDeriv ℝ g x (coordinateVector i) * F i x
        ∂(volume : Measure R3)) = 0 :=
      hLeftSum.symm.trans (hWeak ⟨g,hg⟩ hCompact hSupport)
    simp only [smul_eq_mul]
    calc
      _ = ∑ i : Fin 3, ∫ x, g x * fderiv ℝ (F i) x (coordinateVector i)
          ∂(volume : Measure R3) := hRightSum
      _ = -(∑ i : Fin 3, ∫ x, lineDeriv ℝ g x (coordinateVector i) * F i x
          ∂(volume : Measure R3)) := by
        simp_rw [hReverse]
        rw [Finset.sum_neg_distrib]
      _ = 0 := by rw [hZero,neg_zero]
  have hAE : (fun x => ∑ i : Fin 3, fderiv ℝ (F i) x (coordinateVector i))
      =ᵐ[(volume : Measure R3).restrict Ω] (fun _ => (0 : ℝ)) :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).mpr hFundamental
  exact Measure.eqOn_open_of_ae_eq hAE Ω.isOpen hDcont continuousOn_const

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.lineDeriv_smoothData_coordinate_eq_gradient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateFluxRows_divergence_zero_of_smooth_weakEquation
