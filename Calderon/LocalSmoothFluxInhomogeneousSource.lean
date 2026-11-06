import Calderon.SmoothFluxCompactTestIntegration

/-! Full EXPANSION.json precedes this local inhomogeneous smooth-flux conversion. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ContDiff Distributions
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

theorem coordinateFluxRows_divergence_eq_neg_of_smooth_source_weakEquation
    (Omega : Opens R3) (J : Fin 3 → R3 → ℝ)
    (hJ : ∀ i : Fin 3, ContDiffOn ℝ ∞ (J i) (Omega : Set R3))
    (H : R3 → ℝ) (hH : ContDiffOn ℝ ∞ H (Omega : Set R3))
    (hWeak : ∀ phi : SmoothData, HasCompactSupport phi.1 →
      tsupport phi.1 ⊆ (Omega : Set R3) →
      (∫ x : R3, (∑ i : Fin 3, lineDeriv ℝ phi.1 x (coordinateVector i) * J i x)
        ∂(volume : Measure R3)) =
      ∫ x : R3, H x * phi.1 x ∂(volume : Measure R3)) :
    ∀ x ∈ (Omega : Set R3),
      (∑ i : Fin 3, fderiv ℝ (J i) x (coordinateVector i)) = -H x := by
  let D : R3 → ℝ := fun x => ∑ i : Fin 3, fderiv ℝ (J i) x (coordinateVector i)
  have hDi (i : Fin 3) : ContinuousOn
      (fun x => fderiv ℝ (J i) x (coordinateVector i)) (Omega : Set R3) :=
    ((hJ i).continuousOn_fderiv_of_isOpen Omega.isOpen (by simp)).clm_apply continuousOn_const
  have hD : ContinuousOn D (Omega : Set R3) :=
    continuousOn_finsetSum Finset.univ (fun i _ => hDi i)
  have hDH : ContinuousOn (fun x => D x + H x) (Omega : Set R3) := hD.add hH.continuousOn
  have hFundamental : ∀ᵐ x ∂(volume : Measure R3), x ∈ (Omega : Set R3) →
      D x + H x = 0 := by
    apply Omega.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hDH.locallyIntegrableOn Omega.isOpen.measurableSet)
    intro f hf hCompact hSupport
    let phi : 𝓓(Omega, ℝ) := ⟨f,hf,hCompact,hSupport⟩
    have hDInt : Integrable (fun x => f x * D x) (volume : Measure R3) := by
      simpa only [smul_eq_mul,phi,TestFunction.coe_mk] using
        TauCeti.integrable_smul_of_locallyIntegrableOn
          (hD.locallyIntegrableOn Omega.isOpen.measurableSet) phi
    have hHInt : Integrable (fun x => f x * H x) (volume : Measure R3) := by
      simpa only [smul_eq_mul,phi,TestFunction.coe_mk] using
        TauCeti.integrable_smul_of_locallyIntegrableOn
          (hH.continuousOn.locallyIntegrableOn Omega.isOpen.measurableSet) phi
    have hIBP :
        (∫ x : R3, (∑ i : Fin 3, lineDeriv ℝ f x (coordinateVector i) * J i x)
          ∂(volume : Measure R3)) =
          -(∫ x : R3, f x * D x ∂(volume : Measure R3)) := by
      simpa only [phi,TestFunction.coe_mk,D] using
        smoothFlux_compactTest_integration Omega J hJ phi
    have hSource :
        (∫ x : R3, (∑ i : Fin 3, lineDeriv ℝ f x (coordinateVector i) * J i x)
          ∂(volume : Measure R3)) =
          ∫ x : R3, f x * H x ∂(volume : Measure R3) := by
      have hW := hWeak ⟨f,hf⟩ hCompact hSupport
      simpa only [mul_comm] using hW
    simp only [smul_eq_mul]
    calc
      (∫ x : R3, f x * (D x + H x) ∂(volume : Measure R3)) =
          (∫ x : R3, f x * D x ∂(volume : Measure R3)) +
            ∫ x : R3, f x * H x ∂(volume : Measure R3) := by
        simp_rw [mul_add]
        exact integral_add hDInt hHInt
      _ = 0 := by linarith [hIBP,hSource]
  have hAE : (fun x => D x + H x)
      =ᵐ[(volume : Measure R3).restrict Omega] (fun _ => (0 : ℝ)) :=
    (ae_restrict_iff' Omega.isOpen.measurableSet).mpr hFundamental
  have hEq : EqOn (fun x => D x + H x) (fun _ => (0 : ℝ)) (Omega : Set R3) :=
    Measure.eqOn_open_of_ae_eq hAE Omega.isOpen hDH continuousOn_const
  intro x hx
  have hZero : D x + H x = 0 := hEq hx
  change D x = -H x
  linarith

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateFluxRows_divergence_eq_neg_of_smooth_source_weakEquation
