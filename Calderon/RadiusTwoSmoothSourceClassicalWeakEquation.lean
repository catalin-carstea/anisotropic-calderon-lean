import Calderon.RadiusTwoSmoothSourceClassicalGradient
import Calderon.NativePrincipalEnergyGradientForm
import Calderon.RadiusTwoNativeTestDilation

/-! Full EXPANSION.json precedes the actual-source classical compact-test equation. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff InnerProductSpace Gradient Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution

lemma exists_radiusTwoSmoothSource_classical_weakEquation_innerBall
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (H : SmoothData)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ G : R3 → ℝ, Continuous G ∧ ContDiffOn ℝ ∞ G (ball (0 : R3) (2*a)) ∧
      ((TauCeti.W1p.value (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing H) : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) (2*a))] G) ∧
      ∀ phi : SmoothData, HasCompactSupport phi.1 →
        tsupport phi.1 ⊆ ball (0 : R3) (2*a) →
        (∫ x : R3, TauCeti.PDE.matrixBilinearForm (principalCoefficient g x)
          (gradient phi.1 x) (gradient G x) ∂(volume : Measure R3)) =
          ∫ x : R3, H.1 x * phi.1 x ∂(volume : Measure R3) := by
  obtain ⟨G,hG,hSmooth,hValue,hGradient⟩ :=
    exists_radiusTwoSmoothSource_valueGradient_innerBall hreg hcalc g hg H a ha ha1
  refine ⟨G,hG,hSmooth,hValue,?_⟩
  intro phi hCompact hSupport
  have hSub : ball (0 : R3) (2*a) ⊆ (radiusTwoOpens : Set R3) := by
    change ball (0 : R3) (2*a) ⊆ ball (0 : R3) 2
    exact ball_subset_ball (by linarith)
  let psi : 𝓓(radiusTwoOpens, ℝ) := ⟨phi.1,phi.2,hCompact,hSupport.trans hSub⟩
  let v : RadiusTwoH1Zero := nativeZeroTestLinear radiusTwoOpens psi
  have hTestGradient : (TauCeti.W1p.gradient (v : RadiusTwoH1) : R3 → R3)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] gradient phi.1 := by
    filter_upwards [TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 psi] with x hx
    simpa only [v,nativeZeroTestLinear_coe,TauCeti.W1p.gradient_ofTestFunctionₗ,
      psi,TestFunction.coe_mk] using hx
  have hTestValue : (TauCeti.W1p.value (v : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] phi.1 := by
    filter_upwards [TauCeti.testFunctionLp_apply_ae (mu := volume) 2 psi] with x hx
    simpa only [v,nativeZeroTestLinear_coe,TauCeti.W1p.value_ofTestFunctionₗ,
      psi,TestFunction.coe_mk] using hx
  have hGradGlobal : ∀ᵐ x ∂(volume : Measure R3), x ∈ ball (0 : R3) (2*a) →
      TauCeti.W1p.gradient
        (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing H) : RadiusTwoH1) x = gradient G x :=
    (ae_restrict_iff' isOpen_ball.measurableSet).mp hGradient
  have hZeroOutside (x : R3) (hx : x ∉ ball (0 : R3) (2*a)) : gradient phi.1 x = 0 := by
    have hNot : x ∉ tsupport phi.1 := fun hs => hx (hSupport hs)
    have hD : fderiv ℝ phi.1 x = 0 := fderiv_of_notMem_tsupport ℝ hNot
    simp only [gradient,hD,map_zero]
  let d : R3 → ℝ := fun x => TauCeti.PDE.matrixBilinearForm (principalCoefficient g x)
    (gradient phi.1 x) (gradient G x)
  have hEnergy : TauCeti.PDE.energyFormH1 (principalCoefficient g)
      (0 : R3 → R3) (0 : R3 → ℝ)
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing H) : RadiusTwoH1) (v : RadiusTwoH1) =
      ∫ x in radiusTwoOpens, d x ∂(volume : Measure R3) := by
    rw [nativePrincipalEnergy_eq_gradient_setIntegral]
    apply integral_congr_ae
    filter_upwards [hTestGradient,ae_restrict_of_ae hGradGlobal] with x hx hGrad
    rw [hx]
    by_cases hxA : x ∈ ball (0 : R3) (2*a)
    · exact congrArg (TauCeti.PDE.matrixBilinearForm (principalCoefficient g x)
        (gradient phi.1 x)) (hGrad hxA)
    · simp only [d,hZeroOutside x hxA,map_zero,ContinuousLinearMap.zero_apply]
  have hRhs : (∫ x in radiusTwoOpens, H.1 x * TauCeti.W1p.value (v : RadiusTwoH1) x
      ∂(volume : Measure R3)) =
      ∫ x in radiusTwoOpens, H.1 x * phi.1 x ∂(volume : Measure R3) := by
    apply integral_congr_ae
    filter_upwards [hTestValue] with x hx
    exact congrArg (fun r : ℝ => H.1 x * r) hx
  have hWeak : (∫ x in radiusTwoOpens, d x ∂(volume : Measure R3)) =
      ∫ x in radiusTwoOpens, H.1 x * phi.1 x ∂(volume : Measure R3) :=
    hEnergy.symm.trans ((radiusTwoSourceSolution_smooth_equation g hg H v).trans hRhs)
  have hWholeLeft : (∫ x in radiusTwoOpens, d x ∂(volume : Measure R3)) =
      ∫ x : R3, d x ∂(volume : Measure R3) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxA : x ∉ ball (0 : R3) (2*a) := fun hs => hx (hSub hs)
    simp only [d,hZeroOutside x hxA,map_zero,ContinuousLinearMap.zero_apply]
  have hWholeRight : (∫ x in radiusTwoOpens, H.1 x * phi.1 x ∂(volume : Measure R3)) =
      ∫ x : R3, H.1 x * phi.1 x ∂(volume : Measure R3) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hNot : x ∉ tsupport phi.1 := fun hs => hx (hSub (hSupport hs))
    rw [image_eq_zero_of_notMem_tsupport hNot,mul_zero]
  exact hWholeLeft.symm.trans (hWeak.trans hWholeRight)

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSmoothSource_classical_weakEquation_innerBall
