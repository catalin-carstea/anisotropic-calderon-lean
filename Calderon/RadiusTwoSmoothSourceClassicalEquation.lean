import Calderon.RadiusTwoSmoothSourceResponse
import Calderon.RadiusTwoSmoothSourceClassicalDivergence
import Calderon.NativeMetricJetIdentity

/-! Full upfront expansion precedes the actual chosen source PDE and jet constraint. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory TopologicalSpace Filter
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily MetricVolume Literature

theorem nativeMetricDifferential_congr_of_eventuallyEq
    (g : MatrixField) (u v : R3 → ℝ) (p : R3) (h : u =ᶠ[𝓝 p] v) :
    nativeMetricDifferential g u p = nativeMetricDifferential g v p := by
  unfold nativeMetricDifferential
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hD : fderiv ℝ u =ᶠ[𝓝 p] fderiv ℝ v := h.fderiv
  have hFlux : (fun z => ∑ j : Fin 3, principalCoefficient g z i j *
      fderiv ℝ u z (coordinateVector j)) =ᶠ[𝓝 p]
      (fun z => ∑ j : Fin 3, principalCoefficient g z i j *
        fderiv ℝ v z (coordinateVector j)) := by
    filter_upwards [hD] with z hz
    rw [hz]
  exact congrArg (fun L : R3 →L[ℝ] ℝ => L (coordinateVector i)) hFlux.fderiv_eq

theorem nativeMetricDifferential_radiusTwoSmoothSourceResponse
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (φ : 𝓓(fixedExteriorSourceOpens, ℝ))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) :
    nativeMetricDifferential g (radiusTwoSmoothSourceResponse hreg hcalc g hg φ) p = φ p := by
  have hp2 : ‖p‖ < 2 := mem_ball_zero_iff.mp hp
  let a : ℝ := (‖p‖+2)/4
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : a < 1 := by dsimp only [a]; linarith
  have hpBall : p ∈ ball (0 : R3) (2*a) := by
    rw [mem_ball_zero_iff]
    dsimp only [a]
    linarith
  have hSub : ball (0 : R3) (2*a) ⊆ (radiusTwoOpens : Set R3) :=
    ball_subset_ball (by linarith)
  obtain ⟨U,hCont,hSmooth,hAE,hPDE⟩ :=
    exists_radiusTwoSmoothSource_classical_divergence_innerBall hreg hcalc g hg
      ⟨φ,φ.contDiff⟩ a ha ha1
  have hGlobal := radiusTwoSmoothSourceResponse_spec hreg hcalc g hg φ
  have hGlobalAE : radiusTwoSmoothSourceResponse hreg hcalc g hg φ
      =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) (2*a))] U :=
    (hGlobal.2.2.1.symm.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub))).trans hAE
  have hEq : EqOn (radiusTwoSmoothSourceResponse hreg hcalc g hg φ) U (ball (0 : R3) (2*a)) :=
    Measure.eqOn_open_of_ae_eq (μ := (volume : Measure R3)) hGlobalAE isOpen_ball
      hGlobal.1.continuousOn hCont.continuousOn
  have hNear : radiusTwoSmoothSourceResponse hreg hcalc g hg φ =ᶠ[𝓝 p] U := by
    filter_upwards [isOpen_ball.mem_nhds hpBall] with z hz
    exact hEq hz
  exact (nativeMetricDifferential_congr_of_eventuallyEq g _ U p hNear).trans (hPDE p hpBall)

theorem nativeMetricJetFunctional_radiusTwoSmoothSourceResponse
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (φ : 𝓓(fixedExteriorSourceOpens, ℝ))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) :
    nativeMetricJetFunctional g p
      (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg φ) p)
      (fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg φ)) p) = φ p := by
  have hSmooth := (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg φ).2.1
  have hDSmooth : ContDiffOn ℝ ∞
      (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg φ))
      (radiusTwoOpens : Set R3) :=
    hSmooth.fderiv_of_isOpen radiusTwoOpens.isOpen (by simp)
  have hD : DifferentiableAt ℝ
      (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg φ)) p :=
    (hDSmooth.contDiffAt (radiusTwoOpens.isOpen.mem_nhds hp)).differentiableAt (by simp)
  exact (nativeMetricDifferential_eq_jetFunctional g hg _ p hD).symm.trans
    (nativeMetricDifferential_radiusTwoSmoothSourceResponse hreg hcalc g hg φ p hp)

theorem nativeMetricJetFunctional_radiusTwoSmoothSourceResponse_eq_zero
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (φ : 𝓓(fixedExteriorSourceOpens, ℝ))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3))
    (hOutside : p ∉ (fixedExteriorSourceOpens : Set R3)) :
    nativeMetricJetFunctional g p
      (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg φ) p)
      (fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg φ)) p) = 0 := by
  rw [nativeMetricJetFunctional_radiusTwoSmoothSourceResponse hreg hcalc g hg φ p hp]
  exact image_eq_zero_of_notMem_tsupport (fun h => hOutside (φ.tsupport_subset h))

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.nativeMetricDifferential_congr_of_eventuallyEq
#print axioms OAI.AnisotropicCalderon.ExteriorSource.nativeMetricDifferential_radiusTwoSmoothSourceResponse
#print axioms OAI.AnisotropicCalderon.ExteriorSource.nativeMetricJetFunctional_radiusTwoSmoothSourceResponse
#print axioms OAI.AnisotropicCalderon.ExteriorSource.nativeMetricJetFunctional_radiusTwoSmoothSourceResponse_eq_zero
