import Calderon.ActualTwoMetricSymmetricSourceKernels
import Calderon.RadiusTwoSmoothSourceResponse

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter TopologicalSpace
open scoped ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution TauCeti.PDE.weakSolutionDirichlet

theorem integral_radiusTwoSourceKernel_mul_fixedSource_eq_response
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (p : (radiusTwoOpens : Set R3)) (f : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    (∫ z in radiusTwoOpens, G p z * f z ∂(volume : Measure R3)) =
      radiusTwoSmoothSourceResponse hreg hcalc g hg f p := by
  let rho : RadiusTwoL2 := smoothRadiusTwoForcing ⟨(f : R3 → ℝ),f.contDiff⟩
  obtain ⟨_hLimit,_hCont,_hRep,_hBoundary,hInverse,_hTest⟩ := hData.1 p
  obtain ⟨H,hH,hHA,_hKPair,hGPair⟩ := hInverse rho
  let V : Set R3 :=
    (fun z : R3 => (1/2 : ℝ) • z) ⁻¹' ball (0 : R3) (radiusTwoCanonicalRoom p) ∩
      (radiusTwoOpens : Set R3)
  have hHalf : Continuous (fun z : R3 => (1/2 : ℝ) • z) :=
    (((1/2 : ℝ) • ContinuousLinearMap.id ℝ R3) : R3 →L[ℝ] R3).continuous
  have hPre : IsOpen ((fun z : R3 => (1/2 : ℝ) • z) ⁻¹'
      ball (0 : R3) (radiusTwoCanonicalRoom p)) := isOpen_ball.preimage hHalf
  have hV : IsOpen V := hPre.inter radiusTwoOpens.isOpen
  have hpV : (p : R3) ∈ V := by
    refine ⟨?_,p.property⟩
    exact radiusTwoCanonicalNormalizedPole_mem_room p
  have hVsub : V ⊆ (radiusTwoOpens : Set R3) := fun z hz => hz.2
  have hHA' := hHA.filter_mono
    (ae_mono (Measure.restrict_mono_set (volume : Measure R3) hVsub))
  have hResponse := radiusTwoSmoothSourceResponse_spec hreg hcalc g hg f
  have hResponseAE := hResponse.2.2.1.filter_mono
    (ae_mono (Measure.restrict_mono_set (volume : Measure R3) hVsub))
  have hAE : H =ᵐ[(volume : Measure R3).restrict V]
      radiusTwoSmoothSourceResponse hreg hcalc g hg f := by
    filter_upwards [hHA',hResponseAE,ae_restrict_mem hV.measurableSet] with z hHz hRz hz
    exact (hHz (ball_subset_closedBall hz.1)).trans hRz
  have hPoint : H (p : R3) = radiusTwoSmoothSourceResponse hreg hcalc g hg f p :=
    (Measure.eqOn_open_of_ae_eq (μ := (volume : Measure R3)) hAE hV
      hH.continuousOn hResponse.1.continuousOn) hpV
  calc
    (∫ z in radiusTwoOpens, G p z * f z ∂(volume : Measure R3)) =
        (∫ z in radiusTwoOpens, G p z * rho z ∂(volume : Measure R3)) := by
      apply integral_congr_ae
      filter_upwards [smoothRadiusTwoForcing_ae ⟨(f : R3 → ℝ),f.contDiff⟩] with z hz
      exact congrArg (fun v : ℝ => G p z * v) hz.symm
    _ = H (p : R3) := hGPair
    _ = radiusTwoSmoothSourceResponse hreg hcalc g hg f p := hPoint

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.integral_radiusTwoSourceKernel_mul_fixedSource_eq_response
