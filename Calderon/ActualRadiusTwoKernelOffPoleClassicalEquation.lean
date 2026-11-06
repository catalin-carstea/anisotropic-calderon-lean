import Calderon.ActualTwoMetricSymmetricSourceKernels
import Calderon.RadiusTwoCommonRowOffPoleSmoothRepresentative
import Calderon.RadiusTwoCommonRowOffPoleWeakEquation
import Calderon.NativeSmoothValueClassicalGradient
import Calderon.RadiusTwoSmoothSourceClassicalDivergence
import Calderon.SourceRungeLiteratureInterfaces

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter TopologicalSpace
open scoped ENNReal ContDiff Gradient Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap MetricVolume Literature
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution radiusTwoNativeZeroDilation

theorem radiusTwoSourceKernel_row_contDiffOn_and_nativeMetricDifferential_eq_zero
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (p : (radiusTwoOpens : Set R3)) :
    ContDiffOn ℝ ∞ (G p) ((radiusTwoOpens : Set R3) \ {(p : R3)}) ∧
      ∀ x ∈ (radiusTwoOpens : Set R3) \ {(p : R3)},
        nativeMetricDifferential g (G p) x = 0 := by
  obtain ⟨hLimit,hCont,hRep,_hBoundary,_hInverse,_hTest⟩ := hData.1 p
  have hSubClosed : (radiusTwoOpens : Set R3) \ {(p : R3)} ⊆
      closedBall (0 : R3) 2 \ {(p : R3)} := by
    intro z hz
    exact ⟨ball_subset_closedBall hz.1,hz.2⟩
  have hContOpen : ContinuousOn (G p)
      ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • radiusTwoCanonicalNormalizedPole p}) := by
    simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hCont.mono hSubClosed
  have hRepOpen : (G p) =ᵐ[(volume : Measure R3).restrict
      ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • radiusTwoCanonicalNormalizedPole p})]
      (K p : R3 → ℝ) := by
    simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using
      hRep.filter_mono (ae_mono (Measure.restrict_mono_set (volume : Measure R3) diff_subset))
  have hSmooth : ContDiffOn ℝ ∞ (G p) ((radiusTwoOpens : Set R3) \ {(p : R3)}) := by
    simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using
      contDiffOn_radiusTwoCommonRow_offpole_representative hreg hcalc g hg
        (radiusTwoCanonicalRoom p) (radiusTwoCanonicalRoom_pos p)
        (radiusTwoCanonicalRoom_lt_one p) (radiusTwoCanonicalNormalizedPole p)
        (radiusTwoCanonicalNormalizedPole_mem_room p) (K p) hLimit (G p) hContOpen hRepOpen
  refine ⟨hSmooth,?_⟩
  intro x hx
  obtain ⟨ε,hε,C,_hC,hCRoom,η,hEtaOne,hSupp,_hChain,hBallRoom⟩ :=
    exists_radiusTwo_offpole_dyadic_cutoff_chain (p : R3) x hx
  have hPoleEta : (2 : ℝ) • radiusTwoCanonicalNormalizedPole p ∉
      tsupport (η 0 : R3 → ℝ) := by
    rw [two_smul_radiusTwoCanonicalNormalizedPole]
    intro hp
    exact (hCRoom (hSupp 0 hp)).2 (by simp)
  obtain ⟨w,hw⟩ := exists_radiusTwoCommonLimit_test_cutoff g hg
    (radiusTwoCanonicalRoom p) (radiusTwoCanonicalRoom_pos p)
    (radiusTwoCanonicalRoom_lt_one p) (radiusTwoCanonicalNormalizedPole p)
    (radiusTwoCanonicalNormalizedPole_mem_room p) (K p) hLimit (η 0) hPoleEta
  let Ω : Opens R3 := ⟨ball x ε,isOpen_ball⟩
  have hΩSub : Ω ≤ radiusTwoOpens := fun z hz => (hBallRoom hz).1
  have hΩSmooth : ContDiffOn ℝ ∞ (G p) (Ω : Set R3) := hSmooth.mono hBallRoom
  have hValue : (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict Ω] G p := by
    have hwΩ := hw.filter_mono
      (ae_mono (Measure.restrict_mono_set (volume : Measure R3) hΩSub))
    have hRepΩ := hRep.filter_mono
      (ae_mono (Measure.restrict_mono_set (volume : Measure R3) hΩSub))
    filter_upwards [hwΩ,hRepΩ,ae_restrict_mem Ω.isOpen.measurableSet] with z hzw hzg hz
    exact hzw.trans ((congrArg (fun t : ℝ => t * K p z) (hEtaOne 0 z hz)).trans
      ((one_mul (K p z)).trans hzg.symm))
  have hGradient := native_gradient_ae_eq_gradient_of_contDiffOn_value
    Ω radiusTwoOpens hΩSub (w : RadiusTwoH1) (G p) hΩSmooth hValue
  have hGradGlobal : ∀ᵐ z ∂(volume : Measure R3), z ∈ (Ω : Set R3) →
      TauCeti.W1p.gradient (w : RadiusTwoH1) z = gradient (G p) z :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).mp hGradient
  let J : Fin 3 → R3 → ℝ := fun i z => ∑ j : Fin 3,
    principalCoefficient g z i j * fderiv ℝ (G p) z (coordinateVector j)
  have hDG : ContDiffOn ℝ ∞ (fderiv ℝ (G p)) (Ω : Set R3) :=
    hΩSmooth.fderiv_of_isOpen Ω.isOpen (by simp)
  have hJ (i : Fin 3) : ContDiffOn ℝ ∞ (J i) (Ω : Set R3) :=
    ContDiffOn.sum (fun j _ => (contDiff_principalCoefficient_entry g hg i j).contDiffOn.mul
      (hDG.clm_apply contDiffOn_const))
  have hFluxWeak : ∀ phi : SmoothData, HasCompactSupport phi.1 →
      tsupport phi.1 ⊆ (Ω : Set R3) →
      (∫ z : R3, (∑ i : Fin 3, lineDeriv ℝ phi.1 z (coordinateVector i) * J i z)
        ∂(volume : Measure R3)) = 0 := by
    intro phi hCompact hSupport
    let psi : 𝓓(radiusTwoOpens, ℝ) := ⟨phi.1,phi.2,hCompact,hSupport.trans hΩSub⟩
    let v : RadiusTwoH1Zero := nativeZeroTestLinear radiusTwoOpens psi
    have hOne : ∀ z ∈ tsupport (psi : R3 → ℝ), η 0 z = 1 :=
      fun z hz => hEtaOne 0 z (hSupport hz)
    have hPoleTest : (2 : ℝ) • radiusTwoCanonicalNormalizedPole p ∉
        tsupport (psi : R3 → ℝ) := by
      rw [two_smul_radiusTwoCanonicalNormalizedPole]
      intro hp
      exact (hBallRoom (hSupport hp)).2 (by simp)
    have hOff := radiusTwoCommonRow_cutoff_offpole_weak_equation g hg
      (radiusTwoCanonicalRoom p) (radiusTwoCanonicalRoom_pos p)
      (radiusTwoCanonicalRoom_lt_one p) (radiusTwoCanonicalNormalizedPole p)
      (radiusTwoCanonicalNormalizedPole_mem_room p) (K p) hLimit
      (η 0 : R3 → ℝ) w hw psi hOne hPoleTest
    have hTestGradient : (TauCeti.W1p.gradient (v : RadiusTwoH1) : R3 → R3)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] gradient phi.1 := by
      filter_upwards [TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 psi] with z hz
      simpa only [v,nativeZeroTestLinear_coe,TauCeti.W1p.gradient_ofTestFunctionₗ,
        psi,TestFunction.coe_mk] using hz
    have hZeroOutside (z : R3) (hz : z ∉ (Ω : Set R3)) : gradient phi.1 z = 0 := by
      have hNot : z ∉ tsupport phi.1 := fun hs => hz (hSupport hs)
      simp only [gradient,fderiv_of_notMem_tsupport ℝ hNot,map_zero]
    let d : R3 → ℝ := fun z => TauCeti.PDE.matrixBilinearForm (principalCoefficient g z)
      (gradient phi.1 z) (gradient (G p) z)
    have hEnergy : TauCeti.PDE.energyFormH1 (principalCoefficient g)
        (0 : R3 → R3) (0 : R3 → ℝ) (w : RadiusTwoH1) (v : RadiusTwoH1) =
        ∫ z in radiusTwoOpens, d z ∂(volume : Measure R3) := by
      rw [nativePrincipalEnergy_eq_gradient_setIntegral]
      apply integral_congr_ae
      filter_upwards [hTestGradient,ae_restrict_of_ae hGradGlobal] with z hz hGrad
      rw [hz]
      by_cases hzΩ : z ∈ (Ω : Set R3)
      · exact congrArg (TauCeti.PDE.matrixBilinearForm (principalCoefficient g z)
          (gradient phi.1 z)) (hGrad hzΩ)
      · simp only [d,hZeroOutside z hzΩ,map_zero,ContinuousLinearMap.zero_apply]
    have hPairZero : (∫ z in radiusTwoOpens, d z ∂(volume : Measure R3)) = 0 :=
      hEnergy.symm.trans hOff
    have hWhole : (∫ z in radiusTwoOpens, d z ∂(volume : Measure R3)) =
        ∫ z : R3, d z ∂(volume : Measure R3) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hzΩ : z ∉ (Ω : Set R3) := fun hz' => hz (hΩSub hz')
      simp only [d,hZeroOutside z hzΩ,map_zero,ContinuousLinearMap.zero_apply]
    have hPair : (∫ z : R3, (∑ i : Fin 3, lineDeriv ℝ phi.1 z (coordinateVector i) * J i z)
        ∂(volume : Measure R3)) = ∫ z : R3, d z ∂(volume : Measure R3) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z =>
        (principalFlux_gradient_pairing_eq_coordinate_sum (principalCoefficient g z) phi (G p) z).symm)
    exact hPair.trans (hWhole.symm.trans hPairZero)
  have hDiv := coordinateFluxRows_divergence_zero_of_smooth_weakEquation Ω J hJ hFluxWeak
  have hxΩ : x ∈ (Ω : Set R3) := mem_ball_self hε
  change -(∑ i : Fin 3, fderiv ℝ (J i) x (coordinateVector i)) = 0
  exact neg_eq_zero.mpr (hDiv x hxΩ)

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceKernel_row_contDiffOn_and_nativeMetricDifferential_eq_zero
