import Calderon.ActualPhysicalDensityOperatorGermCongruence
import Calderon.ActualOriginalDensityCutoffPDE
import Calderon.ActualNativeDensityFiberMean
import Calderon.ActualNativeHarmonicTestDensityUniqueness

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory MvPolynomial Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError ConformalDepth ActualNormalizedSecondMetricDrift
  ActualScalarPrincipalAdjoint MetricOperator MetricVolume ActualFiniteHarmonicCore
attribute [local irreducible] referencePhysicalDensityOperator referenceDensityScalarCutoffCommutator
  sphereSobolevInclusionL sphereSobolevConstantOne normalizedThreeHalfSourceField
  referenceRadialEndpointInvertibleLocus referenceFramedNormalizedJacobian

/-- Every originally eligible density inherits the actual packet P equation
on the interior determined by its original physical flux tests. -/
theorem referencePhysicalDensityOperator_eq_zero_of_eligible_native_density
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hPsiSmooth : ContDiff ℝ ∞ Psi) (hPsiCompact : HasCompactSupport Psi)
    (hFlux : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ u : SmoothData,
      (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
        (packetEndpoint S L (cover.packet i) lam y
          (referenceRadius delta Rstar p L y) z) = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p Psi u y =
      nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
        y (referenceRadius delta Rstar p L y) y)
 :
    ∀ i : Fin cover.count, ∀ y ∈ interior cylinder ∩ (cover.packet i).centers,
      referencePhysicalDensityOperator S.g1 L (cover.packet i).y0 (cover.packet i).Phi
        (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
        (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
        S.g1_admissible hcalc hF hO hD τ0 S.g2 lam
        (referenceRadius delta Rstar p L) Psi y = 0 := by
  obtain ⟨PsiNorm,hPsiNormSmooth,hPsiNormCompact,hFluxNorm,hKnown,hPDE,hOperator,
      hNorm,hMeanNorm⟩ :=
    exists_global_native_density_operator_and_fiber_mean_one
      hcalc hreg hF hO hD τ0 hKernel S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius
  have hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling := ⟨hlam.le,hlamRoom⟩
  have hSame : ∀ y ∈ cylinder, PsiNorm y = Psi y := by
    intro y hy
    obtain ⟨i,hi⟩ := cover.covers_cylinder y hy
    have hrPos : 0 < referenceRadius delta Rstar p L y :=
      referenceRadius_pos delta Rstar p L y hdelta hRstar
    have hrCeil : referenceRadius delta Rstar p L y < cover.radiusCeiling :=
      hRadius y hy
    apply eq_of_nativeMixedKernelDensityFunctional_eq_on_actual_physical_harmonic_tests
      hcalc hreg hF hO hD τ0 S L lam delta Rstar p cover i hLam y hi
      hrPos hrCeil PsiNorm Psi
    intro V hV u hCover hPhysical
    have hBall : ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y
            (referenceRadius delta Rstar p L y) z) = 0 := by
      intro z hz
      exact hPhysical _ (hCover ⟨z,ball_subset_closedBall hz,rfl⟩)
    exact (hFluxNorm i y ⟨hy,hi⟩ u hBall).trans
      (hFlux i y ⟨hy,hi⟩ u hBall).symm
  intro i y hy
  have hGerm : PsiNorm =ᶠ[𝓝 y] Psi := by
    filter_upwards [isOpen_interior.mem_nhds hy.1] with z hz
    exact hSame z (interior_subset hz)
  have hP := referencePhysicalDensityOperator_congr_of_eventuallyEq
    S.g1 L (cover.packet i).y0 (cover.packet i).Phi
    (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
    (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
    S.g1_admissible hcalc hF hO hD τ0 S.g2 lam
    (referenceRadius delta Rstar p L) PsiNorm Psi y hGerm
  exact hP.symm.trans (hOperator i y ⟨interior_subset hy.1,hy.2⟩)

theorem referencePhysicalDensityOperator_normalizedSource_eq_rhs_of_eligible_native_density
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hPsiSmooth : ContDiff ℝ ∞ Psi) (hPsiCompact : HasCompactSupport Psi)
    (hFlux : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ u : SmoothData,
      (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
        (packetEndpoint S L (cover.packet i) lam y
          (referenceRadius delta Rstar p L y) z) = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p Psi u y =
      nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
        y (referenceRadius delta Rstar p L y) y)

    (i : Fin cover.count) (chi : R3 → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hSupport : tsupport chi ⊆ interior cylinder ∩ (cover.packet i).centers) :
    let P := cover.packet i
    (fun y => referencePhysicalDensityOperator S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho
      P.H P.a P.w P.native_data S.g1_admissible hcalc hF hO hD τ0 S.g2 lam
        (referenceRadius delta Rstar p L) (normalizedThreeHalfSourceField chi Psi) y) =
    (fun y => -(chi y • referencePhysicalDensityOperator S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho
      P.H P.a P.w P.native_data S.g1_admissible hcalc hF hO hD τ0 S.g2 lam
        (referenceRadius delta Rstar p L) (fun _ => sphereSobolevConstantOne (3/2:ℝ)) y) +
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceDensityScalarCutoffCommutator S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho
          P.H P.a P.w P.native_data S.g1_admissible hcalc hF hO hD τ0 S.g2 lam
            (referenceRadius delta Rstar p L) chi
              (fun z => Psi z-sphereSobolevConstantOne (3/2:ℝ)) y)) := by
  extract_lets P
  let R : R3 → ℝ := referenceRadius delta Rstar p L
  have hR : ContDiff ℝ ∞ R := contDiff_referenceRadius_actual delta Rstar p L hdelta hRstar
  have hq : lam ∈ Icc (0:ℝ) 1 := ⟨hlam.le,hlamRoom.trans cover.dilation_le_one⟩
  have hOp := referencePhysicalDensityOperator_eq_zero_of_eligible_native_density
    hcalc hreg hF hO hD τ0 hKernel S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius Psi hPsiSmooth hPsiCompact hFlux
  have hGeometry : ∀ y ∈ tsupport chi, R y ≠ 0 ∧
      (lam,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
        S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
          hcalc hF hO hD τ0 ∧
      ∀ x : UnitSphere, (referenceFramedNormalizedJacobian
        S.g1 L P.Phi (lam,((y,R y),x.val))).IsInvertible := by
    intro y hy
    have hcent : y ∈ P.centers := (hSupport hy).2
    have hc : ‖y-P.y0‖ < 4*P.rho := (P.centers_room y hcent).1
    have hrpos : 0 < R y := referenceRadius_pos delta Rstar p L y hdelta hRstar
    have hr : |R y| < 4*P.rho := by
      rw [abs_of_pos hrpos]
      exact (hRadius y (interior_subset (hSupport hy).1)).trans (cover.radius_room i)
    have hInv (x : UnitSphere) :
        (referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,R y),x.val))).IsInvertible := by
      apply isInvertible_of_operatorMatrixMap_det_ne_zero
      exact referenceFramedNormalizedJacobian_det_ne_zero_on_closedDoubleBall
        S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
          lam hq y hc.le (R y) hr.le x.val
          (closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall x.property))
    have hp := referenceRadialEndpointInvertibleLocus_mem_on_actual_room
      S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
        hcalc hreg hF hO hD τ0 lam hq y hc.le (R y) hr.le
    exact ⟨hrpos.ne',hp,hInv⟩
  exact referencePhysicalDensityOperator_normalizedSource_eq_cutoff_rhs
    S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
      S.g1_admissible hcalc hF hO hD τ0 S.g2 hreg lam R chi Psi hPsiSmooth hchi hR
      hGeometry (fun y hy => hOp i y (hSupport hy))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
