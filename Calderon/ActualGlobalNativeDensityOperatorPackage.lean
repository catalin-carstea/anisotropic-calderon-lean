import Calderon.ActualMixedKernelFunctionalTraceDictionary
import Calderon.ActualPhysicalHarmonicTestPairingWithoutJointChart
import Calderon.ActualPacketPhysicalHalfTraceDensity
import Calderon.ActualReferenceGaugeRadialInverse
import Calderon.ActualGlobalNativeDensityKnownSideReproduction

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ConnectionError MetricVolume MetricOperator DirichletFamily DirichletFamily.DriftBootstrap
  SphereHarmonic NativeH2ThreeHalfValueTrace NativeSmoothSharpTraceCompletion
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift ConformalDepth ReferenceWeightedApproximation

theorem actual_packet_referencePhysicalDensityOperator_eq_zero_of_scalarPDE
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L) (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (i : Fin cover.count) (y : R3) (hy : y ∈ cylinder ∩ (cover.packet i).centers)
    (hrceil : referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi : R3 → SphereSobolev (3/2 : ℝ)) (hPsi : ContDiff ℝ ∞ Psi)
    (hScalar : ∀ (V : Set R3), IsOpen V → ∀ u : SmoothData,
      packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
        closedBall (0 : R3) 1 ⊆ V →
      (∀ x ∈ V, coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1) x = 0) →
      normalizedSecondLaplacian S.g1 S.g2 L lam
        (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi u) y = 0) :
    referencePhysicalDensityOperator S.g1 L (cover.packet i).y0 (cover.packet i).Phi
      (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
      (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
      S.g1_admissible hcalc hF hO hD τ0 S.g2 lam
      (referenceRadius delta Rstar p L) Psi y = 0 := by
  let P := cover.packet i
  let R : R3 → ℝ := referenceRadius delta Rstar p L
  let r := R y
  let F : SphereSobolev (-(1/2 : ℝ)) := referencePhysicalDensityOperator S.g1 L P.y0 P.Phi
    P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data S.g1_admissible hcalc hF hO hD τ0
    S.g2 lam R Psi y
  have hq : lam ∈ Icc (0 : ℝ) 1 := ⟨hLam.1,hLam.2.trans cover.dilation_le_one⟩
  have hc : ‖y-P.y0‖ < 4*P.rho := (P.centers_room y hy.2).1
  have hrpos : 0 < r := referenceRadius_pos delta Rstar p L y hdelta hRstar
  have hr : |r| < 4*P.rho := by
    rw [abs_of_pos hrpos]
    exact hrceil.trans (cover.radius_room i)
  have hR : ContDiff ℝ ∞ R := contDiff_referenceRadius_actual delta Rstar p L hdelta hRstar
  have hInv (x : UnitSphere) :
      (referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),x.val))).IsInvertible := by
    apply isInvertible_of_operatorMatrixMap_det_ne_zero
    exact referenceFramedNormalizedJacobian_det_ne_zero_on_closedDoubleBall
      S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
      lam hq y hc.le r hr.le x.val
      (closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall x.property))
  have hp := referenceRadialEndpointInvertibleLocus_mem_on_actual_room
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    hcalc hreg hF hO hD τ0 lam hq y hc.le r hr.le
  change F = 0
  apply eq_zero_of_actualPacketPhysicalHarmonicHalfTrace_pairing_eq_zero
    hcalc hreg hF hO hD τ0 S L cover i lam hLam y hy.2 r hrpos hrceil F
  intro z hz
  rcases hz with ⟨u,V,hV,hCover,hPhysical,hzEq⟩
  let U : R3 → SphereSobolev (3/2 : ℝ) := referencePhysicalNativeThreeHalfTraceSection
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    hcalc hF hO hD τ0 lam R u
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let f : R3 → ℝ := fun x => sphereSobolevDualPairing (-(1/2 : ℝ)) (J (I (Psi x))) (I (U x))
  have hFunc : f = nativeMixedKernelDensityFunctional hO hD τ0 S L P
      lam delta Rstar p Psi u := by
    funext x
    exact (nativeMixedKernelDensityFunctional_eq_native_dualTracePairing
      hcalc hF hO hD τ0 S L P lam delta Rstar p Psi u x).symm
  have hPair := referencePhysicalDensityOperator_pairing_physical_harmonic_neighborhood
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    S.g2 S.g2_admissible hcalc hreg hF hO hD τ0 hKernel lam hq R hR y hc hr hrpos.ne'
    (P.centers_room y hy.2).2 hInv hp V hV u hCover hPhysical Psi hPsi
  have hPair' : r * normalizedSecondLaplacian S.g1 S.g2 L lam f y =
      sphereSobolevDualPairing (-(1/2 : ℝ)) F (I (U y)) := hPair
  have hZ : normalizedSecondLaplacian S.g1 S.g2 L lam f y = 0 := by
    rw [hFunc]
    exact hScalar V hV u hCover hPhysical
  rw [hZ,mul_zero] at hPair'
  have hHalf : I (U y) = smoothHalfTrace hF hO hD τ0
      (referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B
        P.native_data.1.1.1 lam y r u) :=
    sphereSobolevInclusionL_nativeThreeHalfValueTraceL_smoothBallSobolev hcalc hF hO hD τ0
      (referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B
        P.native_data.1.1.1 lam y r u)
  rw [hHalf] at hPair'
  rw [hzEq]
  exact hPair'.symm

theorem exists_global_native_density_reproduction_and_operator_equation
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    ∃ Psi : R3 → SphereSobolev (3/2 : ℝ), ContDiff ℝ ∞ Psi ∧ HasCompactSupport Psi ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers, ∀ u : SmoothData,
        (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
          (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u y =
          nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
            y (referenceRadius delta Rstar p L y) y) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        lam • y ∈ S.W → ∀ u : SmoothData,
        (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
          (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi u y = u.1 y) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        ∀ (V : Set R3), IsOpen V → ∀ u : SmoothData,
        packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
          closedBall (0 : R3) 1 ⊆ V →
        (∀ x ∈ V, coordinateFluxDivergence (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) →
        ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
          ContDiffOn ℝ ∞ (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
            lam delta Rstar p Psi u) Y ∧
          ∀ z ∈ Y, normalizedSecondLaplacian S.g1 S.g2 L lam
            (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u) z = 0 ) ∧
      ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        referencePhysicalDensityOperator S.g1 L (cover.packet i).y0 (cover.packet i).Phi
          (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          S.g1_admissible hcalc hF hO hD τ0 S.g2 lam
          (referenceRadius delta Rstar p L) Psi y = 0 := by
  obtain ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE⟩ :=
    exists_global_native_density_scalarPDE_and_original_known_side_reproduction
      hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius
  refine ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,?_⟩
  intro i y hy
  apply actual_packet_referencePhysicalDensityOperator_eq_zero_of_scalarPDE
    hcalc hreg hF hO hD τ0 hKernel S L lam delta Rstar p cover hdelta hRstar
    ⟨hlam.le,hlamRoom⟩ i y hy (hRadius y hy.1) Psi hPsi
  intro V hV u hCover hPhysical
  obtain ⟨Y,hY,hyY,hSmooth,hZero⟩ := hPDE i y hy V hV u hCover hPhysical
  exact hZero y hyY

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
