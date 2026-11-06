import Calderon.ActualNativeHarmonicTestDensityUniqueness
import Calderon.ActualHalfGaugeConormalFamily
import Calderon.ActualGlobalNativeDensityKnownSideReproduction
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualNormalizedSecondMetricDrift

theorem actual_packet_referencePhysicalPullbackData_zero
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (lam : ℝ) (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers) (r : ℝ) (u : SmoothData) :
    (referencePhysicalPullbackData S.g1 S.g1_admissible L (cover.packet i).y0
      (cover.packet i).Phi (cover.packet i).B (cover.packet i).native_data.1.1.1 lam y r u).1 0 =
      u.1 y := by
  have hq : lam ∈ Icc (0 : ℝ) 1 := ⟨hLam.1,hLam.2.trans cover.dilation_le_one⟩
  obtain ⟨-,-,-,-,-,-,-,-,hvalue,-⟩ := (cover.packet i).native_data.1.1.1
  have h0 : packetEndpoint S L (cover.packet i) lam y r 0 = y := by
    show ((cover.packet i).Phi lam
      (y,r • conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y) 0) 1).1 = y
    rw [map_zero,smul_zero]
    exact hvalue lam hq y ((cover.packet i).centers_room y hy).2
  change u.1 (packetEndpoint S L (cover.packet i) lam y r 0) = u.1 y
  rw [h0]

theorem originalKnownSideDensity_eq_referencePhysicalHalfGaugeConormalDensity
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : KnownSideSourceData)
    (L lam delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (hrpos : 0 < referenceRadius delta Rstar p L y)
    (hrceil : referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ)
    (hCompact : HasCompactSupport θ) (b : ℝ) (hb : 0 < b)
    (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (η : R3 → ℝ) (hη : ContDiff ℝ ∞ η)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hKnown : lam • y ∈ S.W → ∀ u : SmoothData,
      (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
        (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p Psi u y = u.1 y)
    (hyKnown : lam • y ∈ S.W)
    (hPi : ∀ v : SmoothData,
      ordinaryPrincipalL hcalc 0 (referencePhysicalGaugeCoefficientJets S.g1 S.g1_admissible L
          (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
          (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          2 (lam,(y,referenceRadius delta Rstar p L y))) (smoothBallSobolev 2 v) = 0 →
      ⟪(sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
          (referencePhysicalHalfGaugeConormalDensity S.g1 S.g1_admissible L
          (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
          (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0
          (lam,(y,referenceRadius delta Rstar p L y)))),
        τ0.valueTraceL (smoothSobolev v)⟫_ℝ = v.1 0) :
    Psi y = referencePhysicalHalfGaugeConormalDensity S.g1 S.g1_admissible L
          (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
          (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0
          (lam,(y,referenceRadius delta Rstar p L y)) := by
  let P := cover.packet i
  let r := referenceRadius delta Rstar p L y
  let Pi : SphereSobolev (3/2 : ℝ) := referencePhysicalHalfGaugeConormalDensity S.g1 S.g1_admissible L
          (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
          (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0
          (lam,(y,referenceRadius delta Rstar p L y))
  change Psi y = Pi
  apply eq_of_nativeMixedKernelDensityFunctional_eq_on_actual_physical_harmonic_tests
    hcalc hreg hF hO hD τ0 S L lam delta Rstar p cover i hLam y hy hrpos hrceil
    Psi (fun _ => Pi)
  intro V hV u hCover hPhysical
  have hBall : ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
      (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
      (packetEndpoint S L P lam y r z) = 0 := by
    intro z hz
    have hzClosed : z ∈ closedBall (0 : R3) 1 := ball_subset_closedBall hz
    exact hPhysical _ (hCover ⟨z,hzClosed,rfl⟩)
  let U : SmoothData := referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B
    P.native_data.1.1.1 lam y r u
  have hq : lam ∈ Icc (0 : ℝ) 1 := ⟨hLam.1,hLam.2.trans cover.dilation_le_one⟩
  have hCenter : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy).1.le
  have hRadius : |r| ≤ 4*P.rho := by
    rw [abs_of_pos hrpos]
    exact (hrceil.trans (cover.radius_room i)).le
  have hNative := referencePhysicalGaugePrincipal_physical_harmonic_eq_zero S.g1 S.g1_admissible
    L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    hcalc lam hq y hCenter r hRadius hrpos u hBall
  have hValue := hPi U hNative
  change nativeMixedKernelDensityFunctional hO hD τ0 S L P lam delta Rstar p Psi u y =
    ⟪(sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) Pi),
      τ0.valueTraceL (smoothSobolev U)⟫_ℝ
  rw [hKnown hyKnown u hBall]
  exact (actual_packet_referencePhysicalPullbackData_zero S L cover i lam hLam y hy r u).symm.trans hValue.symm

theorem exists_original_global_native_density_knownSide_eq_halfGaugeConormalDensity
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ)
    (hCompact : HasCompactSupport θ) (b : ℝ) (hb : 0 < b)
    (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (η : R3 → ℝ) (hη : ContDiff ℝ ∞ η)
    (hPi : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      lam • y ∈ S.W → ∀ v : SmoothData,
      ordinaryPrincipalL hcalc 0 (referencePhysicalGaugeCoefficientJets S.g1 S.g1_admissible L
          (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
          (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          2 (lam,(y,referenceRadius delta Rstar p L y))) (smoothBallSobolev 2 v) = 0 →
      ⟪(sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
          (referencePhysicalHalfGaugeConormalDensity S.g1 S.g1_admissible L
          (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
          (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0
          (lam,(y,referenceRadius delta Rstar p L y)))),
        τ0.valueTraceL (smoothSobolev v)⟫_ℝ = v.1 0) :
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
        lam • y ∈ S.W → Psi y = referencePhysicalHalfGaugeConormalDensity S.g1 S.g1_admissible L
          (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
          (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0
          (lam,(y,referenceRadius delta Rstar p L y))) ∧
      ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        ∀ (V : Set R3), IsOpen V → ∀ u : SmoothData,
        packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
          closedBall (0 : R3) 1 ⊆ V →
        (∀ x ∈ V, coordinateFluxDivergence (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) →
        ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
          ContDiffOn ℝ ∞ (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
            lam delta Rstar p Psi u) Y ∧
          ∀ z ∈ Y, normalizedSecondLaplacian S.g1 S.g2 L lam
            (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u) z = 0 := by
  obtain ⟨Psi,hPsi,hCompactPsi,hFlux,hKnown,hPDE⟩ :=
    exists_global_native_density_scalarPDE_and_original_known_side_reproduction
      hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius
  refine ⟨Psi,hPsi,hCompactPsi,hFlux,hKnown,?_,hPDE⟩
  intro i y hy hyKnown
  exact originalKnownSideDensity_eq_referencePhysicalHalfGaugeConormalDensity
    hcalc hreg hF hO hD τ0 S L lam delta Rstar p cover i ⟨hlam.le,hlamRoom⟩ y hy.2
    (referenceRadius_pos delta Rstar p L y hdelta hRstar) (hRadius y hy.1)
    θ ζ hθ hζ hCompact b hb hZero η hη Psi (hKnown i y hy) hyKnown (hPi i y hy hyKnown)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
