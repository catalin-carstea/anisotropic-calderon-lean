import Calderon.ActualNativeHarmonicTestDensityUniqueness
import Calderon.ActualMixedKernelPhysicalDensityRepresentation
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
attribute [local irreducible] nativeMixedKernelHighDensity referencePhysicalGaugeConormalDensity
  referencePhysicalGaugeCoefficientJets ordinaryPrincipalL sphereSobolevZeroEquiv sphereSobolevInclusionL

theorem eq_nativeMixedKernelHighDensity_of_physicalWronskian_representation
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : KnownSideSourceData)
    (L lam delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (hrpos : 0 < referenceRadius delta Rstar p L y)
    (hrceil : referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (G Hext : R3 × R3 → ℝ) (hH : ContDiff ℝ ∞ Hext)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hRep : ∀ u : SmoothData,
      (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u y =
        nativeMixedKernelWronskianFlux S L (cover.packet i) lam G u.1 y (referenceRadius delta Rstar p L y) y)
    (hGerm : ∀ z ∈ sphere (0 : R3) 1,
      Hext =ᶠ[𝓝 (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z,y)] G) :
    Psi y = nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Hext hH (lam,(y,referenceRadius delta Rstar p L y)) := by
  let P := cover.packet i
  let r := referenceRadius delta Rstar p L y
  let Pi : SphereSobolev (3/2 : ℝ) := nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Hext hH (lam,(y,referenceRadius delta Rstar p L y))
  change Psi y = Pi
  apply eq_of_nativeMixedKernelDensityFunctional_eq_on_actual_physical_harmonic_tests
    hcalc hreg hF hO hD τ0 S L lam delta Rstar p cover i hLam y hy hrpos hrceil
    Psi (fun _ => Pi)
  intro V hV u hCover hPhysical
  have hBall : ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
      (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1) (packetEndpoint S L P lam y r z) = 0 := by
    intro z hz
    exact hPhysical _ (hCover ⟨z,ball_subset_closedBall hz,rfl⟩)
  have hq : lam ∈ Icc (0 : ℝ) 1 := ⟨hLam.1,hLam.2.trans cover.dilation_le_one⟩
  have hCenter : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy).1.le
  have hr : |r| ≤ 4*P.rho := by
    rw [abs_of_pos hrpos]
    exact (hrceil.trans (cover.radius_room i)).le
  have hHRep := nativeMixedKernelHighDensity_represents_physicalFlux hcalc hreg hF hO hD τ0 S L P Hext hH
    lam hq y hCenter r hr hrpos u hBall
  have hFlux := nativeMixedKernelWronskianFlux_eq_of_product_germs S L P lam Hext G u.1 y r y hGerm
  change nativeMixedKernelDensityFunctional hO hD τ0 S L P lam delta Rstar p Psi u y =
    ⟪(sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) Pi),
      τ0.valueTraceL (smoothSobolev (referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B
        P.native_data.1.1.1 lam y r u))⟫_ℝ
  exact (hRep u hBall).trans (hHRep.trans hFlux).symm

theorem nativeMixedKernelHighDensity_eq_of_product_germs_on_profile
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : KnownSideSourceData)
    (L lam delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (hrpos : 0 < referenceRadius delta Rstar p L y)
    (hrceil : referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (G Hext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ Hext)
    (hGerm : ∀ z ∈ sphere (0 : R3) 1,
      G =ᶠ[𝓝 (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z,y)] Hext) :
    nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) G hG (lam,(y,referenceRadius delta Rstar p L y)) =
      nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Hext hH (lam,(y,referenceRadius delta Rstar p L y)) := by
  apply eq_nativeMixedKernelHighDensity_of_physicalWronskian_representation
    hcalc hreg hF hO hD τ0 S L lam delta Rstar p cover i hLam y hy hrpos hrceil
    G Hext hH (fun _ => nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) G hG (lam,(y,referenceRadius delta Rstar p L y)))
  · intro u hu
    have hq : lam ∈ Icc (0 : ℝ) 1 := ⟨hLam.1,hLam.2.trans cover.dilation_le_one⟩
    have hCenter : ‖y-(cover.packet i).y0‖ ≤ 4*(cover.packet i).rho := ((cover.packet i).centers_room y hy).1.le
    have hr : |referenceRadius delta Rstar p L y| ≤ 4*(cover.packet i).rho := by
      rw [abs_of_pos hrpos]
      exact (hrceil.trans (cover.radius_room i)).le
    exact nativeMixedKernelHighDensity_represents_physicalFlux hcalc hreg hF hO hD τ0 S L
      (cover.packet i) G hG lam hq y hCenter (referenceRadius delta Rstar p L y) hr hrpos u hu
  · exact fun z hz => (hGerm z hz).symm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
