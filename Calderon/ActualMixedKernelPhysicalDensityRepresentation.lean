import Calderon.ActualMixedKernelGlobalSurfaceExtension
import Calderon.ActualMixedKernelNativeH3Datum
import Calderon.ActualPhysicalGaugePrincipalKernel
import Calderon.ActualPhysicalNativeWronskianPairing
import Calderon.ActualMixedKernelMovingFixedFlux

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint

def mixedKernelPhysicalSlice (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (y : R3) : SmoothData :=
  ⟨fun x => Gext (x,y), hG.comp (contDiff_id.prodMk contDiff_const)⟩

attribute [local irreducible] nativeMixedKernelHighDensity referencePhysicalGaugeConormalDensity
  referencePhysicalGaugeCoefficientJets ordinaryPrincipalL sphereSobolevZeroEquiv sphereSobolevInclusionL

theorem nativeMixedKernelHighDensity_represents_physicalFlux
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-P.y0‖ ≤ 4*P.rho)
    (r : ℝ) (hr : |r| ≤ 4*P.rho) (hrpos : 0 < r) (u : SmoothData)
    (hphysical : ∀ z ∈ (ballOpens : Set R3),
      coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (q • x)) u.1)
        (packetEndpoint S L P q y r z) = 0) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
        (nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L P Gext hG (q,(y,r)))),
      τ0.valueTraceL (smoothSobolev
        (referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B
          P.native_data.1.1.1 q y r u))⟫_ℝ =
      nativeMixedKernelWronskianFlux S L P q Gext u.1 y r y := by
  let U := referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B
    P.native_data.1.1.1 q y r u
  let V := mixedKernelPhysicalSlice Gext hG y
  have hU := referencePhysicalGaugePrincipal_physical_harmonic_eq_zero
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w
    P.native_data hcalc q hq y hy r hr hrpos u hphysical
  have hRep := referencePhysicalGaugeConormalDensity_represents_Wronskian
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w
    P.native_data hcalc hreg hF hO hD τ0
    (nativeMixedKernelPullbackHkDatum S L P Gext hG 3) (q,(y,r))
    (smoothBallSobolev 2 U) hU
  have hPair := integral_signedPiolaFlux_reference_metricWronskianFlux_eq_native_pairing
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w
    P.native_data hcalc τ0 q hq y hy r hr hrpos u V
  have hE : nativeMixedKernelPullbackDatum S L P Gext hG (q,(y,r)) =
      referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B
        P.native_data.1.1.1 q y r V := by
    apply Subtype.ext
    rfl
  simp only [nativeMixedKernelPullbackHkDatum, hE, firstOrder_smoothBallSobolev,
    lowerOrder_smoothBallSobolev] at hRep
  have hEndpoint : packetEndpoint S L P q y r =
      (fun z => referenceFramedPhysicalEndpoint S.g1 L P.Phi (q,((y,r),z))) := by
    funext z
    rfl
  rw [nativeMixedKernelWronskianFlux, hEndpoint]
  simpa only [nativeMixedKernelHighDensity, U, V, mixedKernelPhysicalSlice] using hRep.trans hPair.symm

private theorem physicalWronskianFlux_eq_of_product_germ
    (g : MatrixField) (u : R3 → ℝ) (G H : R3 × R3 → ℝ) (x y : R3)
    (h : G =ᶠ[𝓝 (x,y)] H) :
    metricWronskianFlux g u (fun z => G (z,y)) x =
      metricWronskianFlux g u (fun z => H (z,y)) x := by
  have hs : (fun z => G (z,y)) =ᶠ[𝓝 x] (fun z => H (z,y)) :=
    h.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hGrad : gradient (fun z => G (z,y)) x = gradient (fun z => H (z,y)) x := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_gradient_left, inner_gradient_left, hs.fderiv_eq]
  unfold metricWronskianFlux metricDivergenceFlux
  dsimp only
  rw [hs.eq_of_nhds, hGrad]

theorem nativeMixedKernelWronskianFlux_eq_of_product_germs
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) (q : ℝ)
    (G H : R3 × R3 → ℝ) (u : R3 → ℝ) (y : R3) (r : ℝ) (pole : R3)
    (h : ∀ z ∈ sphere (0 : R3) 1,
      G =ᶠ[𝓝 (packetEndpoint S L P q y r z,pole)] H) :
    nativeMixedKernelWronskianFlux S L P q G u y r pole =
      nativeMixedKernelWronskianFlux S L P q H u y r pole := by
  apply integral_congr_ae
  apply ae_of_all
  intro theta
  have hEq := physicalWronskianFlux_eq_of_product_germ (fun x => S.g1 (q • x)) u G H
    (packetEndpoint S L P q y r theta.val) pole (h theta.val theta.property)
  simp only [signedPiolaFlux, hEq]


theorem exists_native_mixed_kernel_high_density_represents_physicalFlux
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    ∃ (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext), HasCompactSupport Gext ∧
      (∀ i : Fin cover.count, ∀ k : ℕ,
        ContDiff ℝ ∞ (nativeMixedKernelPullbackHkDatum S L (cover.packet i) Gext hG k)) ∧
      (∀ i : Fin cover.count, ContDiff ℝ ∞ (fun y =>
        nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Gext hG
          (lam,(y,referenceRadius delta Rstar p L y)))) ∧
      ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers, ∀ u : SmoothData,
        (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
          (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
        ⟪(sphereSobolevZeroEquiv hO hD).symm
          (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
            (nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Gext hG
              (lam,(y,referenceRadius delta Rstar p L y)))),
          τ0.valueTraceL (smoothSobolev (referencePhysicalPullbackData S.g1 S.g1_admissible L
            (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
            (cover.packet i).native_data.1.1.1 lam y (referenceRadius delta Rstar p L y) u))⟫_ℝ =
        nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
          y (referenceRadius delta Rstar p L y) y := by
  obtain ⟨Gext,hG,hGc,hGerm⟩ := exists_smooth_mixed_kernel_eq_near_all_native_surfaces
    S L lam delta Rstar bound separation p cover K hdelta hRstar hLam hRadius
  refine ⟨Gext,hG,hGc,fun i k => contDiff_nativeMixedKernelPullbackHkDatum hcalc S L
    (cover.packet i) Gext hG k,fun i => contDiff_nativeMixedKernelHighDensity_profile
      hcalc hreg hF hO hD τ0 S L lam delta Rstar p (cover.packet i) Gext hG hdelta hRstar,?_⟩
  intro i y hy u hphysical
  have hq : lam ∈ Icc (0 : ℝ) 1 := ⟨hLam.1,hLam.2.trans cover.dilation_le_one⟩
  have hc := ((cover.packet i).centers_room y hy.2).1.le
  have hRpos := referenceRadius_pos delta Rstar p L y hdelta hRstar
  have hr : |referenceRadius delta Rstar p L y| ≤ 4*(cover.packet i).rho := by
    rw [abs_of_pos hRpos]
    exact ((hRadius y hy.1).trans (cover.radius_room i)).le
  exact (nativeMixedKernelHighDensity_represents_physicalFlux hcalc hreg hF hO hD τ0 S L
    (cover.packet i) Gext hG lam hq y hc (referenceRadius delta Rstar p L y) hr hRpos u
    hphysical).trans (nativeMixedKernelWronskianFlux_eq_of_product_germs S L (cover.packet i)
      lam Gext K.kernel u.1 y (referenceRadius delta Rstar p L y) y (hGerm i y hy))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
