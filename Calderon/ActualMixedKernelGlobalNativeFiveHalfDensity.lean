import Calderon.ActualMixedKernelSameGlobalFiveHalfDensity

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter Function
open scoped ENNReal ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError SphereHarmonic
  MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint

/-- The original physical-flux global native density has a compact H5/2 lift.
The low field, source extension, packet cover, and flux identity are the
witnesses of the original construction. -/
theorem exists_global_native_mixed_kernel_density_with_fiveHalf_lift
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    ∃ (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
      (Psi : R3 → SphereSobolev (3/2 : ℝ))
      (Psi5 : R3 → SphereSobolev (5/2 : ℝ)),
      HasCompactSupport Gext ∧ ContDiff ℝ ∞ Psi ∧ HasCompactSupport Psi ∧
      ContDiff ℝ ∞ Psi5 ∧ HasCompactSupport Psi5 ∧
      (∀ y ∈ cylinder,
        sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (Psi5 y) = Psi y) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        ∀ z ∈ sphere (0 : R3) 1, Gext =ᶠ[𝓝 (packetEndpoint S L (cover.packet i) lam y
          (referenceRadius delta Rstar p L y) z,y)] K.kernel) ∧
      ∃ U : Set R3, IsOpen U ∧ cylinder ⊆ U ∧
        (∀ i : Fin cover.count, ∀ y ∈ U ∩ (cover.packet i).centers,
          Psi y = nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Gext hG
            (lam,(y,referenceRadius delta Rstar p L y))) ∧
        ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers, ∀ u : SmoothData,
          (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
            (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
            (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
          ⟪(sphereSobolevZeroEquiv hO hD).symm
            (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)),
            τ0.valueTraceL (smoothSobolev (referencePhysicalPullbackData S.g1 S.g1_admissible L
              (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
              (cover.packet i).native_data.1.1.1 lam y (referenceRadius delta Rstar p L y) u))⟫_ℝ =
          nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
            y (referenceRadius delta Rstar p L y) y := by
  obtain ⟨Gext,hG,Psi,hGc,hPsiSmooth,hPsiCompact,hGerm,U,hU,hCU,hPsiPacket,hFlux⟩ :=
    exists_global_native_mixed_kernel_high_density_represents_physicalFlux
      hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K
      hdelta hRstar hLam hRadius
  have hPsiCyl : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      Psi y = nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Gext hG
        (lam,(y,referenceRadius delta Rstar p L y)) := by
    intro i y hy
    exact hPsiPacket i y ⟨hCU hy.1,hy.2⟩
  obtain ⟨Psi5,hPsi5Smooth,hPsi5Compact,hInc⟩ :=
    exists_same_global_native_mixed_kernel_fiveHalf_density hcalc hreg hF hO hD τ0
      S L lam delta Rstar p cover Gext hG Psi hdelta hRstar hLam hRadius hPsiCyl
  exact ⟨Gext,hG,Psi,Psi5,hGc,hPsiSmooth,hPsiCompact,hPsi5Smooth,hPsi5Compact,hInc,
    hGerm,U,hU,hCU,hPsiPacket,hFlux⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
