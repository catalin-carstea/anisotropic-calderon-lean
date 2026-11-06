import Calderon.ActualEligibleAnnularSeedFirstJets
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError ConformalDepth
open ActualScalarPrincipalAdjoint SphereHarmonic ReferenceWeightedApproximation MetricOperator MetricVolume
attribute [local irreducible] nativeMixedKernelHighDensity nativeMixedKernelPullbackHkDatum
  referencePhysicalGaugeConormalDensity
theorem eligible_native_density_annular_firstJet_bound_of_uniform_profile_budget
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam R tail a b : ℝ) (C : NativeNormalCover S L)
    (hLam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (hTail : tail < a) (ha : 0 < a) (hb : b < R)
    (Hseed Hext : R3 × R3 → ℝ) (hHext : ContDiff ℝ ∞ Hext)
    (hExtSeed : ∀ q ∈ nativeMixedKernelAnnularSurface S L lam a b C,
      Hext =ᶠ[𝓝 q] Hseed)
    (B0:ℝ)
    (hBound:∀ i:Fin C.count,∀ y∈cylinder,∀ r∈Icc a b,
      ‖nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (C.packet i) Hext hHext (lam,(y,r))‖ ≤ B0 ∧
      ‖fderiv ℝ (nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (C.packet i) Hext hHext) (lam,(y,r))‖ ≤ B0):
    ∀ (delta Rstar bound separation : ℝ) (p : ℕ)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p C)
    (hKSeed : EqOn K.kernel Hseed (nativeRadialSeedRoom S L C lam R tail))
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hFlux : ∀ i : Fin C.count, ∀ y ∈ cylinder ∩ (C.packet i).centers,
      ∀ u : SmoothData,
      (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
        (packetEndpoint S L (C.packet i) lam y
          (referenceRadius delta Rstar p L y) z) = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (C.packet i)
        lam delta Rstar p Psi u y =
      nativeMixedKernelWronskianFlux S L (C.packet i) lam K.kernel u.1
        y (referenceRadius delta Rstar p L y) y),
      0 < delta → ∀ (i : Fin C.count) (U : Set R3), IsOpen U →
      U ⊆ interior cylinder ∩ (C.packet i).centers →
      (∀ z ∈ U, referenceRadius delta Rstar p L z ∈ Icc a b) → ∀ y ∈ U,
      ‖Psi y‖ ≤ B0 ∧
      (‖fderiv ℝ (referenceRadius delta Rstar p L) y‖ ≤ 1 → ‖fderiv ℝ Psi y‖ ≤ B0) := by
  intro delta Rstar bound separation p K hKSeed Psi hFlux hdelta i U hU hURoom hAnnulus y hy
  have hyRoom : y ∈ cylinder ∩ (C.packet i).centers :=
    ⟨interior_subset (hURoom hy).1,(hURoom hy).2⟩
  have hPB := hBound i y hyRoom.1 (referenceRadius delta Rstar p L y) (hAnnulus y hy)
  have hEq := eq_actual_nativeMixedKernelDensity_of_annular_seed_germs
    hcalc hreg hF hO hD τ0 S L lam R tail a b C hLam hR hRoom hTail ha hb Hseed Hext hHext hExtSeed delta Rstar bound separation p K hKSeed Psi i y hyRoom (hAnnulus y hy) (hFlux i y hyRoom)
  refine ⟨?_,?_⟩
  · rw [hEq]
    exact hPB.1
  · intro hDR
    have hDerivative := fderiv_eligible_native_density_eq_annular_seed_profile
      hcalc hreg hF hO hD τ0 S L lam R tail a b C hLam hR hRoom hTail ha hb Hseed Hext hHext hExtSeed delta Rstar bound separation p K hKSeed Psi hFlux i U hU hURoom hAnnulus y hy
    rw [hDerivative]
    have hPiDiff : DifferentiableAt ℝ (nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (C.packet i) Hext hHext) (lam,(y,referenceRadius delta Rstar p L y)) :=
      (contDiff_nativeMixedKernelHighDensity hcalc hreg hF hO hD τ0 S L
        (C.packet i) Hext hHext).differentiable (by simp) _
    have hRDiff : DifferentiableAt ℝ (referenceRadius delta Rstar p L) y :=
      (hasFDerivAt_referenceRadius delta Rstar p L y hdelta).differentiableAt
    exact norm_fderiv_radiusGraph_pullback_le (nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (C.packet i) Hext hHext) lam
      (referenceRadius delta Rstar p L) y B0 hPiDiff hRDiff hPB.2 hDR

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
