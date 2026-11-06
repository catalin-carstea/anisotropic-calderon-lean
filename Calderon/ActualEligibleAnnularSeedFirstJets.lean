import Calderon.ActualUpperAnnularSeedDensity
import Calderon.RadiusGraphFirstJetBound
import Calderon.ActualAnnularSeedFirstJetUniform
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError ConformalDepth
  ActualScalarPrincipalAdjoint SphereHarmonic ReferenceWeightedApproximation MetricOperator MetricVolume
attribute [local irreducible] nativeMixedKernelHighDensity nativeMixedKernelPullbackHkDatum
  referencePhysicalGaugeConormalDensity

theorem eq_actual_nativeMixedKernelDensity_of_annular_seed_germs
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
    (delta Rstar bound separation : ℝ) (p : ℕ)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p C)
    (hKSeed : EqOn K.kernel Hseed (nativeRadialSeedRoom S L C lam R tail))
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (i : Fin C.count) (y : R3) (hy : y ∈ cylinder ∩ (C.packet i).centers)
    (hr : referenceRadius delta Rstar p L y ∈ Icc a b)
    (hRep : ∀ u : SmoothData,
      (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (C.packet i) lam y
            (referenceRadius delta Rstar p L y) z) = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (C.packet i)
        lam delta Rstar p Psi u y =
        nativeMixedKernelWronskianFlux S L (C.packet i) lam K.kernel u.1 y
          (referenceRadius delta Rstar p L y) y) :
    Psi y = nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L
      (C.packet i) Hext hHext (lam,(y,referenceRadius delta Rstar p L y)) := by
  let r := referenceRadius delta Rstar p L y
  let q (z : R3) : R3 × R3 :=
    (packetEndpoint S L (C.packet i) lam y r z,y)
  have hrPos : 0 < r := ha.trans_le hr.1
  have hrCeil : r < C.radiusCeiling := (hr.2.trans_lt hb).trans hRoom
  have hGerm (z : R3) (hz : z ∈ sphere (0 : R3) 1) :
      Hext =ᶠ[𝓝 (q z)] K.kernel := by
    have hSurface : q z ∈ nativeMixedKernelAnnularSurface S L lam a b C :=
      ⟨i,y,hy,r,hr,z,hz,rfl⟩
    have hSeed : q z ∈ nativeRadialSeedRoom S L C lam R tail :=
      nativeMixedKernelAnnularSurface_subset_seedRoom S L lam R tail a b C
        hLam hR hRoom hTail ha hb hSurface
    have hKGerm : K.kernel =ᶠ[𝓝 (q z)] Hseed := by
      filter_upwards [(isOpen_nativeRadialSeedRoom S L C lam hLam R hR hRoom tail).mem_nhds hSeed]
        with q' hq'
      exact hKSeed hq'
    exact (hExtSeed (q z) hSurface).trans hKGerm.symm
  exact eq_nativeMixedKernelHighDensity_of_physicalWronskian_representation
    hcalc hreg hF hO hD τ0 S L lam delta Rstar p C i hLam y hy.2
    hrPos hrCeil K.kernel Hext hHext Psi hRep hGerm

theorem eligible_native_density_eventuallyEq_annular_seed_profile
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
    (delta Rstar bound separation : ℝ) (p : ℕ)
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
        y (referenceRadius delta Rstar p L y) y)
    (i : Fin C.count) (U : Set R3) (hU : IsOpen U)
    (hURoom : U ⊆ interior cylinder ∩ (C.packet i).centers)
    (hAnnulus : ∀ z ∈ U, referenceRadius delta Rstar p L z ∈ Icc a b)
    (y : R3) (hy : y ∈ U) :
    Psi =ᶠ[𝓝 y] (fun z => nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (C.packet i) Hext hHext (lam,(z,referenceRadius delta Rstar p L z))) := by
  filter_upwards [hU.mem_nhds hy] with z hz
  have hzRoom : z ∈ cylinder ∩ (C.packet i).centers :=
    ⟨interior_subset (hURoom hz).1,(hURoom hz).2⟩
  exact eq_actual_nativeMixedKernelDensity_of_annular_seed_germs
    hcalc hreg hF hO hD τ0 S L lam R tail a b C hLam hR hRoom hTail ha hb Hseed Hext hHext hExtSeed delta Rstar bound separation p K hKSeed Psi i z hzRoom (hAnnulus z hz) (hFlux i z hzRoom)

theorem fderiv_eligible_native_density_eq_annular_seed_profile
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
    (delta Rstar bound separation : ℝ) (p : ℕ)
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
        y (referenceRadius delta Rstar p L y) y)
    (i : Fin C.count) (U : Set R3) (hU : IsOpen U)
    (hURoom : U ⊆ interior cylinder ∩ (C.packet i).centers)
    (hAnnulus : ∀ z ∈ U, referenceRadius delta Rstar p L z ∈ Icc a b)
    (y : R3) (hy : y ∈ U) :
    fderiv ℝ Psi y = fderiv ℝ (fun z => nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (C.packet i) Hext hHext (lam,(z,referenceRadius delta Rstar p L z))) y := by
  exact ((eligible_native_density_eventuallyEq_annular_seed_profile
    hcalc hreg hF hO hD τ0 S L lam R tail a b C hLam hR hRoom hTail ha hb Hseed Hext hHext hExtSeed delta Rstar bound separation p K hKSeed Psi hFlux i U hU hURoom hAnnulus y hy).fderiv (𝕜 := ℝ)).self_of_nhds

theorem exists_uniform_eligible_native_density_annular_seed_firstJet_bound
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
 :
    ∃ B0 : ℝ, 1 ≤ B0 ∧ ∀ (delta Rstar bound separation : ℝ) (p : ℕ)
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
  obtain ⟨B0,hB0,hBound⟩ := exists_uniform_nativeMixedKernelHighDensity_annular_firstJet_bound
    hcalc hreg hF hO hD τ0 S L lam a b C Hext hHext
  refine ⟨B0,hB0,?_⟩
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
