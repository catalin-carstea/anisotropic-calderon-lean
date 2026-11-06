import Calderon.ActualGlobalNativeDensityNormalization
import Calderon.SpherePositiveDensity

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError ConformalDepth ActualNormalizedSecondMetricDrift

/-- The constant physical test is the literal constant sphere trace for the
same native H0 density field. -/
theorem nativeMixedKernelDensityFunctional_one_eq_sphereMean
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (tau : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam delta Rstar : ℝ) (p : ℕ) (Psi : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) :
    nativeMixedKernelDensityFunctional hO hD tau S L P lam delta Rstar p Psi
        (⟨fun _ => (1 : ℝ),contDiff_const⟩ : SmoothData) y =
      sphereMean ((sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))) := by
  unfold nativeMixedKernelDensityFunctional
  rw [tau.valueTrace_smooth]
  have hTrace : smoothSphereValue
      (referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B
        P.native_data.1.1.1 lam y (referenceRadius delta Rstar p L y)
        (⟨fun _ => (1 : ℝ),contDiff_const⟩ : SmoothData)) = polynomialSphere (C 1) := by
    ext z
    simp [smoothSphereValue,referencePhysicalPullbackData,polynomialSphere]
  rw [hTrace]
  change ⟪_, polynomialSphereL2 (C 1)⟫_ℝ = _
  rw [real_inner_comm]
  rfl

/-- Covering packets transfer the already proved constant-functional
normalization to the entire closed cylinder's literal sphere mean. -/
theorem sphereMean_native_density_eq_one_on_cylinder
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (tau : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L) (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hNorm : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      nativeMixedKernelDensityFunctional hO hD tau S L (cover.packet i) lam delta Rstar p Psi
        (⟨fun _ => (1 : ℝ),contDiff_const⟩ : SmoothData) y = 1) :
    ∀ y ∈ cylinder, sphereMean ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))) = 1 := by
  intro y hy
  obtain ⟨i,hi⟩ := cover.covers_cylinder y hy
  exact (nativeMixedKernelDensityFunctional_one_eq_sphereMean hO hD tau S L
    (cover.packet i) lam delta Rstar p Psi y).symm.trans (hNorm i y ⟨hy,hi⟩)

/-- The SAME source-matched cutoff and normalized density give the actual
fixed-frame zero-fiber-mean input, including outside the cylinder. -/
theorem sphereMean_cutoff_native_density_sub_one_eq_zero
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (Psi : R3 → SphereSobolev (3/2 : ℝ)) (chi : R3 → ℝ)
    (hSupport : Function.support chi ⊆ cylinder)
    (hMean : ∀ y ∈ cylinder, sphereMean ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))) = 1) :
    ∀ y : R3, sphereMean (chi y •
      ((sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)) -
          polynomialSphereL2 (C 1))) = 0 := by
  intro y
  by_cases hy : y ∈ cylinder
  · rw [map_smul,map_sub,hMean y hy,sphereMean_constant_one,sub_self,smul_zero]
  · have hc : chi y = 0 := by
      by_contra hh
      exact hy (hSupport hh)
    rw [hc,zero_smul,map_zero]

/-- Retain every existing same-kernel output and add the actual fiber mean of that same density. -/
theorem exists_global_native_density_operator_and_fiber_mean_one
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
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        referencePhysicalDensityOperator S.g1 L (cover.packet i).y0 (cover.packet i).Phi
          (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          S.g1_admissible hcalc hF hO hD τ0 S.g2 lam
          (referenceRadius delta Rstar p L) Psi y = 0 ) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi (⟨fun _ => (1 : ℝ),contDiff_const⟩ : SmoothData) y = 1) ∧
      ∀ y ∈ cylinder, sphereMean ((sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))) = 1 := by
  obtain ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,hOperator,hNorm⟩ :=
    exists_global_native_density_operator_and_constant_normalization
      hcalc hreg hF hO hD τ0 hKernel S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius
  refine ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,hOperator,hNorm,?_⟩
  exact sphereMean_native_density_eq_one_on_cylinder hO hD τ0 S L lam delta Rstar p cover Psi hNorm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
