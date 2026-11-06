import Calderon.ActualKnownSideHalfGaugeDensityIdentification
import Calderon.ReferencePhysicalPoissonDensity
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualNormalizedSecondMetricDrift NativePolynomialBulkMoments

attribute [local irreducible] referencePhysicalHalfGaugeConormalDensity
  referencePhysicalHalfGaugeCollarForcing referencePhysicalGaugeCoefficientJets ordinaryPrincipalL
  sphereSobolevInclusionL sphereSobolevZeroEquiv sphereSobolevSingleL

theorem exists_original_global_native_density_knownSide_eq_fixedPoissonDensity
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
 :
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
        lam • y ∈ S.W → Psi y = referencePhysicalPoissonDensity S.g1 S.g1_admissible L
          (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
          (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          hcalc hF hO hD τ0
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
  apply exists_original_global_native_density_knownSide_eq_halfGaugeConormalDensity
    hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K
    hdelta hRstar hlam hlamRoom hRadius unitBallSmoothCutoff parametrixCollarFactor unitBallSmoothCutoff.contDiff contDiff_parametrixCollarFactor unitBallSmoothCutoff.hasCompactSupport (1/4) (by norm_num) parametrixCollarFactor_zero_of_mem_ball parametrixBoundaryCutoff contDiff_parametrixBoundaryCutoff
  intro i y hy hyKnown v hV
  have hq : lam ∈ Icc (0 : ℝ) 1 := ⟨hlam.le,hlamRoom.trans cover.dilation_le_one⟩
  have hCenter : ‖y-(cover.packet i).y0‖ ≤ 4*(cover.packet i).rho := ((cover.packet i).centers_room y hy.2).1.le
  have hrpos := referenceRadius_pos delta Rstar p L y hdelta hRstar
  have hr : |referenceRadius delta Rstar p L y| ≤ 4*(cover.packet i).rho := by
    rw [abs_of_pos hrpos]
    exact ((hRadius y hy.1).trans (cover.radius_room i)).le
  exact referencePhysicalPoissonDensity_reproduces_native_harmonic_smooth
    S.g1 S.g1_admissible L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
    (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
    (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
    hcalc hF hO hD τ0 hreg lam hq y hCenter (referenceRadius delta Rstar p L y) hr v hV

theorem exists_uniform_nativeCover_referencePhysicalPoissonDensity_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ (i : Fin cover.count) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
      ∀ (y : R3), ‖y-(cover.packet i).y0‖ ≤ 4*(cover.packet i).rho →
      ∀ (r : ℝ), |r| ≤ 4*(cover.packet i).rho →
      ‖referencePhysicalPoissonDensity S.g1 S.g1_admissible L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data hcalc hF hO hD τ0 (q,(y,r))‖ ≤ C0 ∧
      ‖referencePhysicalPoissonDensity S.g1 S.g1_admissible L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data hcalc hF hO hD τ0 (q,(y,r)) - (sphereSobolevSingleL (3/2 : ℝ) 0 ⟨polynomialSphereL2 (MvPolynomial.C 1),polynomialSphereL2_mem 0 _ (C_harmonicHomogeneous 1)⟩)‖ ≤ C0 * |r| := by
  let family (i : Fin cover.count) := referencePhysicalPoissonDensity S.g1 S.g1_admissible L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data hcalc hF hO hD τ0
  let K (i : Fin cover.count) : Set (ℝ × (R3 × ℝ)) := Icc (0 : ℝ) 1 ×ˢ
    (closedBall (cover.packet i).y0 (4*(cover.packet i).rho) ×ˢ Icc (-4*(cover.packet i).rho) (4*(cover.packet i).rho))
  have hK (i : Fin cover.count) : IsCompact (K i) :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  have hBounds : ∀ i : Fin cover.count, ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ (q : ℝ), q ∈ Icc (0 : ℝ) 1 → ∀ (y : R3), ‖y-(cover.packet i).y0‖ ≤ 4*(cover.packet i).rho →
      ∀ (r : ℝ), |r| ≤ 4*(cover.packet i).rho →
      ‖family i (q,(y,r))‖ ≤ C0 ∧ ‖family i (q,(y,r))-(sphereSobolevSingleL (3/2 : ℝ) 0 ⟨polynomialSphereL2 (MvPolynomial.C 1),polynomialSphereL2_mem 0 _ (C_harmonicHomogeneous 1)⟩)‖ ≤ C0*|r| := by
    intro i
    obtain ⟨C1,hC1,hB⟩ := exists_compact_uniform_referencePhysicalPoissonDensity_bound S.g1 S.g1_admissible L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data hcalc hF hO hD τ0 hreg (K i) (hK i)
    obtain ⟨C2,hC2,hD'⟩ := exists_compact_linear_referencePhysicalPoissonDensity_sub_one_bound S.g1 S.g1_admissible L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data hcalc hF hO hD τ0 hreg (K i) (hK i)
    refine ⟨max C1 C2,hC1.trans (le_max_left _ _),?_⟩
    intro q hq y hy r hr
    have hp : (q,(y,r)) ∈ K i := by
      refine ⟨hq,?_,?_⟩
      · simpa only [mem_closedBall,dist_eq_norm] using hy
      · change -4*(cover.packet i).rho ≤ r ∧ r ≤ 4*(cover.packet i).rho
        exact ⟨by linarith [(abs_le.mp hr).1],(abs_le.mp hr).2⟩
    refine ⟨(hB _ hp).trans (le_max_left _ _),?_⟩
    exact (hD' q hq y hy r hp).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg r))
  choose C hC hBound using hBounds
  obtain ⟨C0,hC0⟩ := (Set.finite_range C).bddAbove
  refine ⟨max C0 1,le_max_right _ _,?_⟩
  intro i q hq y hy r hr
  have hCi : C i ≤ max C0 1 := (hC0 ⟨i,rfl⟩).trans (le_max_left _ _)
  have h := hBound i q hq y hy r hr
  exact ⟨h.1.trans hCi,h.2.trans (mul_le_mul_of_nonneg_right hCi (abs_nonneg r))⟩

theorem exists_original_global_native_density_knownSide_uniform_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ (lam delta Rstar bound separation : ℝ) (p : ℕ)
      (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover),
      0 < delta → 0 < Rstar → 0 < lam → lam ≤ cover.dilationCeiling →
      (∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) →
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
        lam • y ∈ S.W → Psi y = referencePhysicalPoissonDensity S.g1 S.g1_admissible L
          (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
          (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          hcalc hF hO hD τ0
          (lam,(y,referenceRadius delta Rstar p L y))) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        lam • y ∈ S.W → ‖Psi y‖ ≤ C0 ∧
          ‖Psi y - (sphereSobolevSingleL (3/2 : ℝ) 0 ⟨polynomialSphereL2 (MvPolynomial.C 1),polynomialSphereL2_mem 0 _ (C_harmonicHomogeneous 1)⟩)‖ ≤ C0 * referenceRadius delta Rstar p L y) ∧
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
  obtain ⟨C0,hC0,hBound⟩ := exists_uniform_nativeCover_referencePhysicalPoissonDensity_bound
    hcalc hreg hF hO hD τ0 S L cover
  refine ⟨C0,hC0,?_⟩
  intro lam delta Rstar bound separation p K hdelta hRstar hlam hlamRoom hRadius
  obtain ⟨Psi,hPsi,hCompactPsi,hFlux,hKnown,hEq,hPDE⟩ :=
    exists_original_global_native_density_knownSide_eq_fixedPoissonDensity
      hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius
  refine ⟨Psi,hPsi,hCompactPsi,hFlux,hKnown,hEq,?_,hPDE⟩
  intro i y hy hyKnown
  have hq : lam ∈ Icc (0 : ℝ) 1 := ⟨hlam.le,hlamRoom.trans cover.dilation_le_one⟩
  have hCenter : ‖y-(cover.packet i).y0‖ ≤ 4*(cover.packet i).rho := ((cover.packet i).centers_room y hy.2).1.le
  have hrpos := referenceRadius_pos delta Rstar p L y hdelta hRstar
  have hr : |referenceRadius delta Rstar p L y| ≤ 4*(cover.packet i).rho := by
    rw [abs_of_pos hrpos]
    exact ((hRadius y hy.1).trans (cover.radius_room i)).le
  have h := hBound i lam hq y hCenter (referenceRadius delta Rstar p L y) hr
  rw [hEq i y hy hyKnown]
  exact ⟨h.1,by simpa only [abs_of_pos hrpos] using h.2⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
