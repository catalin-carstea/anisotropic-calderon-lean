import Calderon.ActualReferenceRaisingAndDriftProfile
import Calderon.FiniteProfileNormComparison
import Calderon.AmbientReferenceCoercivity
import Calderon.ActualFiniteHarmonicModelReferenceEnergyRepresentative

-- Exact original mathematical payload: ActualReferenceProjectedEnergies

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualReferenceProjectedEnergies
open SphereHarmonic SpectralCoreRegularity SmoothSphereFields
  AmbientReferenceRaising HarmonicRaisingModel ReferenceDensityBounds

/-- The raising energy at the output degree corresponding to positive input `m+1`. -/
def referenceProjectedRaisingEnergy (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (m : ℕ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x) *
    ‖sphereHarmonicCoordinate hO hD ((m+1)+1)
      (referenceAllModeRaising hF hO hD g hg L lam f G hG x)‖^2

/-- The lowering energy retains output degree zero when the input degree is one. -/
def referenceProjectedLoweringEnergy (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (m : ℕ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x) *
    ‖sphereHarmonicCoordinate hO hD m
      (referenceAllModeLowering hF hO hD g hg L lam f G hG x)‖^2

theorem referenceProjectedRaisingEnergy_eq_harmonic (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (m : ℕ) :
    referenceProjectedRaisingEnergy hF hO hD g hg L lam f G hG m =
      referenceHarmonicRaisingEnergy hF g L lam m
        (fun y => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG y)) f := by
  unfold referenceProjectedRaisingEnergy referenceHarmonicRaisingEnergy
  simp_rw [referenceAllModeRaising_coordinate hF hO hD g hg L lam f G hG m]

theorem referenceProjectedLoweringEnergy_eq_harmonic (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (m : ℕ) :
    referenceProjectedLoweringEnergy hF hO hD g hg L lam f G hG m =
      referenceHarmonicLoweringEnergy hF g L lam m
        (fun y => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG y)) f := by
  unfold referenceProjectedLoweringEnergy referenceHarmonicLoweringEnergy
  simp_rw [referenceAllModeLowering_coordinate hF hO hD g hg L lam f G hG m]

end OAI.AnisotropicCalderon.ActualReferenceProjectedEnergies


-- Exact original mathematical payload: ActualReferenceCoercivityBetaThreshold

set_option autoImplicit false
universe u
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualReferenceCoercivityBetaThreshold
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift BoundedSpectralMultiplier SmoothSphereFields SmoothAngularApplication
  AmbientReferenceRaising SmoothMetricFrame MovingFrameConnection ActualReferenceParallelRaising
  ActualReferenceModelTrace ActualReferenceOrdinaryPrincipal ActualReferenceDDNormalizedCoefficient
  ActualReferenceDDSpectralTransport ActualReferenceDDQuadraticBound ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherGeometryJets
  ActualNormalizedSecondMetricDrift ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondDriftNativeAdjunction ActualNormalizedSecondDriftWeightedCoefficients
  ActualNormalizedSecondDriftDefectWeightedJets ActualNormalizedSecondDriftDefectCoefficients
  ActualScalarPrincipalAdjoint ActualUnboundedFirstPrincipalFormBound ActualSupportLocalSecondForm
  ActualHorizontalNormBridge ReferenceDensityBounds PrincipalCommutator ConformalDepth RadiusProfile
  WeightedBaseSpectral SectionFiveErrorForms ReferenceWeightedApproximation
  ActualNormalizedSecondDriftDefectBilinearBound ActualNormalizedSecondDriftDefectBalancedBound
  ActualNormalizedSecondDriftDefectAbsorption

open FiniteProfileRaisingGain AngularPolynomial WeightedFischerSquare FischerConnectionTransport
  IntegratedFischerIdentities FiniteRaisingEnergy WeightedRaisingBounds ProfileHessianEnergy
  IntegratedProfileConvexity FullCovectorCurvature ActualNormalizedSecondDriftUniformAbsorption

open FiniteProfileNormComparison

theorem exists_referenceCoercivity_secondDrift_profile_with_beta_threshold (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (K : Set R3) (hK : IsCompact K) :
    ∃ L cRaise : ℝ, 0 < L ∧ 0 < cRaise ∧
      ∀ betaMin ε : ℝ, 0 < ε → ∃ p : ℕ, 2 ≤ p ∧ ∃ R : ℝ, 0 < R ∧
        (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          max (1:ℝ) betaMin ≤ referenceProfileNorm g lam δ R p L x ∧
          ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
          referenceRadius δ R p L x * referenceProfileNorm g lam δ R p L x^2 ≤ ε) ∧
        (∀ (τ : Type u) [Fintype τ], ∀ hF : SphereFischerInner,
          ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ m : ℕ, ∀ b : τ → MvPolynomial (Fin 3) ℝ,
          (∀ j, b j ∈ harmonicHomogeneous (m+1)) →
          ∀ c : R3 → τ → ℝ, ContDiff ℝ ∞ c → HasCompactSupport c →
          (∀ x ∉ K, finitePolynomialField b c x = 0) →
          cRaise*referenceProfileModeEnergy g hg lam δ R L p (m+1) b c ≤
            referenceRaisingEnergy g L lam b c (referenceLogRadius δ R p L) m -
              referenceLoweringEnergy g L lam b c (referenceLogRadius δ R p L) m) ∧
        (∀ tau : ℝ, 0 < tau → ∀ lam ∈ Set.Icc (0 : ℝ) 1,
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
          (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
          ∀ V : R3 × R3 → ℝ, ∀ hV : ContDiff ℝ ∞ V,
          (∀ x ∉ K, ∀ theta : UnitSphere, V (x,theta.val)=0) →
          |∫ x, referenceDensityFamily g L (lam,x)*
            ⟪normalizedSecondWeightedDriftAdjointDefect hO hD g g2 hg L lam δ R p G hG x,ambientSphereL2 V hV x⟫_ℝ| ≤
            tau*referenceHorizontalNormSquare hO hD g L lam (actualReferenceBeta g L lam δ R p) G hG +
              (ε^2/tau)*referenceHorizontalNormSquare hO hD g L lam (actualReferenceBeta g L lam δ R p) V hV) := by
  obtain ⟨L,c0,nu,J1,J2,D,hL,hc0,hnu,hJ1,hJ2,hDbound,hbounds⟩ := exists_referenceProfileBounds g hg K hK
  obtain ⟨C,hC,hcurv⟩ := exists_referenceIntegratedCurvature_allFinite_uniform_bound.{u} g hg L hL K hK
  obtain ⟨Cd,hCd,hdrift⟩ := exists_normalizedSecondDriftDefect_horizontal_absorption_form_bound
    hO hD g g2 hg hg2 L hL K hK
  let a := min (1:ℝ) (nu/8)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hasmall : a ≤ nu/8 := min_le_right _ _
  have ha1 : a ≤ 1 := min_le_left _ _
  refine ⟨L,referenceProfileCoercivityConstant a nu,hL,referenceProfileCoercivityConstant_pos a nu ha hnu,?_⟩
  intro betaMin ε hε
  let betaFloor := max (1:ℝ) betaMin
  let beta0 := max betaFloor (50*C/nu)
  have hfloor : betaFloor ≤ beta0 := le_max_left _ _
  have hb0 : 1 ≤ beta0 := (le_max_left (1:ℝ) betaMin).trans hfloor
  have hab : a ≤ beta0 := ha1.trans hb0
  have habsorb : 50*C ≤ nu*beta0 := by
    have hh := (div_le_iff₀ hnu).mp (le_max_right betaFloor (50*C/nu))
    simpa only [beta0,mul_comm] using hh
  let e : ℝ := ε/(Cd+1)
  have hd : 0 < Cd+1 := by linarith
  have he : 0 < e := div_pos hε hd
  have hele : e ≤ ε := by
    dsimp [e]
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg hε.le hCd.le]
  have hCe : Cd*e ≤ ε := by
    dsimp [e]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  obtain ⟨p,hp,R,hR,hprofile⟩ := referenceProfileBounds_choose_degree_radius g K L c0 nu J1 J2 D hc0 hbounds beta0 e he
  refine ⟨p,hp,R,hR,?_,?_,?_⟩
  · intro lam hlam δ hδ hδ1 x hx
    exact ⟨hfloor.trans (hprofile lam hlam δ hδ hδ1 x hx).1,
      (hprofile lam hlam δ hδ hδ1 x hx).2.1.trans hele,
      (hprofile lam hlam δ hδ hδ1 x hx).2.2.trans hele⟩
  · intro τ inst hF lam hlam δ hδ hδ1 m b hb c hc hcompact hzero
    have hhcurv : |referenceIntegratedFullCovectorCurvature g L lam b c| ≤
        C*((m:ℝ)+1)^2*referenceFischerMass g L lam b c := by
      simpa only [Nat.cast_add,Nat.cast_one] using hcurv τ hF lam hlam (m+1) (by omega) b hb c hc hcompact hzero
    exact referenceProfileModeEnergy_coercive hF g hg K hK.isClosed L c0 nu J1 J2 D hL hnu hbounds
      lam hlam δ hδ hδ1 R hR p (by omega) m b hb c hc hcompact hzero a beta0 C ha hb0 hC.le
      hasmall hab habsorb (fun x hx => (hprofile lam hlam δ hδ hδ1 x hx).1) hhcurv
  · intro tau htau lam hlam δ hδ hδ1 G hG hzG V hV hzV
    have hp1 : 1 ≤ p := by omega
    have hb := fun x hx => hb0.trans (hprofile lam hlam δ hδ hδ1 x hx).1
    have hsmall := fun x hx => (hprofile lam hlam δ hδ hδ1 x hx).2.2
    have ht := hdrift tau htau lam hlam δ hδ hδ1 R hR p hp1 e he.le hb hsmall G hG hzG V hV hzV
    have hNV : 0 ≤ referenceHorizontalNormSquare hO hD g L lam (actualReferenceBeta g L lam δ R p) V hV :=
      referenceHorizontalNormSquare_nonneg hO hD g L lam (actualReferenceBeta g L lam δ R p)
        (fun x => (actualReferenceBeta_pos g hg L lam δ R p hL hδ hR hp1 x).le) V hV
    have hsquare : (Cd*e)^2 ≤ ε^2 := by nlinarith [mul_nonneg hCd.le he.le]
    exact ht.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hsquare htau.le) hNV))

end OAI.AnisotropicCalderon.ActualReferenceCoercivityBetaThreshold


-- Exact original mathematical payload: ActualReferenceProjectedCoercivityBetaThreshold

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualReferenceProjectedCoercivityBetaThreshold
open SphereHarmonic SpectralCoreRegularity SmoothSphereFields
  AmbientReferenceRaising HarmonicRaisingModel ReferenceDensityBounds
  CovariantHarmonicEnergy FischerConnectionTransport FiniteProfileNormComparison
  ActualReferenceProjectedEnergies ActualReferenceCoercivityBetaThreshold
  ActualHorizontalNormBridge ReferenceWeightedApproximation
  ActualNormalizedSecondDriftNativeAdjunction SmoothMetricFrame RadiusProfile ConformalDepth

theorem exists_reference_projected_coercivity_with_beta_threshold_and_secondDrift
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (K : Set R3) (hK : IsCompact K) :
    ∃ L cRaise : ℝ, 0 < L ∧ 0 < cRaise ∧
      ∀ betaMin ε : ℝ, 0 < ε → ∃ p : ℕ, 2 ≤ p ∧ ∃ R : ℝ, 0 < R ∧
        (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          max (1:ℝ) betaMin ≤ referenceProfileNorm g lam δ R p L x ∧
          ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
          referenceRadius δ R p L x * referenceProfileNorm g lam δ R p L x^2 ≤ ε) ∧
        (∀ hF : SphereFischerInner,
          ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ m : ℕ, ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
          (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
          cRaise * referenceHarmonicModeEnergy g lam δ R L p (m+1)
            (fun y => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG y)) ≤
            referenceProjectedRaisingEnergy hF hO hD g hg L lam
              (referenceLogRadius δ R p L) G hG m -
            referenceProjectedLoweringEnergy hF hO hD g hg L lam
              (referenceLogRadius δ R p L) G hG m) ∧
        (∀ tau : ℝ, 0 < tau → ∀ lam ∈ Set.Icc (0:ℝ) 1,
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
          (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
          ∀ V : R3 × R3 → ℝ, ∀ hV : ContDiff ℝ ∞ V,
          (∀ x ∉ K, ∀ theta : UnitSphere, V (x,theta.val)=0) →
          |∫ x, referenceDensityFamily g L (lam,x) *
            ⟪normalizedSecondWeightedDriftAdjointDefect hO hD g g2 hg L lam δ R p G hG x,
              ambientSphereL2 V hV x⟫_ℝ| ≤
            tau * referenceHorizontalNormSquare hO hD g L lam
              (actualReferenceBeta g L lam δ R p) G hG +
            (ε^2/tau) * referenceHorizontalNormSquare hO hD g L lam
              (actualReferenceBeta g L lam δ R p) V hV) := by
  obtain ⟨L,cRaise,hL,hcRaise,hprofile⟩ :=
    exists_referenceCoercivity_secondDrift_profile_with_beta_threshold.{0} hO hD g g2 hg hg2 K hK
  refine ⟨L,cRaise,hL,hcRaise,?_⟩
  intro betaMin ε hε
  obtain ⟨p,hp,R,hR,hsmall,hfinite,hdrift⟩ := hprofile betaMin ε hε
  refine ⟨p,hp,R,hR,hsmall,?_,hdrift⟩
  intro hF lam hlam δ hδ hδ1 m G hG hz
  let U : R3 → SphereL2 := ambientSphereL2 G hG
  have hU : ContDiff ℝ ∞ U := contDiff_ambientSphereL2 G hG
  have hzU : ∀ x ∉ K, U x = 0 := fun x hx => ambientSphereL2_eq_zero G hG x (hz x hx)
  obtain ⟨n,b,c,hb,hc,hcompact,hrep,hcz⟩ :=
    exists_smooth_compact_coordinates_sphereHarmonicCoordinate hO hD (m+1) U hU K hK hzU
  have hpoly : ∀ x ∉ K, finitePolynomialField b c x = 0 := by
    intro x hx
    simp only [finitePolynomialField,hcz x hx,Pi.zero_apply,zero_smul,Finset.sum_const_zero]
  have hproj := contDiff_sphereHarmonicCoordinate hO hD (m+1) U hU
  have hmode := referenceHarmonicModeEnergy_eq_polynomial g hg lam δ R L p (m+1)
    b hb c _ hc hproj hrep
  have hraise := referenceHarmonicRaisingEnergy_eq_polynomial hF g hg L lam m
    b hb c _ hc hproj hrep (referenceLogRadius δ R p L)
  have hlower := referenceHarmonicLoweringEnergy_eq_polynomial hF g hg L lam m
    b hb c _ hc hproj hrep (referenceLogRadius δ R p L)
  have hh := hfinite (Fin n) hF lam hlam δ hδ hδ1 m b hb c hc hcompact hpoly
  rw [referenceProjectedRaisingEnergy_eq_harmonic,
    referenceProjectedLoweringEnergy_eq_harmonic]
  change cRaise * referenceHarmonicModeEnergy g lam δ R L p (m+1)
    (fun y => sphereHarmonicCoordinate hO hD (m+1) (U y)) ≤
    referenceHarmonicRaisingEnergy hF g L lam m
      (fun y => sphereHarmonicCoordinate hO hD (m+1) (U y)) (referenceLogRadius δ R p L) -
    referenceHarmonicLoweringEnergy hF g L lam m
      (fun y => sphereHarmonicCoordinate hO hD (m+1) (U y)) (referenceLogRadius δ R p L)
  rw [hmode,hraise,hlower]
  exact hh

end OAI.AnisotropicCalderon.ActualReferenceProjectedCoercivityBetaThreshold


-- Exact original mathematical payload: ActualReferenceAllModeCoercivityBetaThreshold

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualReferenceAllModeCoercivityBetaThreshold
open SphereHarmonic SpectralCoreRegularity SmoothSphereFields
  AmbientReferenceRaising HarmonicRaisingModel ReferenceDensityBounds
  CovariantHarmonicEnergy ActualReferenceProjectedEnergies
  ActualReferenceProjectedCoercivityBetaThreshold AmbientReferenceCoercivity
  AmbientReferenceProfileEnergy ActualHorizontalNormBridge
  ReferenceWeightedApproximation ActualNormalizedSecondDriftNativeAdjunction
  SmoothMetricFrame RadiusProfile ConformalDepth

theorem exists_referenceAllMode_coercivity_with_beta_threshold_and_secondDrift
    (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (K : Set R3) (hK : IsCompact K) :
    ∃ L cRaise : ℝ, 0 < L ∧ 0 < cRaise ∧
      ∀ betaMin ε : ℝ, 0 < ε → ∃ p : ℕ, 2 ≤ p ∧ ∃ R : ℝ, 0 < R ∧
        (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          max (1:ℝ) betaMin ≤ referenceProfileNorm g lam δ R p L x ∧
          ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
          referenceRadius δ R p L x * referenceProfileNorm g lam δ R p L x^2 ≤ ε) ∧
        (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
          (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
          (∀ x, sphereMean (ambientSphereL2 G hG x)=0) →
          cRaise * referenceAllModeProfileEnergy hO hD g hg lam δ R L p G hG ≤
            referenceAllModeRaisingEnergy hF hO hD g hg L lam
              (referenceLogRadius δ R p L) G hG -
            referenceAllModeLoweringEnergy hF hO hD g hg L lam
              (referenceLogRadius δ R p L) G hG) ∧
        (∀ tau : ℝ, 0 < tau → ∀ lam ∈ Set.Icc (0:ℝ) 1,
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
          (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
          ∀ V : R3 × R3 → ℝ, ∀ hV : ContDiff ℝ ∞ V,
          (∀ x ∉ K, ∀ theta : UnitSphere, V (x,theta.val)=0) →
          |∫ x, referenceDensityFamily g L (lam,x) *
            ⟪normalizedSecondWeightedDriftAdjointDefect hO hD g g2 hg L lam δ R p G hG x,
              ambientSphereL2 V hV x⟫_ℝ| ≤
            tau * referenceHorizontalNormSquare hO hD g L lam
              (actualReferenceBeta g L lam δ R p) G hG +
            (ε^2/tau) * referenceHorizontalNormSquare hO hD g L lam
              (actualReferenceBeta g L lam δ R p) V hV) := by
  obtain ⟨L,cRaise,hL,hcRaise,hprofile⟩ :=
    exists_reference_projected_coercivity_with_beta_threshold_and_secondDrift hO hD g g2 hg hg2 K hK
  refine ⟨L,cRaise,hL,hcRaise,?_⟩
  intro betaMin ε hε
  obtain ⟨p,hp,R,hR,hsmall,hmode,hdrift⟩ := hprofile betaMin ε hε
  refine ⟨p,hp,R,hR,hsmall,?_,hdrift⟩
  intro lam hlam δ hδ hδ1 G hG hz hmean
  have hfinite (n : ℕ) :
      cRaise * referenceAllModeProfileCutEnergy hO hD g hg lam δ R L p n G hG ≤
        referenceAllModeRaisingCutEnergy hF hO hD g hg L lam
          (referenceLogRadius δ R p L) n G hG -
        referenceAllModeLoweringCutEnergy hF hO hD g hg L lam
          (referenceLogRadius δ R p L) n G hG := by
    rw [referenceAllModeProfileCutEnergy_eq_sum_modes hF hO hD g hg lam δ R L p n
        hδ hR hL (by omega) G hG K hK hz,
      referenceAllModeRaisingCutEnergy_eq_sum_modes hF hO hD g hg lam δ R L p n
        hδ hR hL (by omega) G hG K hK hz,
      referenceAllModeLoweringCutEnergy_eq_sum_modes hF hO hD g hg lam δ R L p n
        hδ hR hL (by omega) G hG K hK hz,
      Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro m _
    simpa only [referenceProjectedRaisingEnergy_eq_harmonic,
      referenceProjectedLoweringEnergy_eq_harmonic] using
      hmode hF lam hlam δ hδ hδ1 m G hG hz
  have hf := contDiff_log_referenceRadius δ R p L hδ hR
  exact le_of_tendsto_of_tendsto
    ((tendsto_referenceAllModeProfileCutEnergy hO hD g hg lam δ R L p hδ hR hL
      (by omega) G hG K hK hz hmean).const_mul cRaise)
    ((tendsto_referenceAllModeRaisingCutEnergy hF hO hD g hg L lam _ hf G hG K hK hz hmean).sub
      (tendsto_referenceAllModeLoweringCutEnergy hF hO hD g hg L lam _ hf G hG K hK hz))
    (Filter.Eventually.of_forall hfinite)

end OAI.AnisotropicCalderon.ActualReferenceAllModeCoercivityBetaThreshold


-- Exact original mathematical payload: ActualFiniteHarmonicModelReferenceEnergyBetaThreshold

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient SpectralWeightedGraph
  SmoothSphereFields AmbientReferenceCoercivity AmbientReferenceProfileEnergy ReferenceDensityBounds
  ReferenceWeightedApproximation ConformalDepth ActualReferenceAllModeCoercivityBetaThreshold
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev energyThresholdFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] energyThresholdFunction

theorem exists_nativeReference_uniform_energy_profile_with_beta_threshold
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2) (K : Set R3) (hK : IsCompact K) :
    ∃ L cRaise : ℝ, 0 < L ∧ 0 < cRaise ∧
      ∀ betaMin eps : ℝ, 0 < eps → ∃ p : ℕ, 2 ≤ p ∧ ∃ R : ℝ, ∃ hR : 0 < R,
        (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          max (1:ℝ) betaMin ≤ actualReferenceBeta g1 L lam δ R p x ∧
          ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ eps ∧
          referenceRadius δ R p L x*(actualReferenceBeta g1 L lam δ R p x)^2 ≤ eps) ∧
        ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
          ∀ F : smoothCompactFiniteSphereCore hO hD,
          tsupport (F : R3 → SphereL2) ⊆ K → (∀ x, sphereMean (F x)=0) →
          cRaise*(∫ x : R3, referenceDensityFamily g1 L (lam,x)*
            finiteCoreReferenceProfileEnergy hO hD g1 hg1 L lam (actualReferenceBeta g1 L lam δ R p x) F x) ≤
            (∫ x : R3, referenceDensityFamily g1 L (lam,x)*‖nativeT hO hD hF g1 hg1 L lam δ R p hδ hR F x‖^2)-
            (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
              ‖nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR F x+nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F x‖^2) := by
  obtain ⟨L,c,hL,hc,hgain⟩ := exists_referenceAllMode_coercivity_with_beta_threshold_and_secondDrift
    hF hO hD g1 g2 hg1 hg2 K hK
  refine ⟨L,c,hL,hc,?_⟩
  intro betaMin eps heps
  obtain ⟨p,hp,R,hR,hprofile,hfields,hdrift⟩ := hgain betaMin eps heps
  refine ⟨p,hp,R,hR,hprofile,?_⟩
  intro lam hlam δ hδ hδ1 F hsupp hmean
  let r := coreAmbientRepresentative hO hD F
  have hz (x : R3) (hx : x ∉ K) (theta : UnitSphere) : representativeAmbient hO hD r (x,theta.val)=0 :=
    representativeAmbient_zero_outside hO hD r x theta.val (fun hy => hx (hsupp hy))
  have hm (x : R3) : sphereMean (ambientSphereL2 (representativeAmbient hO hD r)
      (contDiff_representativeAmbient hO hD r) x)=0 := by
    rw [ambientSphereL2_representative hO hD r x]
    exact hmean x
  have ht := hfields lam hlam δ hδ hδ1 (representativeAmbient hO hD r)
    (contDiff_representativeAmbient hO hD r) hz hm
  rw [referenceAllModeProfileEnergy_representative hO hD g1 hg1 lam δ R L p F r,
    referenceAllModeRaisingEnergy_representative hO hD hF g1 hg1 L lam δ R p hδ hR F r,
    referenceAllModeLoweringEnergy_representative hO hD hF g1 hg1 L lam δ R p hδ hR F r] at ht
  exact ht

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
