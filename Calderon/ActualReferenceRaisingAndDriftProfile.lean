import Calderon.ActualNormalizedSecondDriftUniformAbsorption
import Calderon.FiniteProfileRaisingGain

set_option autoImplicit false
universe u
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualReferenceRaisingAndDriftProfile
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

theorem exists_referenceRaising_and_secondDrift_uniform_profile (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (K : Set R3) (hK : IsCompact K) :
    ∃ L a nu : ℝ, 0 < L ∧ 0 < a ∧ 0 < nu ∧
      ∀ ε : ℝ, 0 < ε → ∃ p : ℕ, 2 ≤ p ∧ ∃ R : ℝ, 0 < R ∧
        (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
          referenceRadius δ R p L x * referenceProfileNorm g lam δ R p L x^2 ≤ ε) ∧
        (∀ (τ : Type u) [Fintype τ], ∀ hF : SphereFischerInner,
          ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ m : ℕ, ∀ b : τ → MvPolynomial (Fin 3) ℝ,
          (∀ j, b j ∈ harmonicHomogeneous (m+1)) →
          ∀ c : R3 → τ → ℝ, ContDiff ℝ ∞ c → HasCompactSupport c →
          (∀ x ∉ K, finitePolynomialField b c x = 0) →
          referenceProfileFrameEnergy g lam δ R L p b c (m+1) 1 /2 +
            (a/4)*(((m:ℝ)+1)+2)*referenceProfileWeightedFrameEnergy g lam δ R L p b c (m+1) 1 +
            nu*((m:ℝ)+1)^3*referenceProfileMass g lam δ R L p b c ≤
            sphereNormalization 3 (m+1)*(referenceRaisingEnergy g L lam b c (referenceLogRadius δ R p L) m -
              referenceLoweringEnergy g L lam b c (referenceLogRadius δ R p L) m)) ∧
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
  let beta0 := max (1:ℝ) (50*C/nu)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hasmall : a ≤ nu/8 := min_le_right _ _
  have ha1 : a ≤ 1 := min_le_left _ _
  have hb0 : 1 ≤ beta0 := le_max_left _ _
  have hab : a ≤ beta0 := ha1.trans hb0
  have habsorb : 50*C ≤ nu*beta0 := by
    have hh := (div_le_iff₀ hnu).mp (le_max_right (1:ℝ) (50*C/nu))
    simpa only [beta0,mul_comm] using hh
  refine ⟨L,a,nu,hL,ha,hnu,?_⟩
  intro ε hε
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
    exact ⟨(hprofile lam hlam δ hδ hδ1 x hx).2.1.trans hele,
      (hprofile lam hlam δ hδ hδ1 x hx).2.2.trans hele⟩
  · intro τ inst hF lam hlam δ hδ hδ1 m b hb c hc hcompact hzero
    have hhcurv : |referenceIntegratedFullCovectorCurvature g L lam b c| ≤
        C*((m:ℝ)+1)^2*referenceFischerMass g L lam b c := by
      simpa only [Nat.cast_add,Nat.cast_one] using hcurv τ hF lam hlam (m+1) (by omega) b hb c hc hcompact hzero
    exact referenceProfileRaisingEnergy_gain hF g hg K hK.isClosed L c0 nu J1 J2 D hL hnu hbounds
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

end OAI.AnisotropicCalderon.ActualReferenceRaisingAndDriftProfile
