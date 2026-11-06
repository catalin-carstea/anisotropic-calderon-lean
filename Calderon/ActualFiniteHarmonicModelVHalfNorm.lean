import Calderon.ActualFiniteHarmonicModelFirstBalancedAngularJets
import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficientJets
import Calderon.ActualFiniteHarmonicModelFirstAngularHalfNorm
import Calderon.ActualMixedDensityHigherCoefficientJets

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  BalancedAngularShift ActualModelCommutatorWords ActualReferenceDDHigherGeometryJets
  ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  ActualPhysicalMixedFirst ActualMixedDensityHigherCoefficientJets
  ActualMixedDensityScalarZeroForm CoordinateBootstrapJets
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ReferenceDensityBounds
  SmoothMetricFrame SmoothSphereFields SmoothAngularApplication PrincipalCommutator
  ConformalDepth ReferenceWeightedApproximation ActualReferenceDDSpectralTransport
  ActualReferenceDDNormalizedCoefficient ActualScalarPrincipalAdjoint
  ActualNormalizedSecondMetricDrift ActualNormalizedSecondModelDefectCoefficients
  ActualNormalizedSecondDriftAngularAllocation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeVHalfNormFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeVHalfNormFunction
theorem exists_nativeV_uniform_half_norm_bound
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ j : Fin 3, ∀ F : smoothCompactFiniteSphereCore hO hD,
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F) x‖ ≤
        (C*eps/beta)*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := by
  obtain ⟨CH,hCH,hH⟩ := exists_modelDefectFirstNormalizedCoefficient_uniform_coordinate_word_smallness
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨J,hJ,hjets⟩ := exists_native_first_angular_coefficients_uniform_coordinate_word_bounds g1 g2 hg1 hg2 L hL K hK
  let S : ℝ := (∑ a : Fin 3, ‖normalizedDerivative hF hO hD a+normalizedRaising hF hO hD a‖)+
    3*(2+2*(2 : ℝ)^(1/2 : ℝ))
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact add_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
  refine ⟨CH+J*S,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j F
  let r : ℝ := referenceRadius δ R p L x
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hbpos : 0 < beta := by linarith
  let rate := eps/beta
  have hrate : 0 ≤ rate := div_nonneg heps hbpos.le
  change r*beta^2 ≤ eps at hsmall
  have hrb : r*beta ≤ rate := (le_div_iff₀ hbpos).2 (by nlinarith)
  have her : eps*r ≤ rate := (mul_le_of_le_one_left hr.le heps1).trans
    ((le_mul_of_one_le_right hr.le hb).trans hrb)
  let c (a : Fin 3) : ℝ := -physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x
  have hc (a : Fin 3) : |c a| ≤ J*rate := by
    have ht := (hjets lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [] (by simp) j a 0 0).1
    have hm : |physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x| ≤ J*eps*r := by
      simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using ht
    simpa only [c,abs_neg] using hm.trans (by nlinarith [mul_le_mul_of_nonneg_left her hJ.le])
  let KK := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) j x
  let s : ℝ := adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
    (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j-
    2*(r*normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x))
  let M : SphereL2 →L[ℝ] SphereL2 := s • inverseDegreeMultiplier hO hD-(KK+KK.adjoint)
  let N := modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x
  have hKK : PreservesSphereSpectralGraphs hO hD KK :=
    preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p _ j x
  have hM : PreservesSphereSpectralGraphs hO hD M :=
    preservesSphereSpectralGraphs_sub hO hD _ _
      (preservesSphereSpectralGraphs_smul hO hD _ _ (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD))
      (preservesSphereSpectralGraphs_add hO hD _ _ hKK (preservesSphereSpectralGraphs_adjoint hO hD KK hKK))
  have hN : ‖N‖ ≤ CH*rate := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one,rate,mul_div_assoc] using
      hH lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j [] (by simp)
  have hMN : N = M+∑ a : Fin 3, c a •
      (normalizedDerivative hF hO hD a+normalizedRaising hF hO hD a) := by
    dsimp only [N,M,KK,s,r,c,modelDefectFirstNormalizedCoefficient,normalizedSecondDriftFirstNormalizedCoefficient]
    simp only [Fin.sum_univ_three]
    module
  have hA : nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x =
      M (coreWeightOperator hO hD (besselWeight 1) F x)+
      ∑ a : Fin 3, c a • (coreDerivative hO hD hF a F x+coreRaising hO hD hF a F x) := by
    rw [nativeV_firstAngular_action]
    dsimp only [M,KK,s,r,c]
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      inverseDegreeMultiplier_coreWeight_one_apply hO hD F x,neg_smul,Finset.sum_neg_distrib,sub_smul]
    abel
  have ht := norm_coreWeight_half_first_angular_le hO hD hF M N hM _ F c x (CH*rate) (J*rate)
    (by positivity) hN hc hMN hA
  convert ht using 1 <;> dsimp only [rate,S] <;> ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
