import Calderon.ActualFiniteHarmonicModelFirstBalancedAngularJets
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
  ActualNormalizedSecondMetricDrift
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeHHalfNormFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeHHalfNormFunction
theorem exists_nativeH_uniform_half_norm_bound
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
        (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j F) x‖ ≤
        C*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := by
  obtain ⟨CH,hCH,hH⟩ := exists_nativeHFirstAngularCoefficient_uniform_coordinate_word_bounds
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨M0,hM0,hgeom⟩ := exists_mixed_principal_density_background_jet_bound g1 hg1 L K hK 2
  let S : ℝ := (∑ a : Fin 3, ‖normalizedDerivative hF hO hD a+normalizedRaising hF hO hD a‖)+
    3*(2+2*(2 : ℝ)^(1/2 : ℝ))
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact add_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
  have hM00 : 0 ≤ M0 := le_trans zero_le_one hM0
  refine ⟨CH+26*M0*S,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j F
  let r : ℝ := referenceRadius δ R p L x
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hb0 : 0 ≤ beta := le_trans zero_le_one hb
  have hb2 : 1 ≤ beta^2 := one_le_pow₀ hb
  change r*beta^2 ≤ eps at hsmall
  have hr1 : r ≤ 1 := ((le_mul_of_one_le_right hr.le hb2).trans hsmall).trans heps1
  have her : eps*r ≤ 1 := by nlinarith
  let c (a : Fin 3) : ℝ := -2*referenceMetricGramFrame g1 L (lam,x) a j-
    physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x
  have hc (a : Fin 3) : |c a| ≤ 26*M0 := by
    have he : |referenceMetricGramFrame g1 L (lam,x) a j| ≤ M0 :=
      (hgeom lam hlam x hx).1.1 [] (by simp) a j
    have hm := abs_physicalMixedFirstCoefficient_coordinate_word_le g1 g2 hg1 hg2
      L lam x eps r M0 2 (by norm_num) heps hr.le hM00 (hgeom lam hlam x hx).1 hH8 [] (by simp) a j
    have hm' : |physicalMixedFirstCoefficient g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x| ≤ 24*M0*(eps*r) := by
      convert hm using 1 <;> simp only [coordinateFieldWordPartial,show (2 : ℝ)^2=4 by norm_num] <;> ring
    have hm'' : |physicalMixedFirstCoefficient g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x| ≤ 24*M0 :=
      hm'.trans (by nlinarith)
    dsimp only [c]
    have ht := abs_sub (-2*referenceMetricGramFrame g1 L (lam,x) a j)
      (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x)
    rw [abs_mul] at ht
    rw [abs_neg,abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
    linarith
  let KK := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) j x
  let s : ℝ := adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
    (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j-
    2*(r*normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x))
  let M : SphereL2 →L[ℝ] SphereL2 := s • inverseDegreeMultiplier hO hD-(KK+KK.adjoint)
  let N := nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j x
  have hKK : PreservesSphereSpectralGraphs hO hD KK :=
    preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p _ j x
  have hM : PreservesSphereSpectralGraphs hO hD M :=
    preservesSphereSpectralGraphs_sub hO hD _ _
      (preservesSphereSpectralGraphs_smul hO hD _ _ (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD))
      (preservesSphereSpectralGraphs_add hO hD _ _ hKK (preservesSphereSpectralGraphs_adjoint hO hD KK hKK))
  have hN : ‖N‖ ≤ CH := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using
      hH lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j [] (by simp)
  have hMN : N = M+∑ a : Fin 3, c a •
      (normalizedDerivative hF hO hD a+normalizedRaising hF hO hD a) := by
    dsimp only [N,M,KK,s,r,c,nativeHFirstAngularCoefficient]
    abel
  have hA : nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j F x =
      M (coreWeightOperator hO hD (besselWeight 1) F x)+
      ∑ a : Fin 3, c a • (coreDerivative hO hD hF a F x+coreRaising hO hD hF a F x) := by
    rw [nativeH_apply_eq_firstAngularField]
    dsimp only [nativeHFirstAngularField,M,KK,s,r,c]
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      inverseDegreeMultiplier_coreWeight_one_apply hO hD F x]
    abel
  exact norm_coreWeight_half_first_angular_le hO hD hF M N hM _ F c x CH (26*M0)
    (by positivity) hN hc hMN hA

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
