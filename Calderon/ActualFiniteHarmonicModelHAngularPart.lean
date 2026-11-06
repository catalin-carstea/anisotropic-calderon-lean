import Calderon.ActualFiniteHarmonicModelVLinearExpansion
import Calderon.ActualFiniteHarmonicModelReferenceFirstExpansions

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  ActualPhysicalMixedFirst NormalizedPrincipalMetric ActualScalarPrincipalAdjoint NaturalAngularAdjoint
  ReferenceDensityBounds PrincipalCommutator NormalizedPrincipalMetricSmooth ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def nativeHAngularPart
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j -
    (coreScalar hO hD
      (fun x => adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
        (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j)
      (contDiff_modelAdjointFirstCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j) -
    (2 : ℝ) • coreScalar hO hD (nativeFirstScalarCoefficient g1 g2 L lam δ R p j)
      (contDiff_nativeFirstScalarCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j))

def nativeHAngularPartMass
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (x : R3) : ℝ :=
  4*(∑ a : Fin 3, |referenceMetricGramFrame g1 L (lam,x) a j|)+
    2*|nativeFirstDegreeCoefficient g1 g2 L lam δ R p j x|+
    (∑ a : Fin 3, 2*|physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x|)

lemma nativeHAngularPart_eq_coefficients
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    nativeHAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j =
    2*(nativeReferenceAdjointFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR j-
      nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR j) -
    (2 : ℝ) • (coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p j)
      (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j)*coreDegree hO hD) -
    ∑ a : Fin 3, coreScalar hO hD
      (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j)
      (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
        (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a j)*
      (coreDerivative hO hD hF a+coreRaising hO hD hF a) := by
  unfold nativeHAngularPart nativeH
  rw [nativeV_eq_full_angular_coefficients hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j]
  have he (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) :
      ((2 : ℝ) • A)*B=(2 : ℝ) • (A*B) := by rfl
  rw [he]
  abel

lemma hasCoreScalarExpansionBound_nativeHAngularPart
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (j : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (nativeHAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j) x
      (nativeHAngularPartMass g1 g2 L lam δ R p j x) := by
  rw [nativeHAngularPart_eq_coefficients hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j]
  unfold nativeHAngularPartMass
  apply hasCoreScalarExpansionBound_sub hO hD
  · apply hasCoreScalarExpansionBound_sub hO hD
    · have hd := hasCoreScalarExpansionBound_sub hO hD (coreAngularGenerator hO hD hF) _ _ x _ _
        (hasCoreScalarExpansionBound_nativeReferenceAdjointFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR j x)
        (hasCoreScalarExpansionBound_nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR j x)
      have halg {S : Type} [Ring S] (a : S) : (2 : S)*a=a+a := by noncomm_ring
      rw [halg]
      convert hasCoreScalarExpansionBound_add hO hD (coreAngularGenerator hO hD hF) _ _ x _ _ hd hd using 1 <;> ring
    · have ht := hasCoreScalarExpansionBound_smul hO hD (coreAngularGenerator hO hD hF) _ x _ 2
        (hasCoreScalarExpansionBound_single hO hD (coreAngularGenerator hO hD hF)
          (Sum.inr (Sum.inr (Sum.inr true)))
          (nativeFirstDegreeCoefficient g1 g2 L lam δ R p j)
          (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j) x)
      simpa only [coreAngularGenerator,abs_of_pos (by norm_num : 0 < (2 : ℝ))] using ht
  · apply hasCoreScalarExpansionBound_sum hO hD
    intro a _
    have hp := hasCoreScalarExpansionBound_add hO hD (coreAngularGenerator hO hD hF)
      (coreDerivative hO hD hF a) (coreRaising hO hD hF a) x 1 1
      (hasCoreScalarExpansionBound_generator hO hD hF (Sum.inl a) x)
      (hasCoreScalarExpansionBound_generator hO hD hF (Sum.inr (Sum.inl a)) x)
    have ht := hasCoreScalarExpansionBound_scalar_mul hO hD (coreAngularGenerator hO hD hF)
      _ x (1+1) hp
      (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j)
      (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
        (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a j)
    convert ht using 1 <;> ring

lemma commutator_nativeH_eq_angularPart
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3)
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (hA : ScalarCentral hO hD A) :
    commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j) A =
      commutator (nativeHAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j) A := by
  let S := coreScalar hO hD
    (fun x => adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j)
    (contDiff_modelAdjointFirstCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j) -
    (2 : ℝ) • coreScalar hO hD (nativeFirstScalarCoefficient g1 g2 L lam δ R p j)
      (contDiff_nativeFirstScalarCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j)
  have hsub {R : Type} [Ring R] (u v a : R) (hu : Commute u a) (hv : Commute v a) :
      Commute (u-v) a := hu.sub_left hv
  have hS : Commute S A := by
    dsimp only [S]
    exact hsub _ _ A (hA _ _).symm ((hA _ _).symm.smul_left (2 : ℝ))
  have halg {R : Type} [Ring R] (u s a : R) (h : s*a=a*s) :
      ActualModelCommutatorWords.commutator u a=ActualModelCommutatorWords.commutator (u-s) a := by
    unfold ActualModelCommutatorWords.commutator
    rw [sub_mul,mul_sub,h]
    abel
  exact halg (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j) S A hS.eq

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
