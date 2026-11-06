import Calderon.ActualFiniteHarmonicModelReferenceConnectionExpansion
import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  ActualPhysicalMixedFirst NormalizedPrincipalMetric ActualScalarPrincipalAdjoint NaturalAngularAdjoint
  ReferenceDensityBounds PrincipalCommutator NormalizedPrincipalMetricSmooth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def nativeVAngularPart
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  -(((2 : ℝ) • (coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p j)
      (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j))) * coreDegree hO hD) -
    ∑ a : Fin 3, coreScalar hO hD
        (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j)
        (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
          (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a j) * (coreDerivative hO hD hF a+coreRaising hO hD hF a)

def nativeVAngularPartMass
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (x : R3) : ℝ :=
  2*|nativeFirstDegreeCoefficient g1 g2 L lam δ R p j x|+
    (∑ a : Fin 3, 2*|physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x|)

lemma hasCoreScalarExpansionBound_nativeVAngularPart
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (j : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (nativeVAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j) x
      (nativeVAngularPartMass g1 g2 L lam δ R p j x) := by
  unfold nativeVAngularPart nativeVAngularPartMass
  apply hasCoreScalarExpansionBound_sub hO hD
  · apply hasCoreScalarExpansionBound_neg hO hD
    have ht := hasCoreScalarExpansionBound_smul hO hD (coreAngularGenerator hO hD hF) _ x _ 2
      (hasCoreScalarExpansionBound_single hO hD (coreAngularGenerator hO hD hF)
        (Sum.inr (Sum.inr (Sum.inr true)))
        (nativeFirstDegreeCoefficient g1 g2 L lam δ R p j)
        (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j) x)
    have he (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) :
        ((2 : ℝ) • A)*B = (2 : ℝ) • (A*B) := by rfl
    simpa only [coreAngularGenerator,he,abs_of_pos (by norm_num : 0 < (2 : ℝ))] using ht
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
        (fun i k => NormalizedPrincipalMetricSmooth.contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a j)
    convert ht using 1 <;> ring

lemma commutator_nativeV_eq_angularPart
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3)
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (hA : ScalarCentral hO hD A) :
    ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) A =
      ActualModelCommutatorWords.commutator (nativeVAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j) A := by
  rw [nativeV_eq_full_angular_coefficients]
  have hs := hA (nativeFirstScalarCoefficient g1 g2 L lam δ R p j)
    (contDiff_nativeFirstScalarCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j)
  have ha := hA
    (fun x => adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j)
    (contDiff_modelAdjointFirstCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j)
  have hs2 := hs.smul_right (2 : ℝ)
  have halg {S : Type} [Ring S] (a b c d e : S) (hb : a*b=b*a) (hc : a*c=c*a) :
      (b-c-d-e)*a-a*(b-c-d-e)=(-d-e)*a-a*(-d-e) := by
    simp only [sub_mul,mul_sub,neg_mul,mul_neg]
    rw [← hb,← hc]
    abel
  unfold nativeVAngularPart ActualModelCommutatorWords.commutator
  exact halg A _ _ _ _ ha.eq hs2.eq

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
