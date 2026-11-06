import Calderon.ActualFiniteHarmonicModelReferenceConnectionExpansion
import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  ActualPhysicalMixedFirst NormalizedPrincipalMetric ActualScalarPrincipalAdjoint NaturalAngularAdjoint
  ReferenceDensityBounds PrincipalCommutator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def nativeVLinearExpansionMass
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (x : R3) : ℝ :=
  |adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j|+
    2*|nativeFirstScalarCoefficient g1 g2 L lam δ R p j x|+
    2*|nativeFirstDegreeCoefficient g1 g2 L lam δ R p j x|+
    (∑ a : Fin 3, 2*|physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x|)

lemma hasCoreScalarExpansionBound_nativeV
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (j : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) x
      (nativeVLinearExpansionMass g1 g2 L lam δ R p j x) := by
  rw [nativeV_eq_full_angular_coefficients hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j]
  unfold nativeVLinearExpansionMass
  apply hasCoreScalarExpansionBound_sub hO hD
  · apply hasCoreScalarExpansionBound_sub hO hD
    · apply hasCoreScalarExpansionBound_sub hO hD
      · exact hasCoreScalarExpansionBound_coreScalar hO hD hF _ _ x
      · simpa only [abs_of_pos (by norm_num : 0 < (2 : ℝ))] using
          hasCoreScalarExpansionBound_smul hO hD (coreAngularGenerator hO hD hF) _ x _ 2
            (hasCoreScalarExpansionBound_coreScalar hO hD hF _ _ x)
    · have ht := hasCoreScalarExpansionBound_smul hO hD (coreAngularGenerator hO hD hF) _ x _ 2
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

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
