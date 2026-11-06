import Calderon.ActualFiniteHarmonicModelBLinearExpansion

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  ActualPhysicalMixedFirst NormalizedPrincipalMetric ActualModelCommutatorWords
  NormalizedPrincipalMetricSmooth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def nativeBAngularPart
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR -
    coreScalar hO hD (nativeFirstScalarCoefficient g1 g2 L lam δ R p j)
      (contDiff_nativeFirstScalarCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j)

def nativeBAngularPartMass
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (x : R3) : ℝ :=
  |nativeFirstDegreeCoefficient g1 g2 L lam δ R p j x|+
    (∑ c : Fin 3, |nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c x| *
      nativeReferenceConnectionCoefficientMass g1 L lam c x)+
    (∑ a : Fin 3, |physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x|)

lemma nativeBAngularPart_eq_coefficients
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    nativeBAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j =
    coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p j)
      (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j) * coreDegree hO hD +
    (∑ c : Fin 3, coreScalar hO hD (nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c)
      (contDiff_nativeFirstConnectionCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j c) *
      nativeReferenceConnectionAction hO hD g1 hg1 L lam c) +
    ∑ a : Fin 3, coreScalar hO hD
        (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j)
        (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
          (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a j) * coreRaising hO hD hF a := by
  unfold nativeBAngularPart
  rw [nativeB_eq_full_angular_coefficients hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j]
  abel

lemma hasCoreScalarExpansionBound_nativeBAngularPart
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (j : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (nativeBAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j) x
      (nativeBAngularPartMass g1 g2 L lam δ R p j x) := by
  rw [nativeBAngularPart_eq_coefficients hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j]
  unfold nativeBAngularPartMass
  apply hasCoreScalarExpansionBound_add hO hD
  · apply hasCoreScalarExpansionBound_add hO hD
    · exact hasCoreScalarExpansionBound_single hO hD (coreAngularGenerator hO hD hF)
        (Sum.inr (Sum.inr (Sum.inr true))) _ _ x
    · apply hasCoreScalarExpansionBound_sum hO hD
      intro c _
      exact hasCoreScalarExpansionBound_scalar_mul hO hD (coreAngularGenerator hO hD hF) _ x _
        (hasCoreScalarExpansionBound_nativeReferenceConnectionAction hO hD hF g1 hg1 L lam c x) _ _
  · apply hasCoreScalarExpansionBound_sum hO hD
    intro a _
    exact hasCoreScalarExpansionBound_single hO hD (coreAngularGenerator hO hD hF)
      (Sum.inr (Sum.inl a)) _ _ x

lemma commutator_nativeB_eq_angularPart
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3)
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (hA : ScalarCentral hO hD A) :
    commutator A (nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) =
      commutator A (nativeBAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j) := by
  have hs := (hA (nativeFirstScalarCoefficient g1 g2 L lam δ R p j)
    (contDiff_nativeFirstScalarCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j)).eq
  unfold nativeBAngularPart ActualModelCommutatorWords.commutator
  have halg {R : Type} [Ring R] (a b c : R) (h : a*c=c*a) :
      a*b-b*a = a*(b-c)-(b-c)*a := by
    rw [mul_sub,sub_mul,h]
    abel
  exact halg A (nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR)
    (coreScalar hO hD (nativeFirstScalarCoefficient g1 g2 L lam δ R p j)
      (contDiff_nativeFirstScalarCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j)) hs

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
