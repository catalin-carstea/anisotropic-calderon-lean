import Calderon.ActualNormalizedSecondModelDefectNormalForm

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondModelCoefficients
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  BoundedAngularShift AmbientAngularShift ActualNormalizedSecondModelErrorAssembly
  ActualReferenceOrdinaryPrincipal ActualReferenceDDNormalizedCoefficient
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection
  ActualPhysicalMixedNative ActualPhysicalPureAngular ActualNormalizedSecondDriftAngularAllocation
  ActualRawMixedPrincipalCollection NormalizedPrincipalMetric PrincipalCommutator
  ActualScalarPrincipalAdjoint ActualPerturbedDefect ReferenceDensityBounds

/-- Order-one normalization of the literal full E/F-free model first coefficient.
The raw first coefficient is this map after W1, not a bounded raw L2 map. -/
def modelFirstNormalizedCoefficient
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) j x +
    (∑ a : Fin 3, physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x •
        normalizedRaising hF hO hD a) +
    normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x

def modelFirstBaseField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ j : Fin 3, modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x
    (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x)

/-- Native zero-base action retaining all DD, covector connection, profile,
pure angular and actual second-metric drift components. -/
def modelZeroBaseField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  referenceWeightedZeroBaseTrace hO hD g1 hg1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
    physicalMixedProfileRaising hF hO hD g1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
    physicalMixedConnectionRaising hF hO hD g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
    physicalPureAngularRaising hF hO hD g1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
    normalizedSecondDriftZeroBaseField hO hD g1 g2 hg1 L lam δ R p G hG x

lemma physicalMixedFirstRaising_eq_normalized
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    physicalMixedFirstRaising hF hO hD g L lam h G hG x =
      ∑ j : Fin 3, (∑ a : Fin 3, physicalMixedFirstCoefficient g L lam h a j x •
        normalizedRaising hF hO hD a)
        (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x) := by
  have hraise (a j : Fin 3) :
      directionalFDeriv (coordinateDirection j) (ambientRaisingField hF hO hD a G hG) x =
        normalizedRaising hF hO hD a
          (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x) := by
    change directionalFDeriv (coordinateDirection j)
      (fun y => normalizedRaising hF hO hD a (ambientBesselField hO hD 1 (by norm_num) G hG y)) x = _
    have hd := directionalFDeriv_clm_apply (coordinateDirection j)
      (fun _ : R3 => normalizedRaising hF hO hD a)
      (ambientBesselField hO hD 1 (by norm_num) G hG) contDiff_const
      (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG) x
    simpa only [AmbientAngularShift.ambientRaisingField,directionalFDeriv,fderiv_const_apply,
      ContinuousLinearMap.zero_apply,zero_add] using hd
  unfold physicalMixedFirstRaising frameRaisingFirst
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply]
  simp_rw [hraise]
  rw [Finset.sum_comm]

lemma normalizedSecondDriftFirstBaseField_eq_normalized
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x =
      ∑ j : Fin 3, normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
        (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x) := by
  unfold normalizedSecondDriftFirstBaseField normalizedSecondDriftFirstNormalizedCoefficient
  simp only [ContinuousLinearMap.smul_apply,Finset.smul_sum,
    inverseDegreeMultiplier_directional_ambientBesselField_one,smul_smul]

lemma modelFirstBaseField_eq_components
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    modelFirstBaseField hF hO hD g1 g2 hg1 L lam δ R p G hG x =
      referenceWeightedFirstBaseTrace hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      physicalMixedFirstRaising hF hO hD g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x := by
  rw [referenceWeightedFirstBaseTrace_eq_normalizedCoefficient,
    physicalMixedFirstRaising_eq_normalized,
    normalizedSecondDriftFirstBaseField_eq_normalized]
  unfold modelFirstBaseField modelFirstNormalizedCoefficient
  simp only [ContinuousLinearMap.add_apply,Finset.sum_add_distrib]

theorem normalizedSecondModelError_full_coefficient_form
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    normalizedSecondModelError hF hO hD g1 g2 hg1 L lam δ R p G hG x =
      ScalarBaseAdjoint.scalarSecondBase coordinateDirection
        (fun y => ConformalDepth.referenceRadius δ R p L y • referenceNormalizedPrincipalMatrix g1 g2 L lam y)
        (ambientSphereL2 G hG) x +
      modelFirstBaseField hF hO hD g1 g2 hg1 L lam δ R p G hG x +
      modelZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p G hG x := by
  rw [normalizedSecondModelError_ordinary_decomposition hF hO hD g1 g2 hg1 L lam δ R p hδ hR,
    physicalMixedNativeRaising_decomposition,
    normalizedSecondWeightedDriftField_ordinary_split,
    modelFirstBaseField_eq_components]
  unfold modelZeroBaseField
  abel

end OAI.AnisotropicCalderon.ActualNormalizedSecondModelCoefficients
