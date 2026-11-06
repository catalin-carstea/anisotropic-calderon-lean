import Calderon.ActualNormalizedSecondModelCoefficients

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondModelDefectCoefficients
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  BoundedAngularShift AmbientAngularShift ActualNormalizedSecondModelErrorAssembly
  ActualNormalizedSecondModelDefectNormalForm ActualNormalizedSecondModelCoefficients
  ActualReferenceOrdinaryPrincipal ActualReferenceDDNativeAdjunction ActualReferenceDDNormalizedCoefficient ActualReferenceDDHigherSpectralGraphs
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
  ActualNormalizedSecondDriftAngularAllocation ActualNormalizedSecondDriftNativeAdjunction
  ActualRawMixedPrincipalCollection NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  PrincipalCommutator ActualScalarPrincipalAdjoint ActualPerturbedDefect ReferenceDensityBounds
  NaturalAngularAdjoint ScalarBaseAdjoint

/-- Genuine order-one normalization of the first-base coefficient V in Udag-U.
The raising/lowering sum uses actual native outputs; it is not the Hilbert
adjoint of the whole B W1-inverse normalization. -/
def modelDefectFirstNormalizedCoefficient
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j •
      inverseDegreeMultiplier hO hD -
    referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) j x -
    ContinuousLinearMap.adjoint (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) j x) -
    (∑ a : Fin 3, physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x •
        (normalizedDerivative hF hO hD a + normalizedRaising hF hO hD a)) -
    (2 : ℝ) • normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x

def modelDefectFirstBaseField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ j : Fin 3, modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x
    (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x)

/-- Whole native zero-base defect action W. All density derivatives, actual
mixed covector corrections and reversed angular zero-base adjoints are retained. -/
def modelDefectZeroBaseField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  adjointZeroCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x •
      ambientSphereL2 G hG x -
    (referenceDensityFamily g1 L (lam,x))⁻¹ • ∑ j : Fin 3,
      weightedAngularAdjointDerivative (coordinateDirection j) (fun y => referenceDensityFamily g1 L (lam,y))
        (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
          (referenceNormalizedPrincipalDifference g1 g2 L lam) j) x
        (ambientBesselField hO hD 1 (by norm_num) G hG x) +
    (referenceWeightedZeroBaseAdjoint hO hD g1 hg1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x -
      referenceWeightedZeroBaseTrace hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x) +
    (∑ a : Fin 3, physicalMixedDensityCorrection g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a x • ambientDerivativeField hF hO hD a G hG x) +
    physicalMixedProfileDefect hF hO hD g1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
    physicalMixedConnectionDefect hF hO hD g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
    physicalPureAngularDefect hF hO hD g1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
    (-2 : ℝ) • normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p G hG x -
    normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p x • ambientSphereL2 G hG x

/-- Native DD adjunction expanded on W1. The genuine bounded normalized DD
coefficient is the only object to which the bounded angular adjoint lemma applies. -/
lemma referenceWeightedFirstBaseDefect_normalized_coefficient_form
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (h : MatrixField) (hh : ContDiff ℝ ∞ h)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceWeightedFirstBaseAdjoint hO hD g hg L lam δ R p h G hG x -
      referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x =
    (∑ j : Fin 3, (-ContinuousLinearMap.adjoint
        (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x) -
      referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x)
      (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x)) -
    (referenceDensityFamily g L (lam,x))⁻¹ • ∑ j : Fin 3,
      weightedAngularAdjointDerivative (coordinateDirection j) (fun y => referenceDensityFamily g L (lam,y))
        (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j) x
        (ambientBesselField hO hD 1 (by norm_num) G hG x) := by
  have hm : ContDiff ℝ ∞ (fun y : R3 => referenceDensityFamily g L (lam,y)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hK (j : Fin 3) := contDiff_referenceWeightedFirstBaseNormalizedCoefficient
    hO hD g hg L lam δ R p hδ hR h hh j
  have hp : referenceDensityFamily g L (lam,x) ≠ 0 := (referenceDensityFamily_pos g hg L (lam,x)).ne'
  rw [referenceWeightedFirstBaseAdjoint,
    angularFirstBaseAdjoint_coefficient_form coordinateDirection _ _ _ hm hK
      (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG) x hp,
    referenceWeightedFirstBaseTrace_eq_normalizedCoefficient]
  simp only [angularAdjoint,ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,
    Finset.sum_sub_distrib,Finset.sum_neg_distrib,Finset.smul_sum]
  module

/-- Actual mixed first defect in its order-one normalization, retaining the
whole actual weighted covector divergence in the native zero-base term. -/
lemma physicalMixedFirstDefect_normalized_coefficient_form
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    physicalMixedFirstDefect hF hO hD g L lam h G hG x =
      (∑ j : Fin 3, (-(∑ a : Fin 3, physicalMixedFirstCoefficient g L lam h a j x •
        (normalizedDerivative hF hO hD a + normalizedRaising hF hO hD a)))
        (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x)) +
      ∑ a : Fin 3, physicalMixedDensityCorrection g L lam h a x • ambientDerivativeField hF hO hD a G hG x := by
  have hDerivative (a j : Fin 3) :
      directionalFDeriv (coordinateDirection j) (AmbientAngularShift.ambientDerivativeField hF hO hD a G hG) x =
      normalizedDerivative hF hO hD a
        (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x) := by
    change directionalFDeriv (coordinateDirection j)
      (fun y => normalizedDerivative hF hO hD a (ambientBesselField hO hD 1 (by norm_num) G hG y)) x = _
    exact OAI.AnisotropicCalderon.ActualReferenceDecomposition.directionalFDeriv_fixed_map _ _
      (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG) _ _
  have hRaising (a j : Fin 3) :
      directionalFDeriv (coordinateDirection j) (AmbientAngularShift.ambientRaisingField hF hO hD a G hG) x =
      normalizedRaising hF hO hD a
        (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x) := by
    change directionalFDeriv (coordinateDirection j)
      (fun y => normalizedRaising hF hO hD a (ambientBesselField hO hD 1 (by norm_num) G hG y)) x = _
    exact OAI.AnisotropicCalderon.ActualReferenceDecomposition.directionalFDeriv_fixed_map _ _
      (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG) _ _
  rw [physicalMixedFirstDefect_coefficient_form hF hO hD g L lam h hg hh G hG x]
  simp_rw [hDerivative,hRaising]
  simp only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply,neg_smul,smul_add,Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp only [← neg_add, ← Finset.sum_neg_distrib]

/-- The actual scalar first defect coefficient acts after the native inverse
degree weight, with precisely the same W1 derivative as all other first terms. -/
lemma scalarFirstDefect_eq_normalized
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (∑ j : Fin 3, adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j •
      directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x) =
    ∑ j : Fin 3, (adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j •
      inverseDegreeMultiplier hO hD)
      (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x) := by
  simp only [ContinuousLinearMap.smul_apply,
    inverseDegreeMultiplier_directional_ambientBesselField_one]

/-- Full native pointwise coefficient extraction of Udag-U. This does not
instantiate the generic operator Ring on a full invariant raw domain. -/
theorem normalizedSecondModelErrorDefect_full_coefficient_form
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    normalizedSecondModelErrorDefect hF hO hD g1 g2 hg1 L lam δ R p G hG x =
      modelDefectFirstBaseField hF hO hD g1 g2 hg1 L lam δ R p G hG x +
      modelDefectZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p G hG x := by
  have hh := contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have he (i j : Fin 3) := contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i j
  rw [normalizedSecondModelErrorDefect_normal_form hF hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR G hG x,
    referenceWeightedFirstBaseDefect_normalized_coefficient_form hO hD g1 hg1 L lam δ R p hδ hR _ hh G hG x,
    physicalMixedFirstDefect_normalized_coefficient_form hF hO hD g1 hg1 L lam _ he G hG x,
    scalarFirstDefect_eq_normalized hO hD g1 g2 L lam δ R p G hG x,
    normalizedSecondDriftFirstBaseField_eq_normalized hO hD g1 g2 hg1 L lam δ R p G hG x]
  simp only [modelDefectFirstBaseField,modelDefectFirstNormalizedCoefficient,modelDefectZeroBaseField,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,ContinuousLinearMap.smul_apply,
    Finset.sum_sub_distrib,Finset.sum_neg_distrib,Finset.smul_sum,neg_smul]
  module

/-- The actual native formal-adjoint field has the same second-base scalar
principal and the explicitly corrected first and zero actions. -/
theorem normalizedSecondModelErrorAdjoint_full_coefficient_form
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    normalizedSecondModelErrorAdjoint hF hO hD g1 g2 hg1 L lam δ R p G hG x =
      scalarSecondBase coordinateDirection
        (fun y => ConformalDepth.referenceRadius δ R p L y • referenceNormalizedPrincipalMatrix g1 g2 L lam y)
        (ambientSphereL2 G hG) x +
      (∑ j : Fin 3, (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x +
        modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x)
        (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x)) +
      (modelZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p G hG x +
        modelDefectZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p G hG x) := by
  have he := normalizedSecondModelErrorDefect_full_coefficient_form
    hF hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR G hG x
  unfold normalizedSecondModelErrorDefect at he
  have ha : normalizedSecondModelErrorAdjoint hF hO hD g1 g2 hg1 L lam δ R p G hG x =
      normalizedSecondModelError hF hO hD g1 g2 hg1 L lam δ R p G hG x +
        (modelDefectFirstBaseField hF hO hD g1 g2 hg1 L lam δ R p G hG x +
          modelDefectZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p G hG x) :=
    (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  rw [ha,normalizedSecondModelError_full_coefficient_form hF hO hD g1 g2 hg1 L lam δ R p hδ hR G hG x]
  simp only [modelFirstBaseField,modelDefectFirstBaseField,ContinuousLinearMap.add_apply,Finset.sum_add_distrib]
  abel

/-- Genuine compact-domain weak adjunction with the explicit actual adjoint
coefficient action. No unbounded angular coefficient is made an L2 map. -/
theorem compact_normalizedSecondModelError_adjoint_coefficient_form
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K : Set R3) (hK : IsCompact K)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ K, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪normalizedSecondModelError hF hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 H hH x⟫_ℝ) =
    ∫ x, referenceDensityFamily g1 L (lam,x) * ⟪ambientSphereL2 G hG x,
      scalarSecondBase coordinateDirection
        (fun y => ConformalDepth.referenceRadius δ R p L y • referenceNormalizedPrincipalMatrix g1 g2 L lam y)
        (ambientSphereL2 H hH) x +
      (∑ j : Fin 3, (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x +
        modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x)
        (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) H hH) x)) +
      (modelZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p H hH x +
        modelDefectZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p H hH x)⟫_ℝ := by
  rw [compact_normalizedSecondModelError_adjoint hF hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR G H hG hH K hK hzG hzH]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [normalizedSecondModelErrorAdjoint_full_coefficient_form hF hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR H hH x])

end OAI.AnisotropicCalderon.ActualNormalizedSecondModelDefectCoefficients
