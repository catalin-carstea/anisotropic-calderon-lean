import Calderon.ActualFiniteHarmonicModelSecondAngularNormalization
import Calderon.ActualFiniteHarmonicModelConnectionSymmetric
import Calderon.ActualFiniteHarmonicAmbient

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient SpectralWeightedGraph BoundedAngularShift
  ActualNormalizedSphereRotation ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
  AngularDerivativeBesselField AmbientAngularShift AmbientReferenceRaising SmoothSphereFields SmoothAngularApplication
  SmoothAmbientAngularCasimir ActualReferenceParallelRaising ActualReferenceDDSpectralTransport
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeWAdjointBasisFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWAdjointBasisFunction
lemma nativeW_profile_basis_inner_adjoint
    (hF : SphereFischerInner) (a : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪normalizedDerivative hF hO hD a (coreWeightOperator hO hD (besselWeight 2) F x - (2 : ℝ) • coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      ⟪F x,normalizedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight 2) G x - coreWeightOperator hO hD (besselWeight 1) G x)⟫_ℝ := by
  have hW (A : smoothCompactFiniteSphereCore hO hD) (s : ℝ) (hs : s ≤ 2) :
      ambientBesselField hO hD s hs (coreAmbientFunction hO hD A) (contDiff_coreAmbientFunction hO hD A) x =
        coreWeightOperator hO hD (besselWeight s) A x :=
    (coreWeightOperator_eq_ambientBesselField hO hD A (coreAmbientRepresentative hO hD A) s hs x).symm
  have ht := ambientMixedRaisingDegreeField_inner_adjoint hF hO hD a
    (coreAmbientFunction hO hD G) (coreAmbientFunction hO hD F)
    (contDiff_coreAmbientFunction hO hD G) (contDiff_coreAmbientFunction hO hD F) x
  unfold ambientMixedRaisingDegreeField ambientMixedDegreeBesselField ambientMixedDegreeDerivativeField at ht
  simp only [hW F 2 (by norm_num),hW F 1 (by norm_num),hW G 2 (by norm_num),hW G 1 (by norm_num),
    ambientSphereL2_coreAmbientFunction hO hD] at ht
  simpa only [real_inner_comm] using ht.symm


lemma nativeW_connection_basis_inner_adjoint
    (hF : SphereFischerInner) (a b c : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪normalizedRotation hO hD b c (normalizedDerivative hF hO hD a (coreWeightOperator hO hD (besselWeight 2) F x - coreWeightOperator hO hD (besselWeight 1) F x)),G x⟫_ℝ =
      -⟪F x,normalizedRaising hF hO hD a (normalizedRotation hO hD b c (coreWeightOperator hO hD (besselWeight 2) G x))⟫_ℝ := by
  have hW (A : smoothCompactFiniteSphereCore hO hD) (s : ℝ) (hs : s ≤ 2) :
      ambientBesselField hO hD s hs (coreAmbientFunction hO hD A) (contDiff_coreAmbientFunction hO hD A) x =
        coreWeightOperator hO hD (besselWeight s) A x :=
    (coreWeightOperator_eq_ambientBesselField hO hD A (coreAmbientRepresentative hO hD A) s hs x).symm
  let GA := coreAmbientFunction hO hD G
  have hGA : ContDiff ℝ ∞ GA := contDiff_coreAmbientFunction hO hD G
  have hrot : ambientSphereL2 (ambientAngularRotation b c GA)
      (contDiff_ambientAngularRotation b c GA hGA) x = coreRotation hO hD b c G x :=
    (coreRotation_eq_ambientAngularRotation hO hD b c G (coreAmbientRepresentative hO hD G) x).symm
  have hrotWeight : ambientBesselField hO hD 1 (by norm_num) (ambientAngularRotation b c GA)
      (contDiff_ambientAngularRotation b c GA hGA) x =
        coreWeightOperator hO hD (besselWeight 1) (coreRotation hO hD b c G) x := by
    apply spectralGraph_output_unique hO hD (besselWeight 1) (coreRotation hO hD b c G x)
    · simpa only [sphereBesselGraph,hrot] using
        ambientBesselField_graph hO hD 1 (by norm_num) (ambientAngularRotation b c GA)
          (contDiff_ambientAngularRotation b c GA hGA) x
    · exact coreWeightOperator_graph hO hD (besselWeight 1) (coreRotation hO hD b c G) x
  have hUV : (coreWeightOperator hO hD (besselWeight 1) G x,
      coreWeightOperator hO hD (besselWeight 2) G x) ∈ sphereBesselGraph hO hD 1 := by
    rw [← coreWeight_one_twice_apply hO hD G x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) G) x
  have hRotW : coreWeightOperator hO hD (besselWeight 1) (coreRotation hO hD b c G) x =
      normalizedRotation hO hD b c (coreWeightOperator hO hD (besselWeight 2) G x) := by
    have ha := preservesSphereSpectralGraphs_normalizedRotation hO hD b c (besselWeight 1)
      (coreWeightOperator hO hD (besselWeight 1) G x)
      (coreWeightOperator hO hD (besselWeight 2) G x) hUV
    have hg := coreWeightOperator_graph hO hD (besselWeight 1) (coreRotation hO hD b c G) x
    rw [coreRotation_apply_eq_normalizedRotation hO hD b c G x] at hg
    exact spectralGraph_output_unique hO hD (besselWeight 1)
      (normalizedRotation hO hD b c (coreWeightOperator hO hD (besselWeight 1) G x)) _ _ hg ha
  have ht := ambientMixedRaisingRotationField_inner_adjoint hF hO hD a b c GA
    (coreAmbientFunction hO hD F) hGA (contDiff_coreAmbientFunction hO hD F) x
  unfold ambientMixedRaisingRotationField ambientMixedRotatedDerivativeField ambientRaisingField AngularDerivativeBesselField.ambientDerivativeBesselField at ht
  rw [hrotWeight,hRotW] at ht
  simp only [hW F 2 (by norm_num),hW F 1 (by norm_num),GA,ambientSphereL2_coreAmbientFunction hO hD] at ht
  have he := congrArg Neg.neg ht
  simpa only [neg_neg,real_inner_comm] using he.symm


lemma nativeW_pure_basis_inner_adjoint
    (hF : SphereFischerInner) (a b : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪normalizedDerivative hF hO hD b (normalizedDerivative hF hO hD a (coreWeightOperator hO hD (besselWeight 2) F x - coreWeightOperator hO hD (besselWeight 1) F x)),G x⟫_ℝ =
      ⟪F x,normalizedRaising hF hO hD a (normalizedRaising hF hO hD b (coreWeightOperator hO hD (besselWeight 2) G x + coreWeightOperator hO hD (besselWeight 1) G x))⟫_ℝ := by
  have hW (A : smoothCompactFiniteSphereCore hO hD) (s : ℝ) (hs : s ≤ 2) :
      ambientBesselField hO hD s hs (coreAmbientFunction hO hD A) (contDiff_coreAmbientFunction hO hD A) x =
        coreWeightOperator hO hD (besselWeight s) A x :=
    (coreWeightOperator_eq_ambientBesselField hO hD A (coreAmbientRepresentative hO hD A) s hs x).symm
  have ht := ambientDoubleRaisingField_inner_adjoint hF hO hD a b
    (coreAmbientFunction hO hD G) (coreAmbientFunction hO hD F)
    (contDiff_coreAmbientFunction hO hD G) (contDiff_coreAmbientFunction hO hD F) x
  unfold ambientDoubleRaisingField ambientDoubleDerivativeField ambientRaisingBesselField AngularDerivativeBesselField.ambientDerivativeBesselField at ht
  simp only [hW F 2 (by norm_num),hW F 1 (by norm_num),hW G 2 (by norm_num),hW G 1 (by norm_num),
    ambientSphereL2_coreAmbientFunction hO hD] at ht
  simpa only [real_inner_comm] using ht.symm


lemma nativeW_angular_connection_weight_inner_skew
    (g : MatrixField) (L lam : ℝ) (y X : R3)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪normalizedReferenceAngularConnection hO hD g L lam y X (coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      -⟪F x,normalizedReferenceAngularConnection hO hD g L lam y X (coreWeightOperator hO hD (besselWeight 1) G x)⟫_ℝ := by
  exact ActualNormalizedSecondDriftNativeAdjunction.normalizedReferenceAngularConnection_bessel_inner_skew hO hD g L lam y X
    (F x) (coreWeightOperator hO hD (besselWeight 1) F x)
    (G x) (coreWeightOperator hO hD (besselWeight 1) G x)
    (coreWeightOperator_graph hO hD (besselWeight 1) F x)
    (coreWeightOperator_graph hO hD (besselWeight 1) G x)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
