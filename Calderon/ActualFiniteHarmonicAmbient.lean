import Calderon.ActualFiniteHarmonicCore
import Calderon.ActualNormalizedSecondModelCoefficients
import Calderon.SmoothMovingFrameFields
import Calderon.SmoothAngularCasimir

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter MvPolynomial
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicAmbient
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  ActualFiniteHarmonicCore FischerConnectionTransport SmoothAngularCasimir GreenRadialTrace
  SmoothSphereFields SmoothAngularApplication AmbientAngularShift AngularShiftGraph
  ActualPhysicalPureAngular AngularDerivativeBesselField SmoothMovingFrameFields
  SmoothAmbientAngularCasimir AmbientReferenceRaising SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondModelCoefficients ActualNormalizedSecondModelErrorAssembly
  NormalizedPrincipalMetric ReferenceDensityBounds

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev finiteHarmonicAmbientFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] finiteHarmonicAmbientFunction

lemma sphereHarmonicPartialSum_eq_of_finiteBand (n : ℕ) (F : R3 → SphereL2)
    (hF : finiteHarmonicBand hO hD n F) (x : R3) :
    sphereHarmonicPartialSum hO hD n (F x) = F x := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k (sphereHarmonicPartialSum hO hD n (F x)) =
    sphereHarmonicCoordinate hO hD k (F x)
  rw [sphereHarmonicCoordinate_partialSum]
  by_cases hk : k < n
  · rw [if_pos hk]
  · rw [if_neg hk, hF x k (Nat.le_of_not_gt hk)]

structure FiniteHarmonicAmbientRepresentative (F : smoothCompactFiniteSphereCore hO hD) where
  cutoff : ℕ
  dimension : Fin cutoff → ℕ
  polynomial : ∀ k : Fin cutoff, Fin (dimension k) → MvPolynomial (Fin 3) ℝ
  coefficient : ∀ k : Fin cutoff, R3 → Fin (dimension k) → ℝ
  polynomial_mem : ∀ (k : Fin cutoff) (j : Fin (dimension k)),
    polynomial k j ∈ harmonicHomogeneous (k:ℕ)
  coefficient_contDiff : ∀ k, ContDiff ℝ ∞ (coefficient k)
  coefficient_zero : ∀ k x, x ∉ tsupport (F : R3 → SphereL2) → coefficient k x = 0
  represents : ∀ x, polynomialSphereL2
    (∑ k : Fin cutoff, finitePolynomialField (polynomial k) (coefficient k) x) = F x

def representativePolynomial {F : smoothCompactFiniteSphereCore hO hD}
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) : MvPolynomial (Fin 3) ℝ :=
  ∑ k : Fin r.cutoff, finitePolynomialField (r.polynomial k) (r.coefficient k) x

def representativeAmbient {F : smoothCompactFiniteSphereCore hO hD}
    (r : FiniteHarmonicAmbientRepresentative hO hD F) : R3 × R3 → ℝ :=
  fun z => polynomialEvaluation (representativePolynomial hO hD r z.1) z.2

lemma contDiff_representativeAmbient {F : smoothCompactFiniteSphereCore hO hD}
    (r : FiniteHarmonicAmbientRepresentative hO hD F) :
    ContDiff ℝ ∞ (representativeAmbient hO hD r) := by
  have heq : representativeAmbient hO hD r =
      fun z => ∑ k : Fin r.cutoff, ∑ j : Fin (r.dimension k),
        r.coefficient k z.1 j * polynomialEvaluation (r.polynomial k j) z.2 := by
    funext z
    simp [representativeAmbient, representativePolynomial, finitePolynomialField,
      polynomialEvaluation, smul_eq_C_mul]
  rw [heq]
  exact ContDiff.sum fun k _ => ContDiff.sum fun j _ =>
    ((contDiff_pi.mp (r.coefficient_contDiff k) j).comp contDiff_fst).mul
      ((contDiff_polynomialEvaluation (r.polynomial k j)).comp contDiff_snd)

lemma representativeAmbient_zero_outside {F : smoothCompactFiniteSphereCore hO hD}
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x ξ : R3)
    (hx : x ∉ tsupport (F : R3 → SphereL2)) :
    representativeAmbient hO hD r (x,ξ) = 0 := by
  have hcz (k : Fin r.cutoff) : r.coefficient k x = 0 := r.coefficient_zero k x hx
  have hp : representativePolynomial hO hD r x = 0 := by
    simp [representativePolynomial, finitePolynomialField, hcz]
  change polynomialEvaluation (representativePolynomial hO hD r x) ξ = 0
  rw [hp]
  simp [polynomialEvaluation]

lemma ambientSphereL2_representative {F : smoothCompactFiniteSphereCore hO hD}
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    ambientSphereL2 (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
      F x := by
  calc
    _ = polynomialSphereL2 (representativePolynomial hO hD r x) := by
      change (ContinuousMap.toLp 2 sphereProbability ℝ)
          (ambientSphereSection (representativeAmbient hO hD r)
            (contDiff_representativeAmbient hO hD r) x) =
        (ContinuousMap.toLp 2 sphereProbability ℝ) (polynomialSphere (representativePolynomial hO hD r x))
      congr 1 <;> rfl
    _ = F x := r.represents x

lemma exists_finiteHarmonicAmbientRepresentative (F : smoothCompactFiniteSphereCore hO hD) :
    Nonempty (FiniteHarmonicAmbientRepresentative hO hD F) := by
  classical
  let N := F.property.2.2.choose
  let K := tsupport (F : R3 → SphereL2)
  have hK : IsCompact K := F.property.2.1
  have hz : ∀ x ∉ K, F x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hex (k : Fin N) := exists_smooth_compact_coordinates_sphereHarmonicCoordinate
    hO hD (k:ℕ) (F : R3 → SphereL2) F.property.1 K hK hz
  choose m b c hb hc hcompact hrep hcz using hex
  refine ⟨{
    cutoff := N
    dimension := m
    polynomial := b
    coefficient := c
    polynomial_mem := hb
    coefficient_contDiff := hc
    coefficient_zero := fun k x hx => hcz k x hx
    represents := ?_ }⟩
  intro x
  calc
    _ = ∑ k : Fin N, (sphereHarmonicCoordinate hO hD (k:ℕ) (F x) : SphereL2) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun k _ => hrep k x)
    _ = sphereHarmonicPartialSum hO hD N (F x) := by
      rw [sphereHarmonicPartialSum_apply]
      simp only [sphereHarmonicCoordinate_apply]
      exact Fin.sum_univ_eq_sum_range
        (fun k => (sphereHarmonicDecomposition hO hD (F x) k : SphereL2)) N
    _ = F x := sphereHarmonicPartialSum_eq_of_finiteBand hO hD N
      (F : R3 → SphereL2) F.property.2.2.choose_spec x

lemma coreWeightOperator_eq_ambientBesselField
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F)
    (s : ℝ) (hs : s ≤ 2) (x : R3) :
    coreWeightOperator hO hD (besselWeight s) F x =
      ambientBesselField hO hD s hs (representativeAmbient hO hD r)
        (contDiff_representativeAmbient hO hD r) x := by
  apply spectralGraph_output_unique hO hD (besselWeight s) (F x)
  · exact coreWeightOperator_graph hO hD (besselWeight s) F x
  · simpa only [SpectralWeightedGraph.sphereBesselGraph,
      ambientSphereL2_representative hO hD r x] using
      ambientBesselField_graph hO hD s hs (representativeAmbient hO hD r)
        (contDiff_representativeAmbient hO hD r) x

lemma coreDerivative_eq_ambientDerivativeField (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F)
    (x : R3) :
    coreDerivative hO hD hF i F x = ambientDerivativeField hF hO hD i
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x := by
  apply sphereDerivativeGraph_output_unique hF hO hD i (F x)
  · exact coreDerivative_graph hO hD hF i F x
  · simpa only [ambientSphereL2_representative hO hD r x] using
      ambientDerivativeField_graph hF hO hD i (representativeAmbient hO hD r)
        (contDiff_representativeAmbient hO hD r) x

lemma coreRaising_eq_ambientRaisingField (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F)
    (x : R3) :
    coreRaising hO hD hF i F x = ambientRaisingField hF hO hD i
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x := by
  apply sphereRaisingGraph_output_unique hF hO hD i (F x)
  · exact coreRaising_graph hO hD hF i F x
  · simpa only [ambientSphereL2_representative hO hD r x] using
      ambientRaisingField_graph hF hO hD i (representativeAmbient hO hD r)
        (contDiff_representativeAmbient hO hD r) x

lemma coreWeightDerivative_eq_ambientDerivativeBesselField (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F)
    (x : R3) :
    coreWeightOperator hO hD (besselWeight 1) (coreDerivative hO hD hF i F) x =
      ambientDerivativeBesselField hF hO hD i (representativeAmbient hO hD r)
        (contDiff_representativeAmbient hO hD r) x := by
  apply spectralGraph_output_unique hO hD (besselWeight 1) (coreDerivative hO hD hF i F x)
  · exact coreWeightOperator_graph hO hD (besselWeight 1) (coreDerivative hO hD hF i F) x
  · rw [coreDerivative_eq_ambientDerivativeField hO hD hF i F r x]
    exact ambientDerivativeBesselField_graph hF hO hD i (representativeAmbient hO hD r)
      (contDiff_representativeAmbient hO hD r) x

lemma coreWeightRaising_eq_ambientRaisingBesselField (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F)
    (x : R3) :
    coreWeightOperator hO hD (besselWeight 1) (coreRaising hO hD hF i F) x =
      ambientRaisingBesselField hF hO hD i (representativeAmbient hO hD r)
        (contDiff_representativeAmbient hO hD r) x := by
  apply spectralGraph_output_unique hO hD (besselWeight 1) (coreRaising hO hD hF i F x)
  · exact coreWeightOperator_graph hO hD (besselWeight 1) (coreRaising hO hD hF i F) x
  · rw [coreRaising_eq_ambientRaisingField hO hD hF i F r x]
    exact ambientRaisingBesselField_graph hF hO hD i (representativeAmbient hO hD r)
      (contDiff_representativeAmbient hO hD r) x

lemma coreDegree_eq_ambientDegreeField
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F)
    (x : R3) :
    coreDegree hO hD F x = ambientDegreeField hO hD (representativeAmbient hO hD r)
      (contDiff_representativeAmbient hO hD r) x := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k (coreWeightOperator hO hD (fun l => (l:ℝ)) F x) =
    sphereHarmonicCoordinate hO hD k (ambientDegreeField hO hD (representativeAmbient hO hD r)
      (contDiff_representativeAmbient hO hD r) x)
  rw [(coreWeightOperator_graph hO hD (fun l => (l:ℝ)) F x) k,
    ambientDegreeField_coordinate, ambientSphereL2_representative hO hD r x]

lemma coreRotation_eq_ambientAngularRotation (i j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F)
    (x : R3) :
    coreRotation hO hD i j F x = ambientSphereL2
      (ambientAngularRotation i j (representativeAmbient hO hD r))
      (contDiff_ambientAngularRotation i j _ (contDiff_representativeAmbient hO hD r)) x := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k
      (coreBlockOperator hO hD (fun l => SmoothSphereRotationProjection.harmonicSphereRotation l i j) F x) =
    sphereHarmonicCoordinate hO hD k (ambientSphereL2
      (ambientAngularRotation i j (representativeAmbient hO hD r))
      (contDiff_ambientAngularRotation i j _ (contDiff_representativeAmbient hO hD r)) x)
  rw [coreBlockOperator_coordinate, sphereHarmonicCoordinate_ambientAngularRotation,
    ambientSphereL2_representative hO hD r x]
  exact contDiff_representativeAmbient hO hD r

def coreFrameHorizontalAction (C : R3 → Fin 3 → Fin 3 → ℝ) (X : R3 → R3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  fderiv ℝ (F : R3 → SphereL2) x (X x) + (1/2:ℝ) •
    ∑ i : Fin 3, ∑ j : Fin 3, C x i j • coreRotation hO hD i j F x

lemma ambientFrameHorizontal_representative
    (C : R3 → Fin 3 → Fin 3 → ℝ) (hC : ∀ i j, ContDiff ℝ ∞ (fun x => C x i j))
    (hskew : ∀ x i j, C x i j = -C x j i) (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F)
    (x : R3) :
    ambientSphereL2 (ambientFrameHorizontal C X (representativeAmbient hO hD r))
      (contDiff_ambientFrameHorizontal C hC X hX _ (contDiff_representativeAmbient hO hD r)) x =
      coreFrameHorizontalAction hO hD C X F x := by
  rw [ambientSphereL2_frameHorizontal C hC hskew X hX (representativeAmbient hO hD r)
    (contDiff_representativeAmbient hO hD r) x]
  have heq : ambientSphereL2 (representativeAmbient hO hD r)
      (contDiff_representativeAmbient hO hD r) = (F : R3 → SphereL2) :=
    funext (ambientSphereL2_representative hO hD r)
  rw [heq]
  unfold coreFrameHorizontalAction
  simp_rw [← coreRotation_eq_ambientAngularRotation hO hD _ _ F r x]

lemma referenceHorizontalField_representative (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (a : Fin 3) (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    referenceHorizontalField g hg L lam a (representativeAmbient hO hD r)
      (contDiff_representativeAmbient hO hD r) x =
    coreFrameHorizontalAction hO hD
      (fun y => referenceFrameConnectionCoefficient g L lam y (referenceMetricGramFrame g L (lam,y) a))
      (fun y => referenceMetricGramFrame g L (lam,y) a) F x := by
  have hX := contDiff_referenceMetricGramFrame_slice g hg L lam a
  have hC := fun i j => AmbientReferenceCovariantCore.contDiff_referenceFrameConnectionCoefficient_field g hg L lam _ hX i j
  have hs := fun y i j => referenceFrameConnectionCoefficient_skew g hg L lam y
    (referenceMetricGramFrame g L (lam,y) a) i j
  simpa only [referenceHorizontalField, referenceHorizontalAmbient] using
    ambientFrameHorizontal_representative hO hD
      (fun y => referenceFrameConnectionCoefficient g L lam y (referenceMetricGramFrame g L (lam,y) a))
      hC hs (fun y => referenceMetricGramFrame g L (lam,y) a) hX F r x

lemma referenceWeightedInputField_representative (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam s : ℝ) (a : Fin 3) (f : R3 → ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    referenceWeightedInputField hO hD g hg L lam s a f (representativeAmbient hO hD r)
      (contDiff_representativeAmbient hO hD r) x =
      s • coreFrameHorizontalAction hO hD
        (fun y => referenceFrameConnectionCoefficient g L lam y (referenceMetricGramFrame g L (lam,y) a))
        (fun y => referenceMetricGramFrame g L (lam,y) a) F x +
      referenceFrameDerivative g L lam a f x • coreDegree hO hD F x := by
  rw [referenceWeightedInputField, referenceHorizontalField_representative hO hD g hg L lam a F r x,
    ← coreDegree_eq_ambientDegreeField hO hD F r x]

def coreModelFirstBaseAction (hF : SphereFischerInner)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  ∑ j : Fin 3, modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x
    (coreDirectionalDerivative hO hD (ReferenceDensityBounds.coordinateDirection j)
      (coreWeightOperator hO hD (besselWeight 1) F) x)

lemma modelFirstBaseField_representative (hF : SphereFischerInner)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    modelFirstBaseField hF hO hD g1 g2 hg1 L lam δ R p (representativeAmbient hO hD r)
      (contDiff_representativeAmbient hO hD r) x =
      coreModelFirstBaseAction hO hD hF g1 g2 hg1 L lam δ R p F x := by
  have heq : ambientBesselField hO hD 1 (by norm_num) (representativeAmbient hO hD r)
      (contDiff_representativeAmbient hO hD r) =
      (fun y => coreWeightOperator hO hD (besselWeight 1) F y) :=
    funext (fun y => (coreWeightOperator_eq_ambientBesselField hO hD F r 1 (by norm_num) y).symm)
  unfold modelFirstBaseField coreModelFirstBaseAction
  rw [heq]
  simp only [coreDirectionalDerivative, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_mk, PrincipalCommutator.directionalFDeriv]

lemma normalizedSecondModelError_representative_principal_first (hF : SphereFischerInner)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F)
    (x : R3) :
    normalizedSecondModelError hF hO hD g1 g2 hg1 L lam δ R p (representativeAmbient hO hD r)
      (contDiff_representativeAmbient hO hD r) x =
      ScalarBaseAdjoint.scalarSecondBase ReferenceDensityBounds.coordinateDirection
        (fun y => ConformalDepth.referenceRadius δ R p L y •
          referenceNormalizedPrincipalMatrix g1 g2 L lam y)
        (F : R3 → SphereL2) x +
      coreModelFirstBaseAction hO hD hF g1 g2 hg1 L lam δ R p F x +
      modelZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p (representativeAmbient hO hD r)
        (contDiff_representativeAmbient hO hD r) x := by
  rw [normalizedSecondModelError_full_coefficient_form hF hO hD g1 g2 hg1 L lam δ R p hδ hR,
    modelFirstBaseField_representative hO hD hF g1 g2 hg1 L lam δ R p F r x]
  have heq : ambientSphereL2 (representativeAmbient hO hD r)
      (contDiff_representativeAmbient hO hD r) = (F : R3 → SphereL2) :=
    funext (ambientSphereL2_representative hO hD r)
  rw [heq]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicAmbient
