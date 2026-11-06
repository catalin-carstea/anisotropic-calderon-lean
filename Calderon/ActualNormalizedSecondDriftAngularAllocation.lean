import Calderon.ActualNormalizedSecondMetricDrift
import Calderon.ActualReferenceDDNormalizedCoefficient

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondDriftAngularAllocation
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift BoundedSpectralMultiplier SmoothSphereFields SmoothAngularApplication
  AmbientAngularShift AmbientReferenceRaising SmoothMetricFrame MovingFrameConnection
  ActualReferenceScaledRaisingTransport ActualReferenceModelTrace ActualReferenceDecomposition
  ActualReferenceOrdinaryPrincipal ActualReferenceDDNormalizedCoefficient
  ActualNormalizedSecondMetricDrift ReferenceDensityBounds PrincipalCommutator ConformalDepth RadiusProfile
  ActualPhysicalPureAngular HarmonicRaisingModel
  ActualScalarPrincipalAdjoint WeightedBaseSpectral

def normalizedSecondModelDriftField (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => referenceRadius δ R p L x • ∑ a : Fin 3,
    normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
      referenceModelInputField hF hO hD g1 hg1 L lam δ R p a G hG x

def normalizedSecondWeightedDriftField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => referenceRadius δ R p L x • ∑ a : Fin 3,
    normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
      referenceWeightedInputField hO hD g1 hg1 L lam 1 a
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x

def normalizedSecondRaisingDriftField (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => ∑ a : Fin 3, normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
    ambientRaisingField hF hO hD a G hG x

def normalizedSecondDriftFirstBaseField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => referenceRadius δ R p L x • ∑ j : Fin 3,
    normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x) •
      directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x

def normalizedSecondDriftZeroBaseField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => referenceRadius δ R p L x • ∑ a : Fin 3,
    normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
      referenceWeightedZeroBaseField hO hD g1 hg1 L lam δ R p a G hG x

def normalizedSecondWeightedDriftBesselField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => referenceRadius δ R p L x • ∑ a : Fin 3,
    normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
      referenceWeightedBesselField hO hD g1 hg1 L lam 1 a
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x

def normalizedSecondRaisingDriftBesselField (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => ∑ a : Fin 3, normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
    ambientRaisingBesselField hF hO hD a G hG x

def normalizedSecondDriftFirstNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (j : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  (referenceRadius δ R p L x * normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)) •
    inverseDegreeMultiplier hO hD

def normalizedSecondDriftZeroNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  referenceRadius δ R p L x • ∑ a : Fin 3,
    normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
      (referenceWeightedZeroBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p a x).comp
        (inverseDegreeMultiplier hO hD)

theorem normalizedSecondModelDriftField_split (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
  normalizedSecondModelDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG x = normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG x + normalizedSecondRaisingDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG x :=
by
  have hr : referenceRadius δ R p L x ≠ 0 :=
    (referenceRadius_pos δ R p L x hδ hR).ne'
  unfold normalizedSecondModelDriftField normalizedSecondWeightedDriftField
    normalizedSecondRaisingDriftField referenceModelInputField inverseRadiusRaisingField
  simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  calc
    referenceRadius δ R p L x *
        (normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) *
          (referenceRadius δ R p L x)⁻¹) =
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) *
        (referenceRadius δ R p L x * (referenceRadius δ R p L x)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hr, mul_one]

theorem normalizedSecondWeightedDriftField_ordinary_split (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
  normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG x = normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x + normalizedSecondDriftZeroBaseField hO hD g1 g2 hg1 L lam δ R p G hG x :=
by
  have hphi (X : R3) : directionalFDeriv X (ambientSphereL2 G hG) x =
      ∑ j : Fin 3, X j • directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x := by
    simpa only [directionalFDeriv] using
      fderiv_apply_eq_coordinate_sum (ambientSphereL2 G hG) x X
  have hbase : (∑ a : Fin 3, normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
      directionalFDeriv (referenceMetricGramFrame g1 L (lam,x) a) (ambientSphereL2 G hG) x) =
      ∑ j : Fin 3, normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x) •
        directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x := by
    have hterm (a : Fin 3) :
        normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
          directionalFDeriv (referenceMetricGramFrame g1 L (lam,x) a) (ambientSphereL2 G hG) x =
        ∑ j : Fin 3, (normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) *
          referenceMetricGramFrame g1 L (lam,x) a j) •
          directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x := by
      rw [hphi,Finset.smul_sum]
      simp only [smul_smul]
    calc
      _ = ∑ a : Fin 3, ∑ j : Fin 3,
          (normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) *
            referenceMetricGramFrame g1 L (lam,x) a j) •
            directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x :=
        Finset.sum_congr rfl (fun a _ => hterm a)
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_smul,normalizedSecondDriftFrame_coordinate_conversion g1 g2 hg1 L lam x j]
  calc
    normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG x =
        referenceRadius δ R p L x •
          ((∑ a : Fin 3, normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
            directionalFDeriv (referenceMetricGramFrame g1 L (lam,x) a) (ambientSphereL2 G hG) x) +
           (∑ a : Fin 3, normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
             referenceWeightedZeroBaseField hO hD g1 hg1 L lam δ R p a G hG x)) := by
      unfold normalizedSecondWeightedDriftField
      simp_rw [referenceWeightedInputField_ordinary_expansion hO hD g1 hg1 L lam δ R p]
      simp only [smul_add,Finset.sum_add_distrib]
    _ = normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x +
        normalizedSecondDriftZeroBaseField hO hD g1 g2 hg1 L lam δ R p G hG x := by
      rw [hbase,smul_add]
      rfl


theorem normalizedSecondWeightedDriftField_normalized_representation (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
  normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG x =
    (∑ j : Fin 3, normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
      (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x)) +
    normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p x
      (ambientBesselField hO hD 2 (by norm_num) G hG x) :=
by
  have hfirst : normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x =
      ∑ j : Fin 3, normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
        (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x) := by
    have hterm (j : Fin 3) : normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
        (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x) =
        referenceRadius δ R p L x • (normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x) •
          directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x) := by
      unfold normalizedSecondDriftFirstNormalizedCoefficient
      rw [ContinuousLinearMap.smul_apply,inverseDegreeMultiplier_directional_ambientBesselField_one hO hD G hG x (coordinateDirection j)]
      rw [smul_smul]
    unfold normalizedSecondDriftFirstBaseField
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (hterm j).symm
  have hzero : normalizedSecondDriftZeroBaseField hO hD g1 g2 hg1 L lam δ R p G hG x =
      normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p x
        (ambientBesselField hO hD 2 (by norm_num) G hG x) := by
    unfold normalizedSecondDriftZeroBaseField normalizedSecondDriftZeroNormalizedCoefficient
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
    rw [inverseDegreeMultiplier_ambientBesselField_two hO hD G hG x]
    simp_rw [referenceWeightedZeroBaseNormalizedCoefficient_apply_one hO hD g1 hg1 L lam δ R p _ G hG x]
  rw [normalizedSecondWeightedDriftField_ordinary_split hO hD g1 g2 hg1 L lam δ R p G hG x]
  exact congrArg₂ (fun a b : SphereL2 => a+b) hfirst hzero


lemma normalizedSecondWeightedDriftBesselField_graph (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
  (normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG x, normalizedSecondWeightedDriftBesselField hO hD g1 g2 hg1 L lam δ R p G hG x) ∈
    sphereBesselGraph hO hD 1 :=
by
  intro k
  change sphereHarmonicCoordinate hO hD k
      (normalizedSecondWeightedDriftBesselField hO hD g1 g2 hg1 L lam δ R p G hG x) =
    besselWeight 1 k • sphereHarmonicCoordinate hO hD k
      (normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG x)
  unfold normalizedSecondWeightedDriftBesselField normalizedSecondWeightedDriftField
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  rw [referenceWeightedBesselField_graph hO hD g1 hg1 L lam 1 a
    (fun y => Real.log (referenceRadius δ R p L y)) G hG x k]
  simp only [smul_smul]
  congr 1
  ring

lemma normalizedSecondRaisingDriftBesselField_graph (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
  (normalizedSecondRaisingDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG x, normalizedSecondRaisingDriftBesselField hF hO hD g1 g2 hg1 L lam δ R p G hG x) ∈
    sphereBesselGraph hO hD 1 :=
by
  intro k
  change sphereHarmonicCoordinate hO hD k
      (normalizedSecondRaisingDriftBesselField hF hO hD g1 g2 hg1 L lam δ R p G hG x) =
    besselWeight 1 k • sphereHarmonicCoordinate hO hD k
      (normalizedSecondRaisingDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG x)
  unfold normalizedSecondRaisingDriftBesselField normalizedSecondRaisingDriftField
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  rw [ambientRaisingBesselField_graph hF hO hD a G hG x k]
  simp only [smul_smul]
  congr 1
  ring

lemma normalizedSecondRaisingDriftField_component_graph (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) (a : Fin 3) :
  (normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) • ambientSphereL2 G hG x,
    normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) • ambientRaisingField hF hO hD a G hG x) ∈
      sphereRaisingGraph hF hO hD a :=
by
  exact (sphereRaisingGraph hF hO hD a).smul_mem
    (normalizedSecondDriftFrameJoint g1 g2 L a (lam,x))
    (ambientRaisingField_graph hF hO hD a G hG x)

lemma normalizedSecondRaisingDriftField_coordinates (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
  sphereHarmonicCoordinate hO hD 0 (normalizedSecondRaisingDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG x) = 0 ∧
  ∀ m : ℕ, sphereHarmonicCoordinate hO hD (m+1) (normalizedSecondRaisingDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG x) =
    ∑ a : Fin 3, normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
      HarmonicDerivativeOperator.harmonicDerivativeAdjoint hF m a
        (sphereHarmonicCoordinate hO hD m (ambientSphereL2 G hG x)) :=
by
  constructor
  · unfold normalizedSecondRaisingDriftField
    simp only [map_sum, map_smul]
    simp_rw [(ambientRaisingField_graph hF hO hD _ G hG x).1]
    simp only [smul_zero, Finset.sum_const_zero]
  · intro m
    unfold normalizedSecondRaisingDriftField
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro a _
    rw [(ambientRaisingField_graph hF hO hD a G hG x).2 m]

lemma normalizedSecondWeightedDriftField_coordinate (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) (k : ℕ) :
  sphereHarmonicCoordinate hO hD k (normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG x) =
    referenceRadius δ R p L x • ∑ a : Fin 3,
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
        referenceWeightedHarmonicDerivative g1 L lam k
          (fun y => sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG y))
          (fun y => Real.log (referenceRadius δ R p L y)) 1 x
          (referenceMetricGramFrame g1 L (lam,x) a) :=
by
  unfold normalizedSecondWeightedDriftField
  simp only [map_smul, map_sum]
  simp_rw [referenceWeightedInputField_coordinate hO hD g1 hg1 L lam 1 _
    (fun y => Real.log (referenceRadius δ R p L y)) G hG k x]

lemma contDiff_normalizedSecondWeightedDriftField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) : ContDiff ℝ ∞ (normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG) :=
by
  have hb (a : Fin 3) : ContDiff ℝ ∞
      (fun x : R3 => normalizedSecondDriftFrameJoint g1 g2 L a (lam,x)) := by
    simpa only [Function.comp_def, Function.id_def] using
      (contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a).comp
        (contDiff_const.prodMk contDiff_id)
  have hs : ContDiff ℝ ∞ (fun x : R3 => ∑ a : Fin 3,
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
        referenceWeightedInputField hO hD g1 hg1 L lam 1 a
          (fun y => Real.log (referenceRadius δ R p L y)) G hG x) :=
    ContDiff.sum (fun a _ => (hb a).smul (contDiff_referenceWeightedInputField hO hD g1 hg1 L lam 1 a
        (fun y => Real.log (referenceRadius δ R p L y))
        (contDiff_log_referenceRadius_profile δ R L p hδ hR) G hG))
  unfold normalizedSecondWeightedDriftField
  exact (contDiff_referenceRadius_actual δ R p L hδ hR).smul hs

lemma normalizedSecondWeightedDriftField_eq_zero_outside (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
  normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG x = 0 :=
by
  unfold normalizedSecondWeightedDriftField
  simp_rw [referenceWeightedInputField_eq_zero_outside hO hD g1 hg1 L lam δ R p _ G hG K hK hz x hx]
  simp only [smul_zero, Finset.sum_const_zero]

lemma hasCompactSupport_normalizedSecondWeightedDriftField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
  HasCompactSupport (normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG) :=
by
  exact HasCompactSupport.intro hK
    (fun x hx => normalizedSecondWeightedDriftField_eq_zero_outside hO hD g1 g2 hg1 L lam δ R p G hG K hK hz x hx)

lemma integrable_normalizedSecondWeightedDriftField_norm_sq (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
  Integrable (fun x => referenceDensityFamily g1 L (lam,x) * ‖normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG x‖^2) :=
by
  exact integrable_referenceBase_norm_sq g1 hg1 L lam _
    (contDiff_normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR).continuous
    (hasCompactSupport_normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG K hK hz)

lemma contDiff_normalizedSecondRaisingDriftField (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) : ContDiff ℝ ∞ (normalizedSecondRaisingDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG) :=
by
  have hb (a : Fin 3) : ContDiff ℝ ∞
      (fun x : R3 => normalizedSecondDriftFrameJoint g1 g2 L a (lam,x)) := by
    simpa only [Function.comp_def, Function.id_def] using
      (contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a).comp
        (contDiff_const.prodMk contDiff_id)
  have hs : ContDiff ℝ ∞ (fun x : R3 => ∑ a : Fin 3,
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
        ambientRaisingField hF hO hD a G hG x) :=
    ContDiff.sum (fun a _ => (hb a).smul (contDiff_ambientRaisingField hF hO hD a G hG))
  unfold normalizedSecondRaisingDriftField
  exact hs

lemma normalizedSecondRaisingDriftField_eq_zero_outside (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
  normalizedSecondRaisingDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG x = 0 :=
by
  unfold normalizedSecondRaisingDriftField
  simp_rw [ambientRaisingField_eq_zero hF hO hD _ G hG K hz x hx]
  simp only [smul_zero, Finset.sum_const_zero]

lemma hasCompactSupport_normalizedSecondRaisingDriftField (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
  HasCompactSupport (normalizedSecondRaisingDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG) :=
by
  exact HasCompactSupport.intro hK
    (fun x hx => normalizedSecondRaisingDriftField_eq_zero_outside hF hO hD g1 g2 hg1 L lam δ R p G hG K hK hz x hx)

lemma integrable_normalizedSecondRaisingDriftField_norm_sq (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
  Integrable (fun x => referenceDensityFamily g1 L (lam,x) * ‖normalizedSecondRaisingDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG x‖^2) :=
by
  exact integrable_referenceBase_norm_sq g1 hg1 L lam _
    (contDiff_normalizedSecondRaisingDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR).continuous
    (hasCompactSupport_normalizedSecondRaisingDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG K hK hz)

lemma contDiff_normalizedSecondModelDriftField (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) : ContDiff ℝ ∞ (normalizedSecondModelDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG) :=
by
  have hb (a : Fin 3) : ContDiff ℝ ∞
      (fun x : R3 => normalizedSecondDriftFrameJoint g1 g2 L a (lam,x)) := by
    simpa only [Function.comp_def, Function.id_def] using
      (contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a).comp
        (contDiff_const.prodMk contDiff_id)
  have hs : ContDiff ℝ ∞ (fun x : R3 => ∑ a : Fin 3,
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
        referenceModelInputField hF hO hD g1 hg1 L lam δ R p a G hG x) :=
    ContDiff.sum (fun a _ => (hb a).smul (contDiff_referenceModelInputField hF hO hD g1 hg1 L lam δ R p hδ hR a G hG))
  unfold normalizedSecondModelDriftField
  exact (contDiff_referenceRadius_actual δ R p L hδ hR).smul hs

lemma normalizedSecondModelDriftField_eq_zero_outside (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
  normalizedSecondModelDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG x = 0 :=
by
  unfold normalizedSecondModelDriftField
  simp_rw [referenceModelInputField_eq_zero_outside hF hO hD g1 hg1 L lam δ R p _ G hG K hK hz x hx]
  simp only [smul_zero, Finset.sum_const_zero]

lemma hasCompactSupport_normalizedSecondModelDriftField (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
  HasCompactSupport (normalizedSecondModelDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG) :=
by
  exact HasCompactSupport.intro hK
    (fun x hx => normalizedSecondModelDriftField_eq_zero_outside hF hO hD g1 g2 hg1 L lam δ R p G hG K hK hz x hx)

lemma integrable_normalizedSecondModelDriftField_norm_sq (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
  Integrable (fun x => referenceDensityFamily g1 L (lam,x) * ‖normalizedSecondModelDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG x‖^2) :=
by
  exact integrable_referenceBase_norm_sq g1 hg1 L lam _
    (contDiff_normalizedSecondModelDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR).continuous
    (hasCompactSupport_normalizedSecondModelDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG K hK hz)

end OAI.AnisotropicCalderon.ActualNormalizedSecondDriftAngularAllocation
