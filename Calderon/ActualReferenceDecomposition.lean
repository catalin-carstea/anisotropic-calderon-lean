import Calderon.AmbientReferenceRaising
import Calderon.ActualRawMixedPrincipalCollection
import Calderon.ReferenceRaisingAdjunctionEndpoint
import Calderon.ProfileRadiusJets
import Calderon.SectionFiveNormalizedSecondForm

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualReferenceDecomposition
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  SmoothMovingFrameFields AmbientReferenceCovariantCore AmbientReferenceRaising
  AmbientAngularShift SmoothMetricFrame MovingFrameConnection SpectralCoreRegularity
  SpectralWeightedGraph AngularShiftGraph BoundedAngularShift HarmonicRaisingModel
  CovariantHarmonicEnergy ReferenceDensityBounds ActualRawMixedPrincipalCollection
  ActualPrincipalErrorCoefficient PrincipalCommutator ReferenceRaisingAdjunction
  ReferenceRaisingAdjunctionEndpoint ConformalDepth RadiusProfile SmoothAmbientAngularCasimir

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma vector_eq_sum_coordinateDirection (X : R3) :
    X = ∑ k : Fin 3, X k • coordinateDirection k := by
  ext k
  fin_cases k <;> simp [coordinateDirection, Fin.sum_univ_three, Pi.single_apply]

lemma fderiv_apply_eq_coordinate_sum (U : R3 → E) (x X : R3) :
    fderiv ℝ U x X = ∑ k : Fin 3, X k • directionalFDeriv (coordinateDirection k) U x := by
  conv_lhs => rw [vector_eq_sum_coordinateDirection X]
  simp only [map_sum,map_smul,directionalFDeriv]

lemma directionalFDeriv_fixed_map (K : E →L[ℝ] F) (U : R3 → E)
    (hU : ContDiff ℝ ∞ U) (X x : R3) :
    directionalFDeriv X (fun y => K (U y)) x = K (directionalFDeriv X U x) := by
  unfold directionalFDeriv
  have hd := K.hasFDerivAt.comp x ((hU.differentiable (by simp) x).hasFDerivAt)
  change (fderiv ℝ (K ∘ U) x) X = K ((fderiv ℝ U x) X)
  rw [hd.fderiv]
  rfl

/-- Actual connection coefficient in the source Gram frame. -/
def referenceConnectionEntry (g : MatrixField) (L lam : ℝ) (i a b : Fin 3) (x : R3) : ℝ :=
  referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) i) a b

lemma contDiff_referenceConnectionEntry (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (i a b : Fin 3) : ContDiff ℝ ∞ (referenceConnectionEntry g L lam i a b) :=
  contDiff_referenceFrameConnectionCoefficient_field g hg L lam _
    (contDiff_referenceMetricGramFrame_slice g hg L lam i) a b

/-- The horizontal connection contribution has zero base derivatives. -/
def referenceRotationField (g : MatrixField) (L lam : ℝ) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, referenceConnectionEntry g L lam i a b x •
    ambientSphereL2 (ambientAngularRotation a b G) (contDiff_ambientAngularRotation a b G hG) x

lemma referenceHorizontalField_expansion (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (i : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceHorizontalField g hg L lam i G hG x =
      (∑ k : Fin 3, referenceFrameEntryFamily g L i k (lam,x) •
        directionalFDeriv (coordinateDirection k) (ambientSphereL2 G hG) x) +
      referenceRotationField g L lam i G hG x := by
  unfold referenceHorizontalField
  dsimp only [referenceHorizontalAmbient]
  rw [
    ambientSphereL2_frameHorizontal _
      (fun a b => contDiff_referenceFrameConnectionCoefficient_field g hg L lam _
        (contDiff_referenceMetricGramFrame_slice g hg L lam i) a b)
      (fun y a b => referenceFrameConnectionCoefficient_skew g hg L lam y
        (referenceMetricGramFrame g L (lam,y) i) a b)
      _ (contDiff_referenceMetricGramFrame_slice g hg L lam i) G hG x,
    fderiv_apply_eq_coordinate_sum]
  rfl

/-- Its genuine W1 output; raw W1 is not declared bounded. -/
def referenceRotationBesselField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (i : Fin 3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, referenceConnectionEntry g L lam i a b x •
    ambientBesselField hO hD 1 (by norm_num) (ambientAngularRotation a b G)
      (contDiff_ambientAngularRotation a b G hG) x

lemma referenceHorizontalBesselField_expansion (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (i : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceHorizontalBesselField hO hD g hg L lam 1 (by norm_num) i G hG x =
      (∑ k : Fin 3, referenceFrameEntryFamily g L i k (lam,x) •
        directionalFDeriv (coordinateDirection k) (ambientBesselField hO hD 1 (by norm_num) G hG) x) +
      referenceRotationBesselField hO hD g L lam i G hG x := by
  apply spectralGraph_output_unique hO hD (besselWeight 1)
    (referenceHorizontalField g hg L lam i G hG x)
  · exact referenceHorizontalBesselField_graph hO hD g hg L lam 1 (by norm_num) i G hG x
  · rw [referenceHorizontalField_expansion]
    intro m
    have hbase (k : Fin 3) : sphereHarmonicCoordinate hO hD m
        (directionalFDeriv (coordinateDirection k) (ambientBesselField hO hD 1 (by norm_num) G hG) x) =
        besselWeight 1 m • sphereHarmonicCoordinate hO hD m
          (directionalFDeriv (coordinateDirection k) (ambientSphereL2 G hG) x) :=
      SectionFiveErrorForms.directionalDeriv_besselGraph hO hD 1
      (coordinateDirection k) (ambientSphereL2 G hG) (ambientBesselField hO hD 1 (by norm_num) G hG)
      (contDiff_ambientSphereL2 G hG) (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG)
      (ambientBesselField_graph hO hD 1 (by norm_num) G hG) x m
    simp only [referenceRotationBesselField,referenceRotationField,map_add,map_smul,map_sum]
    simp_rw [show ∀ k : Fin 3, sphereHarmonicCoordinate hO hD m
        (directionalFDeriv (coordinateDirection k) (ambientBesselField hO hD 1 (by norm_num) G hG) x) =
        besselWeight 1 m • sphereHarmonicCoordinate hO hD m
          (directionalFDeriv (coordinateDirection k) (ambientSphereL2 G hG) x) from hbase,
      ambientBesselField_graph hO hD 1 (by norm_num) (ambientAngularRotation _ _ G)
        (contDiff_ambientAngularRotation _ _ G hG) x m]
    simp only [smul_add,Finset.smul_sum,smul_smul]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      congr 1
      ring
    · apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      congr 1
      ring

/-- Literal W1 output of Bu, where B=k. -/
def ambientDegreeBesselField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => ambientBesselField hO hD 2 (by norm_num) G hG x-
    ambientBesselField hO hD 1 (by norm_num) G hG x

lemma ambientDegreeBesselField_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientDegreeField hO hD G hG x,ambientDegreeBesselField hO hD G hG x) ∈
      sphereBesselGraph hO hD 1 := by
  intro k
  simp only [ambientDegreeBesselField,map_sub,
    ambientBesselField_graph hO hD 2 (by norm_num) G hG x k,
    ambientBesselField_graph hO hD 1 (by norm_num) G hG x k,
    ambientDegreeField_coordinate,besselWeight,Real.rpow_two,Real.rpow_one]
  module

/-- Literal coordinate raising first part already used by the raw mixed collection. -/
def referenceCoordinateRaising (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  frameRaisingFirst (fun i k y => referenceFrameEntryFamily g L i k (lam,y))
    (fun i => ambientRaisingField hF hO hD i G hG)

def referenceCoordinateLowering (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  frameLoweringFirst (fun i k y => referenceFrameEntryFamily g L i k (lam,y))
    (fun i => ambientDerivativeField hF hO hD i G hG)

/-- Two angular derivatives and no base derivative, with actual connection coefficients. -/
def referenceConnectionRaising (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ i : Fin 3, (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
    referenceConnectionEntry g L lam i a b x •
      ambientRaisingField hF hO hD i (ambientAngularRotation a b G)
        (contDiff_ambientAngularRotation a b G hG) x

def referenceConnectionLowering (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ i : Fin 3, (-1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
    referenceConnectionEntry g L lam i a b x •
      ambientDerivativeField hF hO hD i (ambientAngularRotation a b G)
        (contDiff_ambientAngularRotation a b G hG) x

def referenceProfileRaising (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ i : Fin 3, referenceFrameDerivative g L lam i f x •
    normalizedRaising hF hO hD i (ambientDegreeBesselField hO hD G hG x)

def referenceProfileLowering (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ i : Fin 3, referenceFrameDerivative g L lam i f x •
    normalizedDerivative hF hO hD i (ambientDegreeBesselField hO hD G hG x)

/-- Full source T, with no degree omitted and no decomposition supplied as a premise. -/
theorem referenceAllModeRaising_decomposition (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceAllModeRaising hF hO hD g hg L lam f G hG x =
      referenceCoordinateRaising hF hO hD g L lam G hG x +
      referenceConnectionRaising hF hO hD g L lam G hG x +
      referenceProfileRaising hF hO hD g L lam f G hG x := by
  simp only [referenceAllModeRaising,referenceWeightedBesselField,
    referenceHorizontalBesselField_expansion,one_smul,ambientDegreeBesselField,
    map_add,map_smul,map_sum,Finset.sum_add_distrib]
  simp only [referenceCoordinateRaising,frameRaisingFirst,referenceConnectionRaising,
    referenceProfileRaising,referenceRotationBesselField,ambientRaisingField,
    map_smul,map_sum]
  have hfixed (i k : Fin 3) :
      directionalFDeriv (coordinateDirection k) (ambientRaisingField hF hO hD i G hG) x =
        normalizedRaising hF hO hD i
          (directionalFDeriv (coordinateDirection k)
            (ambientBesselField hO hD 1 (by norm_num) G hG) x) := by
    change directionalFDeriv (coordinateDirection k)
      (fun y => normalizedRaising hF hO hD i
        (ambientBesselField hO hD 1 (by norm_num) G hG y)) x = _
    exact directionalFDeriv_fixed_map _ _
      (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG) _ _
  simp_rw [hfixed]
  dsimp only [ambientDegreeBesselField]

/-- Full source Tflat, retaining the degree-one to constant endpoint. -/
theorem referenceAllModeLowering_decomposition (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceAllModeLowering hF hO hD g hg L lam f G hG x =
      referenceCoordinateLowering hF hO hD g L lam G hG x +
      referenceConnectionLowering hF hO hD g L lam G hG x +
      referenceProfileLowering hF hO hD g L lam f G hG x := by
  simp only [referenceAllModeLowering,referenceWeightedBesselField,
    referenceHorizontalBesselField_expansion,ambientDegreeBesselField,
    smul_add,Finset.smul_sum,smul_smul,map_add,map_smul,map_sum,Finset.sum_add_distrib]
  simp only [referenceCoordinateLowering,frameLoweringFirst,referenceConnectionLowering,
    referenceProfileLowering,referenceRotationBesselField,ambientDerivativeField,
    map_smul,map_sum,Finset.smul_sum,smul_smul]
  have hfixed (i k : Fin 3) :
      directionalFDeriv (coordinateDirection k) (ambientDerivativeField hF hO hD i G hG) x =
        normalizedDerivative hF hO hD i
          (directionalFDeriv (coordinateDirection k)
            (ambientBesselField hO hD 1 (by norm_num) G hG) x) := by
    change directionalFDeriv (coordinateDirection k)
      (fun y => normalizedDerivative hF hO hD i
        (ambientBesselField hO hD 1 (by norm_num) G hG y)) x = _
    exact directionalFDeriv_fixed_map _ _
      (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG) _ _
  simp_rw [hfixed]
  dsimp only [ambientDegreeBesselField]
  have hn : (-1/2 : ℝ) = -(1/2 : ℝ) := by ring
  simp only [hn,neg_one_smul,neg_mul,one_mul,neg_smul,Finset.sum_neg_distrib]

/-- Exact source Z, constructed from the actual angular derivative output. -/
def referenceAllModeDefect (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ i : Fin 3, referenceFrameDerivative g L lam i f x • ambientDerivativeField hF hO hD i G hG x

/-- Independent differential expression, to be identified by compact adjunction separately. -/
def referenceAllModeAdjointExpression (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (f : R3 → ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ i : Fin 3, normalizedDerivative hF hO hD i
    ((-1 : ℝ) • referenceHorizontalBesselField hO hD g hg L lam 1 (by norm_num) i G hG x +
      referenceFrameDerivative g L lam i f x •
        (ambientBesselField hO hD 2 (by norm_num) G hG x-
          (2 : ℝ) • ambientBesselField hO hD 1 (by norm_num) G hG x))

lemma referenceAllModeLowering_sub_adjointExpression (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceAllModeLowering hF hO hD g hg L lam f G hG x-
      referenceAllModeAdjointExpression hF hO hD g hg L lam f G hG x =
      referenceAllModeDefect hF hO hD g L lam f G hG x := by
  simp only [referenceAllModeLowering,referenceWeightedBesselField,
    referenceAllModeAdjointExpression,referenceAllModeDefect,ambientDerivativeField,
    map_add,map_sub,map_smul,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  module

lemma contDiff_referenceAllModeDefect (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceAllModeDefect hF hO hD g L lam f G hG) :=
  ContDiff.sum fun i _ =>
    (contDiff_referenceFrameDerivative g hg L lam i f hf).smul
      (contDiff_ambientDerivativeField hF hO hD i G hG)

lemma contDiff_referenceAllModeAdjointExpression (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceAllModeAdjointExpression hF hO hD g hg L lam f G hG) := by
  have he : referenceAllModeAdjointExpression hF hO hD g hg L lam f G hG =
      fun x => referenceAllModeLowering hF hO hD g hg L lam f G hG x-
        referenceAllModeDefect hF hO hD g L lam f G hG x := by
    funext x
    have h := referenceAllModeLowering_sub_adjointExpression hF hO hD g hg L lam f G hG x
    rw [sub_eq_iff_eq_add.mp h]
    module
  rw [he]
  exact (contDiff_referenceAllModeLowering hF hO hD g hg L lam f hf G hG).sub
    (contDiff_referenceAllModeDefect hF hO hD g hg L lam f hf G hG)

lemma referenceAllModeDefect_eq_zero (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (L lam : ℝ) (f : R3 → ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (x : R3) (hx : x ∉ K) : referenceAllModeDefect hF hO hD g L lam f G hG x = 0 := by
  simp only [referenceAllModeDefect,ambientDerivativeField_eq_zero hF hO hD _ G hG K hz x hx,
    smul_zero,Finset.sum_const_zero]

lemma hasCompactSupport_referenceAllModeAdjointExpression (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (referenceAllModeAdjointExpression hF hO hD g hg L lam f G hG) := by
  apply HasCompactSupport.intro hK
  intro x hx
  have h := referenceAllModeLowering_sub_adjointExpression hF hO hD g hg L lam f G hG x
  rw [referenceAllModeLowering_eq_zero hF hO hD g hg L lam f G hG K hK hz x hx,
    referenceAllModeDefect_eq_zero hF hO hD g L lam f G hG K hz x hx] at h
  simpa using h

/-- Missing generic k=0 coordinate formula is derived rather than imposing mean zero. -/
lemma referenceAllModeRaising_coordinate_one (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    sphereHarmonicCoordinate hO hD 1 (referenceAllModeRaising hF hO hD g hg L lam f G hG x) =
      referenceHarmonicConstantRaising hF g L lam
        (fun y => sphereHarmonicCoordinate hO hD 0 (ambientSphereL2 G hG y)) x := by
  rw [referenceAllModeRaising,map_sum]
  unfold referenceHarmonicConstantRaising
  apply Finset.sum_congr rfl
  intro i _
  rw [(normalizedRaising_graph hF hO hD i _ _
    (referenceWeightedBesselField_graph hO hD g hg L lam 1 i f G hG x)).2 0,
    referenceWeightedInputField_coordinate]
  simp [referenceWeightedHarmonicDerivative]

lemma referenceAllModeAdjointExpression_coordinate_positive (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (m : ℕ) (x : R3) :
    sphereHarmonicCoordinate hO hD (m+1)
      (referenceAllModeAdjointExpression hF hO hD g hg L lam f G hG x) =
      referenceHarmonicRaisingAdjoint hF g L lam m
        (fun y => sphereHarmonicCoordinate hO hD ((m+1)+1) (ambientSphereL2 G hG y)) f x := by
  have h := congrArg (sphereHarmonicCoordinate hO hD (m+1))
    (referenceAllModeLowering_sub_adjointExpression hF hO hD g hg L lam f G hG x)
  rw [map_sub,referenceAllModeLowering_coordinate] at h
  have hz : sphereHarmonicCoordinate hO hD (m+1)
      (referenceAllModeDefect hF hO hD g L lam f G hG x) =
      referenceHarmonicRaisingDefect hF g L lam m
        (fun y => sphereHarmonicCoordinate hO hD ((m+1)+1) (ambientSphereL2 G hG y)) f x := by
    simp only [referenceAllModeDefect,referenceHarmonicRaisingDefect,map_sum,map_smul,
      referenceFrameDerivative,ambientDerivativeField_graph hF hO hD _ G hG x (m+1)]
  rw [hz] at h
  have he := h.trans (referenceHarmonicLowering_sub_adjoint hF g L lam m
    (fun y => sphereHarmonicCoordinate hO hD ((m+1)+1) (ambientSphereL2 G hG y)) f x).symm
  simpa only [sub_right_inj] using he

lemma referenceAllModeAdjointExpression_coordinate_zero (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    sphereHarmonicCoordinate hO hD 0
      (referenceAllModeAdjointExpression hF hO hD g hg L lam f G hG x) =
      referenceHarmonicDegreeOneRaisingAdjoint hF g L lam
        (fun y => sphereHarmonicCoordinate hO hD 1 (ambientSphereL2 G hG y)) x := by
  have h := congrArg (sphereHarmonicCoordinate hO hD 0)
    (referenceAllModeLowering_sub_adjointExpression hF hO hD g hg L lam f G hG x)
  rw [map_sub,referenceAllModeLowering_coordinate] at h
  have hz : sphereHarmonicCoordinate hO hD 0
      (referenceAllModeDefect hF hO hD g L lam f G hG x) =
      referenceHarmonicDegreeOneRaisingDefect hF g L lam
        (fun y => sphereHarmonicCoordinate hO hD 1 (ambientSphereL2 G hG y)) f x := by
    simp only [referenceAllModeDefect,referenceHarmonicDegreeOneRaisingDefect,map_sum,map_smul,
      referenceFrameDerivative,ambientDerivativeField_graph hF hO hD _ G hG x 0]
  rw [hz] at h
  have he := h.trans (referenceHarmonicLowering_zero_sub_adjoint hF g L lam
    (fun y => sphereHarmonicCoordinate hO hD 1 (ambientSphereL2 G hG y)) f x).symm
  simpa only [Nat.zero_add, sub_right_inj] using he

/-- Source specialization: f is the actual logarithmic radius. -/
lemma contDiff_referenceLogRadius_actual (δ R L : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) : ContDiff ℝ ∞ (referenceLogRadius δ R p L) :=
  contDiff_log_referenceRadius_profile δ R L p hδ hR

/-- Coordinate T0 has its genuine actual reference-density adjoint on this compact core. -/
theorem compact_referenceCoordinateRaising_adjoint (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (G H : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪referenceCoordinateRaising hF hO hD g L lam G hG x,ambientSphereL2 H hH x⟫_ℝ) =
      ∫ x : R3, referenceDensityFamily g L (lam,x) *
        ⟪ambientSphereL2 G hG x,
          frameRaisingFirstAdjoint (fun y => referenceDensityFamily g L (lam,y))
            (fun i k y => referenceFrameEntryFamily g L i k (lam,y))
            (fun i => ambientDerivativeField hF hO hD i H hH) x⟫_ℝ := by
  apply compact_frameRaisingFirst_adjoint hF hO hD
  · exact (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  · intro i k
    exact (contDiff_referenceFrameEntryFamily g hg L i k).comp (contDiff_const.prodMk contDiff_id)
  · exact contDiff_ambientSphereL2 G hG
  · intro i; exact contDiff_ambientRaisingField hF hO hD i G hG
  · intro i; exact contDiff_ambientDerivativeField hF hO hD i H hH
  · exact hasCompactSupport_ambientSphereL2 G hG K hK hz
  · intro y; exact referenceDensityFamily_pos g hg L (lam,y)
  · intro i y; exact ambientRaisingField_graph hF hO hD i G hG y
  · intro i y; exact ambientDerivativeField_graph hF hO hD i H hH y

lemma contDiff_referenceConnectionRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceConnectionRaising hF hO hD g L lam G hG) := by
  apply ContDiff.sum; intro i _
  apply ContDiff.const_smul (1/2 : ℝ)
  apply ContDiff.sum; intro a _
  apply ContDiff.sum; intro b _
  exact (contDiff_referenceConnectionEntry g hg L lam i a b).smul
    (contDiff_ambientRaisingField hF hO hD i (ambientAngularRotation a b G)
      (contDiff_ambientAngularRotation a b G hG))

lemma contDiff_referenceConnectionLowering (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceConnectionLowering hF hO hD g L lam G hG) := by
  apply ContDiff.sum; intro i _
  apply ContDiff.const_smul (-1/2 : ℝ)
  apply ContDiff.sum; intro a _
  apply ContDiff.sum; intro b _
  exact (contDiff_referenceConnectionEntry g hg L lam i a b).smul
    (contDiff_ambientDerivativeField hF hO hD i (ambientAngularRotation a b G)
      (contDiff_ambientAngularRotation a b G hG))

lemma contDiff_referenceProfileParts (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceProfileRaising hF hO hD g L lam f G hG) ∧
    ContDiff ℝ ∞ (referenceProfileLowering hF hO hD g L lam f G hG) := by
  have hb : ContDiff ℝ ∞ (ambientDegreeBesselField hO hD G hG) :=
    (contDiff_ambientBesselField hO hD 2 (by norm_num) G hG).sub
      (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG)
  constructor
  · exact ContDiff.sum fun i _ => (contDiff_referenceFrameDerivative g hg L lam i f hf).smul
      ((normalizedRaising hF hO hD i).contDiff.comp hb)
  · exact ContDiff.sum fun i _ => (contDiff_referenceFrameDerivative g hg L lam i f hf).smul
      ((normalizedDerivative hF hO hD i).contDiff.comp hb)

lemma hasCompactSupport_referenceConnectionParts (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (referenceConnectionRaising hF hO hD g L lam G hG) ∧
    HasCompactSupport (referenceConnectionLowering hF hO hD g L lam G hG) := by
  constructor <;> apply HasCompactSupport.intro hK <;> intro x hx
  · simp only [referenceConnectionRaising,
      ambientRaisingField_eq_zero hF hO hD _ (ambientAngularRotation _ _ G)
        (contDiff_ambientAngularRotation _ _ G hG) K
        (ambientAngularRotation_sphere_zero _ _ G hG K hz) x hx,
      smul_zero,Finset.sum_const_zero]
  · simp only [referenceConnectionLowering,
      ambientDerivativeField_eq_zero hF hO hD _ (ambientAngularRotation _ _ G)
        (contDiff_ambientAngularRotation _ _ G hG) K
        (ambientAngularRotation_sphere_zero _ _ G hG K hz) x hx,
      smul_zero,Finset.sum_const_zero]

lemma hasCompactSupport_referenceProfileParts (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (L lam : ℝ) (f : R3 → ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (referenceProfileRaising hF hO hD g L lam f G hG) ∧
    HasCompactSupport (referenceProfileLowering hF hO hD g L lam f G hG) := by
  have hb (x : R3) (hx : x ∉ K) : ambientDegreeBesselField hO hD G hG x = 0 := by
    simp [ambientDegreeBesselField,ambientBesselField_eq_zero hO hD _ _ G hG K hz x hx]
  constructor <;> apply HasCompactSupport.intro hK <;> intro x hx
  · simp [referenceProfileRaising,hb x hx]
  · simp [referenceProfileLowering,hb x hx]

/-- Actual source f, full operators and the independently constructed expression are on the smooth compact core. -/
theorem actual_referenceAllMode_core (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    ContDiff ℝ ∞ (referenceAllModeRaising hF hO hD g hg L lam (referenceLogRadius δ R p L) G hG) ∧
    ContDiff ℝ ∞ (referenceAllModeLowering hF hO hD g hg L lam (referenceLogRadius δ R p L) G hG) ∧
    ContDiff ℝ ∞ (referenceAllModeAdjointExpression hF hO hD g hg L lam (referenceLogRadius δ R p L) G hG) ∧
    HasCompactSupport (referenceAllModeRaising hF hO hD g hg L lam (referenceLogRadius δ R p L) G hG) ∧
    HasCompactSupport (referenceAllModeLowering hF hO hD g hg L lam (referenceLogRadius δ R p L) G hG) ∧
    HasCompactSupport (referenceAllModeAdjointExpression hF hO hD g hg L lam (referenceLogRadius δ R p L) G hG) := by
  have hf := contDiff_referenceLogRadius_actual δ R L p hδ hR
  exact ⟨contDiff_referenceAllModeRaising hF hO hD g hg L lam _ hf G hG,
    contDiff_referenceAllModeLowering hF hO hD g hg L lam _ hf G hG,
    contDiff_referenceAllModeAdjointExpression hF hO hD g hg L lam _ hf G hG,
    hasCompactSupport_referenceAllModeRaising hF hO hD g hg L lam _ G hG K hK hz,
    hasCompactSupport_referenceAllModeLowering hF hO hD g hg L lam _ G hG K hK hz,
    hasCompactSupport_referenceAllModeAdjointExpression hF hO hD g hg L lam _ G hG K hK hz⟩

/-- Full adjoint expression relative to the genuine coordinate density adjoint.
The remaining terms are literal connection/profile/degree/density terms, without a form-bound premise. -/
theorem referenceAllModeAdjointExpression_decomposition (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceAllModeAdjointExpression hF hO hD g hg L lam f G hG x =
      frameRaisingFirstAdjoint (fun y => referenceDensityFamily g L (lam,y))
        (fun i k y => referenceFrameEntryFamily g L i k (lam,y))
        (fun i => ambientDerivativeField hF hO hD i G hG) x +
      referenceConnectionLowering hF hO hD g L lam G hG x +
      referenceProfileLowering hF hO hD g L lam f G hG x -
      referenceAllModeDefect hF hO hD g L lam f G hG x -
      frameDensityZero (fun y => referenceDensityFamily g L (lam,y))
        (fun i k y => referenceFrameEntryFamily g L i k (lam,y))
        (fun i => ambientDerivativeField hF hO hD i G hG) x := by
  have hm : ContDiff ℝ ∞ (fun y : R3 => referenceDensityFamily g L (lam,y)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hc (i k : Fin 3) : ContDiff ℝ ∞ (fun y : R3 => referenceFrameEntryFamily g L i k (lam,y)) :=
    (contDiff_referenceFrameEntryFamily g hg L i k).comp (contDiff_const.prodMk contDiff_id)
  have hcoef := frameRaisingFirstAdjoint_coefficient_form
    (fun y => referenceDensityFamily g L (lam,y))
    (fun i k y => referenceFrameEntryFamily g L i k (lam,y))
    (fun i => ambientDerivativeField hF hO hD i G hG) hm hc
    (fun i => contDiff_ambientDerivativeField hF hO hD i G hG)
    (fun y => ne_of_gt (referenceDensityFamily_pos g hg L (lam,y))) x
  have hd := referenceAllModeLowering_sub_adjointExpression hF hO hD g hg L lam f G hG x
  have he : referenceAllModeAdjointExpression hF hO hD g hg L lam f G hG x =
      referenceAllModeLowering hF hO hD g hg L lam f G hG x-
        referenceAllModeDefect hF hO hD g L lam f G hG x := by
    rw [sub_eq_iff_eq_add.mp hd]
    module
  rw [he,referenceAllModeLowering_decomposition,hcoef]
  change _ = (referenceCoordinateLowering hF hO hD g L lam G hG x + _) + _ + _ - _ - _
  module

end OAI.AnisotropicCalderon.ActualReferenceDecomposition
