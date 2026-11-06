import Calderon.AmbientAngularShift
import Calderon.AmbientReferenceCovariantCore
import Calderon.HarmonicRaisingModel
import Calderon.PositiveSpectralCore
import Mathlib.Tactic.Module

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.AmbientReferenceRaising
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  SmoothMovingFrameFields AmbientReferenceCovariantCore SmoothMetricFrame MovingFrameConnection
  SpectralCoreRegularity SpectralWeightedGraph AngularShiftGraph BoundedAngularShift
  WeightedBaseSpectral WeightedAngularConvergence HarmonicRaisingModel CovariantHarmonicEnergy
  PositiveSpectralCore

def referenceHorizontalAmbient (g : MatrixField) (L lam : ℝ) (i : Fin 3)
    (G : R3 × R3 → ℝ) : R3 × R3 → ℝ :=
  ambientFrameHorizontal
    (fun x => referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) i))
    (fun x => referenceMetricGramFrame g L (lam,x) i) G

lemma contDiff_referenceHorizontalAmbient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (i : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceHorizontalAmbient g L lam i G) :=
  contDiff_ambientFrameHorizontal _
    (fun a b => contDiff_referenceFrameConnectionCoefficient_field g hg L lam _
      (contDiff_referenceMetricGramFrame_slice g hg L lam i) a b)
    _ (contDiff_referenceMetricGramFrame_slice g hg L lam i) G hG

def referenceHorizontalField (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (i : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    R3 → SphereL2 :=
  ambientSphereL2 (referenceHorizontalAmbient g L lam i G)
    (contDiff_referenceHorizontalAmbient g hg L lam i G hG)

def referenceHorizontalBesselField (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam s : ℝ) (hs : s ≤ 2) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  ambientBesselField hO hD s hs (referenceHorizontalAmbient g L lam i G)
    (contDiff_referenceHorizontalAmbient g hg L lam i G hG)

lemma referenceHorizontalAmbient_sphere_zero (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (i : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    ∀ x ∉ K, ∀ theta : UnitSphere, referenceHorizontalAmbient g L lam i G (x,theta.val)=0 :=
  ambientFrameHorizontal_sphere_zero _
    (fun x a b => referenceFrameConnectionCoefficient_skew g hg L lam x
      (referenceMetricGramFrame g L (lam,x) i) a b)
    _ G hG K hK.isClosed hz

lemma contDiff_referenceHorizontalField (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (i : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceHorizontalField g hg L lam i G hG) :=
  contDiff_ambientSphereL2 _ (contDiff_referenceHorizontalAmbient g hg L lam i G hG)

lemma contDiff_referenceHorizontalBesselField (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam s : ℝ) (hs : s ≤ 2) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceHorizontalBesselField hO hD g hg L lam s hs i G hG) :=
  contDiff_ambientBesselField hO hD s hs _
    (contDiff_referenceHorizontalAmbient g hg L lam i G hG)

lemma referenceHorizontalField_coordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (i : Fin 3) (k : ℕ) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    sphereHarmonicCoordinate hO hD k (referenceHorizontalField g hg L lam i G hG x) =
      referenceHarmonicCovariantDerivative g L lam k
        (fun y => sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG y)) x
        (referenceMetricGramFrame g L (lam,x) i) :=
  sphereHarmonicCoordinate_referenceFrameHorizontal hO hD g hg L lam k _
    (contDiff_referenceMetricGramFrame_slice g hg L lam i) G hG x

lemma referenceHorizontalBesselField_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam s : ℝ) (hs : s ≤ 2) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (referenceHorizontalField g hg L lam i G hG x,
      referenceHorizontalBesselField hO hD g hg L lam s hs i G hG x) ∈
        sphereBesselGraph hO hD s :=
  ambientBesselField_graph hO hD s hs _
    (contDiff_referenceHorizontalAmbient g hg L lam i G hG) x

/-- The actual source B=k, represented through its exact 1+B graph output. -/
def ambientDegreeField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => ambientBesselField hO hD 1 (by norm_num) G hG x - ambientSphereL2 G hG x

lemma ambientDegreeField_coordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (k : ℕ) (x : R3) :
    sphereHarmonicCoordinate hO hD k (ambientDegreeField hO hD G hG x) =
      (k:ℝ) • sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG x) := by
  rw [ambientDegreeField,map_sub,ambientBesselField_graph hO hD 1 (by norm_num) G hG x k]
  simp only [besselWeight,Real.rpow_one]
  module

lemma contDiff_ambientDegreeField (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientDegreeField hO hD G hG) :=
  (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG).sub
    (contDiff_ambientSphereL2 G hG)

def referenceFrameDerivative (g : MatrixField) (L lam : ℝ) (i : Fin 3)
    (f : R3 → ℝ) (x : R3) : ℝ :=
  fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) i)

lemma contDiff_referenceFrameDerivative (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (i : Fin 3) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (referenceFrameDerivative g L lam i f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiff_referenceMetricGramFrame_slice g hg L lam i)

/-- Exact D_i^s=s ∇_i+f_i B on actual all-degree fields. -/
def referenceWeightedInputField (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam s : ℝ) (i : Fin 3) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => s • referenceHorizontalField g hg L lam i G hG x +
    referenceFrameDerivative g L lam i f x • ambientDegreeField hO hD G hG x

/-- Its genuine 1+B output, constructed using actual Casimir-derived fields. -/
def referenceWeightedBesselField (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam s : ℝ) (i : Fin 3) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => s • referenceHorizontalBesselField hO hD g hg L lam 1 (by norm_num) i G hG x +
    referenceFrameDerivative g L lam i f x •
      (ambientBesselField hO hD 2 (by norm_num) G hG x -
        ambientBesselField hO hD 1 (by norm_num) G hG x)

lemma contDiff_referenceWeightedInputField (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam s : ℝ) (i : Fin 3) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceWeightedInputField hO hD g hg L lam s i f G hG) :=
  ((contDiff_referenceHorizontalField g hg L lam i G hG).const_smul s).add
    ((contDiff_referenceFrameDerivative g hg L lam i f hf).smul
      (contDiff_ambientDegreeField hO hD G hG))

lemma contDiff_referenceWeightedBesselField (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam s : ℝ) (i : Fin 3) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceWeightedBesselField hO hD g hg L lam s i f G hG) :=
  ((contDiff_referenceHorizontalBesselField hO hD g hg L lam 1 (by norm_num) i G hG).const_smul s).add
    ((contDiff_referenceFrameDerivative g hg L lam i f hf).smul
      ((contDiff_ambientBesselField hO hD 2 (by norm_num) G hG).sub
        (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG)))

lemma referenceWeightedInputField_coordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam s : ℝ) (i : Fin 3) (f : R3 → ℝ) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (k : ℕ) (x : R3) :
    sphereHarmonicCoordinate hO hD k
      (referenceWeightedInputField hO hD g hg L lam s i f G hG x) =
        referenceWeightedHarmonicDerivative g L lam k
          (fun y => sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG y)) f s x
          (referenceMetricGramFrame g L (lam,x) i) := by
  rw [referenceWeightedInputField,map_add,map_smul,map_smul,
    referenceHorizontalField_coordinate,ambientDegreeField_coordinate]
  simp only [referenceWeightedHarmonicDerivative,referenceFrameDerivative,smul_smul]
  congr 1
  congr 1
  ring

lemma referenceWeightedBesselField_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam s : ℝ) (i : Fin 3) (f : R3 → ℝ) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    (referenceWeightedInputField hO hD g hg L lam s i f G hG x,
      referenceWeightedBesselField hO hD g hg L lam s i f G hG x) ∈
        sphereBesselGraph hO hD 1 := by
  intro k
  simp only [referenceWeightedBesselField,referenceWeightedInputField,ambientDegreeField,
    map_add,map_smul,map_sub]
  rw [referenceHorizontalBesselField_graph hO hD g hg L lam 1 (by norm_num) i G hG x k,
    ambientBesselField_graph hO hD 2 (by norm_num) G hG x k,
    ambientBesselField_graph hO hD 1 (by norm_num) G hG x k]
  simp only [besselWeight,Real.rpow_one,Real.rpow_two]
  module

lemma referenceWeightedBesselField_eq_zero (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam s : ℝ) (i : Fin 3) (f : R3 → ℝ) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceWeightedBesselField hO hD g hg L lam s i f G hG x = 0 := by
  have hH := ambientBesselField_eq_zero hO hD 1 (by norm_num)
    (referenceHorizontalAmbient g L lam i G)
    (contDiff_referenceHorizontalAmbient g hg L lam i G hG) K
    (referenceHorizontalAmbient_sphere_zero g hg L lam i G hG K hK hz) x hx
  simp only [referenceWeightedBesselField,referenceHorizontalBesselField,hH,
    ambientBesselField_eq_zero hO hD 2 (by norm_num) G hG K hz x hx,
    ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx,
    smul_zero,sub_self,add_zero]

def referenceAllModeRaising (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (f : R3 → ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    R3 → SphereL2 :=
  fun x => ∑ i : Fin 3, normalizedRaising hF hO hD i
    (referenceWeightedBesselField hO hD g hg L lam 1 i f G hG x)

def referenceAllModeLowering (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (f : R3 → ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    R3 → SphereL2 :=
  fun x => ∑ i : Fin 3, normalizedDerivative hF hO hD i
    (referenceWeightedBesselField hO hD g hg L lam (-1) i f G hG x)

lemma contDiff_referenceAllModeRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceAllModeRaising hF hO hD g hg L lam f G hG) :=
  ContDiff.sum (fun i _ => (normalizedRaising hF hO hD i).contDiff.comp
    (contDiff_referenceWeightedBesselField hO hD g hg L lam 1 i f hf G hG))

lemma contDiff_referenceAllModeLowering (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceAllModeLowering hF hO hD g hg L lam f G hG) :=
  ContDiff.sum (fun i _ => (normalizedDerivative hF hO hD i).contDiff.comp
    (contDiff_referenceWeightedBesselField hO hD g hg L lam (-1) i f hf G hG))

lemma referenceAllModeRaising_coordinate_zero (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    sphereHarmonicCoordinate hO hD 0 (referenceAllModeRaising hF hO hD g hg L lam f G hG x) = 0 := by
  rw [referenceAllModeRaising,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact (normalizedRaising_graph hF hO hD i _ _
    (referenceWeightedBesselField_graph hO hD g hg L lam 1 i f G hG x)).1

lemma referenceAllModeRaising_coordinate (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (m : ℕ) (x : R3) :
    sphereHarmonicCoordinate hO hD ((m+1)+1)
      (referenceAllModeRaising hF hO hD g hg L lam f G hG x) =
        referenceHarmonicRaising hF g L lam m
          (fun y => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG y)) f x := by
  rw [referenceAllModeRaising,map_sum]
  unfold referenceHarmonicRaising
  apply Finset.sum_congr rfl
  intro i _
  rw [(normalizedRaising_graph hF hO hD i _ _
    (referenceWeightedBesselField_graph hO hD g hg L lam 1 i f G hG x)).2 (m+1)]
  rw [referenceWeightedInputField_coordinate]

lemma referenceAllModeLowering_coordinate (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (m : ℕ) (x : R3) :
    sphereHarmonicCoordinate hO hD m
      (referenceAllModeLowering hF hO hD g hg L lam f G hG x) =
        referenceHarmonicLowering hF g L lam m
          (fun y => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG y)) f x := by
  rw [referenceAllModeLowering,map_sum]
  unfold referenceHarmonicLowering
  apply Finset.sum_congr rfl
  intro i _
  rw [normalizedDerivative_graph hF hO hD i _ _
    (referenceWeightedBesselField_graph hO hD g hg L lam (-1) i f G hG x) m]
  rw [referenceWeightedInputField_coordinate]

lemma referenceAllModeRaising_coordinate_one_of_meanZero (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (hmean : ∀ y, sphereMean (ambientSphereL2 G hG y)=0) (x : R3) :
    sphereHarmonicCoordinate hO hD 1
      (referenceAllModeRaising hF hO hD g hg L lam f G hG x) = 0 := by
  have hz : (fun y => sphereHarmonicCoordinate hO hD 0 (ambientSphereL2 G hG y)) =
      (fun _ : R3 => (0 : harmonicSphereSubspace 0)) := by
    funext y
    exact (sphereHarmonicCoordinate_zero_eq_zero_iff hO hD _).mpr (hmean y)
  have hzx : sphereHarmonicCoordinate hO hD 0 (ambientSphereL2 G hG x) = 0 :=
    congrFun hz x
  have hdf : fderiv ℝ
      (fun y => sphereHarmonicCoordinate hO hD 0 (ambientSphereL2 G hG y)) x = 0 := by
    rw [hz]
    exact fderiv_const_apply (0 : harmonicSphereSubspace 0)
  rw [referenceAllModeRaising,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hr := (normalizedRaising_graph hF hO hD i _ _
    (referenceWeightedBesselField_graph hO hD g hg L lam 1 i f G hG x)).2 0
  rw [referenceWeightedInputField_coordinate] at hr
  rw [hr]
  simp [referenceWeightedHarmonicDerivative,referenceHarmonicCovariantDerivative,hdf,hzx]

lemma referenceAllModeRaising_eq_zero (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceAllModeRaising hF hO hD g hg L lam f G hG x = 0 := by
  unfold referenceAllModeRaising
  simp only [referenceWeightedBesselField_eq_zero hO hD g hg L lam 1 _ f G hG K hK hz x hx,
    map_zero,Finset.sum_const_zero]

lemma referenceAllModeLowering_eq_zero (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceAllModeLowering hF hO hD g hg L lam f G hG x = 0 := by
  unfold referenceAllModeLowering
  simp only [referenceWeightedBesselField_eq_zero hO hD g hg L lam (-1) _ f G hG K hK hz x hx,
    map_zero,Finset.sum_const_zero]

lemma hasCompactSupport_referenceAllModeRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (referenceAllModeRaising hF hO hD g hg L lam f G hG) :=
  HasCompactSupport.intro hK
    (fun x hx => referenceAllModeRaising_eq_zero hF hO hD g hg L lam f G hG K hK hz x hx)

lemma hasCompactSupport_referenceAllModeLowering (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (referenceAllModeLowering hF hO hD g hg L lam f G hG) :=
  HasCompactSupport.intro hK
    (fun x hx => referenceAllModeLowering_eq_zero hF hO hD g hg L lam f G hG K hK hz x hx)

lemma integrable_referenceAllModeRaising_norm_sq (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    Integrable (fun x => ReferenceDensityBounds.referenceDensityFamily g L (lam,x) *
      ‖referenceAllModeRaising hF hO hD g hg L lam f G hG x‖^2) :=
  integrable_referenceBase_norm_sq g hg L lam _
    (contDiff_referenceAllModeRaising hF hO hD g hg L lam f hf G hG).continuous
    (hasCompactSupport_referenceAllModeRaising hF hO hD g hg L lam f G hG K hK hz)

lemma integrable_referenceAllModeLowering_norm_sq (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    Integrable (fun x => ReferenceDensityBounds.referenceDensityFamily g L (lam,x) *
      ‖referenceAllModeLowering hF hO hD g hg L lam f G hG x‖^2) :=
  integrable_referenceBase_norm_sq g hg L lam _
    (contDiff_referenceAllModeLowering hF hO hD g hg L lam f hf G hG).continuous
    (hasCompactSupport_referenceAllModeLowering hF hO hD g hg L lam f G hG K hK hz)

theorem tendsto_referenceBaseLift_referenceAllModeRaising
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    let V := referenceAllModeRaising hF hO hD g hg L lam f G hG
    let hV := (contDiff_referenceAllModeRaising hF hO hD g hg L lam f hf G hG).continuous
    let hc := hasCompactSupport_referenceAllModeRaising hF hO hD g hg L lam f G hG K hK hz
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => sphereHarmonicPartialSum hO hD n (V x))
      ((sphereHarmonicPartialSum hO hD n).continuous.comp hV)
      (hc.comp_left (map_zero _))) atTop (𝓝 (referenceBaseLift g hg L lam V hV hc)) :=
  tendsto_referenceBaseLift_sphereHarmonicPartialSum g hg L lam hO hD _
    (contDiff_referenceAllModeRaising hF hO hD g hg L lam f hf G hG).continuous
    (hasCompactSupport_referenceAllModeRaising hF hO hD g hg L lam f G hG K hK hz)

theorem tendsto_referenceBaseLift_referenceAllModeLowering
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    let V := referenceAllModeLowering hF hO hD g hg L lam f G hG
    let hV := (contDiff_referenceAllModeLowering hF hO hD g hg L lam f hf G hG).continuous
    let hc := hasCompactSupport_referenceAllModeLowering hF hO hD g hg L lam f G hG K hK hz
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => sphereHarmonicPartialSum hO hD n (V x))
      ((sphereHarmonicPartialSum hO hD n).continuous.comp hV)
      (hc.comp_left (map_zero _))) atTop (𝓝 (referenceBaseLift g hg L lam V hV hc)) :=
  tendsto_referenceBaseLift_sphereHarmonicPartialSum g hg L lam hO hD _
    (contDiff_referenceAllModeLowering hF hO hD g hg L lam f hf G hG).continuous
    (hasCompactSupport_referenceAllModeLowering hF hO hD g hg L lam f G hG K hK hz)

end OAI.AnisotropicCalderon.AmbientReferenceRaising
