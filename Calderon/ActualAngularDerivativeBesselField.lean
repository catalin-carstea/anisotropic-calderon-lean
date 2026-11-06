import Calderon.AmbientAngularShift

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.AngularDerivativeBesselField
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift HarmonicDerivativeOperator
  SmoothSphereFields SmoothAngularApplication AmbientAngularShift

lemma inverseDegreeWeight_second_difference (m : ℕ) :
    inverseDegreeWeight (m+1) * (besselWeight 2 (m+1)-besselWeight 1 (m+1)) =
      besselWeight 1 m := by
  simp only [inverseDegreeWeight,besselWeight,Real.rpow_two,Real.rpow_one]
  push_cast
  field_simp
  ring

/-- Actual W1 A_i u, including the degree-one-to-constant endpoint. -/
def ambientDerivativeBesselField (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => normalizedDerivative hF hO hD i
    (ambientBesselField hO hD 2 (by norm_num) G hG x-
      ambientBesselField hO hD 1 (by norm_num) G hG x)

lemma ambientDerivativeBesselField_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientDerivativeField hF hO hD i G hG x,
      ambientDerivativeBesselField hF hO hD i G hG x) ∈ sphereBesselGraph hO hD 1 := by
  intro m
  change sphereHarmonicCoordinate hO hD m
      (normalizedDerivativeOutput hF hO hD i
        (ambientBesselField hO hD 2 (by norm_num) G hG x-
          ambientBesselField hO hD 1 (by norm_num) G hG x)) = _
  rw [normalizedDerivativeOutput_graph hF hO hD i _ m,
    inverseDegreeMultiplier_coordinate,map_sub,
    ambientBesselField_graph hO hD 2 (by norm_num) G hG x (m+1),
    ambientBesselField_graph hO hD 1 (by norm_num) G hG x (m+1)]
  simp only [Prod.fst]
  rw [← sub_smul (besselWeight 2 (m+1)) (besselWeight 1 (m+1))
    (sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG x)),smul_smul,map_smul,inverseDegreeWeight_second_difference,
    ambientDerivativeField_graph hF hO hD i G hG x m]

lemma contDiff_ambientDerivativeBesselField (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientDerivativeBesselField hF hO hD i G hG) :=
  (normalizedDerivative hF hO hD i).contDiff.comp
    ((contDiff_ambientBesselField hO hD 2 (by norm_num) G hG).sub
      (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG))

lemma ambientDerivativeBesselField_eq_zero (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    ambientDerivativeBesselField hF hO hD i G hG x = 0 := by
  simp only [ambientDerivativeBesselField,
    ambientBesselField_eq_zero hO hD 2 (by norm_num) G hG K hz x hx,
    ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx,sub_self,map_zero]

end OAI.AnisotropicCalderon.AngularDerivativeBesselField
