import Calderon.BoundedAngularShift
import Calderon.SmoothAngularApplication

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.AmbientAngularShift
open SphereHarmonic SmoothSphereFields SmoothAngularApplication
  SpectralCoreRegularity SpectralWeightedGraph AngularShiftGraph
  BoundedAngularShift WeightedBaseSpectral WeightedAngularConvergence

def ambientDerivativeField (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => normalizedDerivative hF hO hD i
    (ambientBesselField hO hD 1 (by norm_num) G hG x)

def ambientRaisingField (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => normalizedRaising hF hO hD i
    (ambientBesselField hO hD 1 (by norm_num) G hG x)

/-- A_i of the actual smooth probability-sphere field exists, with its full endpoint. -/
lemma ambientDerivativeField_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientSphereL2 G hG x,ambientDerivativeField hF hO hD i G hG x) ∈
      sphereDerivativeGraph hF hO hD i :=
  normalizedDerivative_graph hF hO hD i _ _
    (ambientBesselField_graph hO hD 1 (by norm_num) G hG x)

/-- A_i* of the actual smooth field exists; it also acts on constant input. -/
lemma ambientRaisingField_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientSphereL2 G hG x,ambientRaisingField hF hO hD i G hG x) ∈
      sphereRaisingGraph hF hO hD i :=
  normalizedRaising_graph hF hO hD i _ _
    (ambientBesselField_graph hO hD 1 (by norm_num) G hG x)

lemma contDiff_ambientDerivativeField (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientDerivativeField hF hO hD i G hG) :=
  (normalizedDerivative hF hO hD i).contDiff.comp
    (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG)

lemma contDiff_ambientRaisingField (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientRaisingField hF hO hD i G hG) :=
  (normalizedRaising hF hO hD i).contDiff.comp
    (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG)

lemma ambientDerivativeField_eq_zero (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    ambientDerivativeField hF hO hD i G hG x = 0 := by
  unfold ambientDerivativeField
  rw [ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx,map_zero]

lemma ambientRaisingField_eq_zero (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    ambientRaisingField hF hO hD i G hG x = 0 := by
  unfold ambientRaisingField
  rw [ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx,map_zero]

lemma hasCompactSupport_ambientDerivativeField (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (ambientDerivativeField hF hO hD i G hG) :=
  HasCompactSupport.intro hK
    (fun x hx => ambientDerivativeField_eq_zero hF hO hD i G hG K hz x hx)

lemma hasCompactSupport_ambientRaisingField (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (ambientRaisingField hF hO hD i G hG) :=
  HasCompactSupport.intro hK
    (fun x hx => ambientRaisingField_eq_zero hF hO hD i G hG K hz x hx)

lemma integrable_ambientDerivativeField_norm_sq (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    Integrable (fun x => ReferenceDensityBounds.referenceDensityFamily g L (lam,x) *
      ‖ambientDerivativeField hF hO hD i G hG x‖^2) :=
  integrable_referenceBase_norm_sq g hg L lam _
    (contDiff_ambientDerivativeField hF hO hD i G hG).continuous
    (hasCompactSupport_ambientDerivativeField hF hO hD i G hG K hK hz)

lemma integrable_ambientRaisingField_norm_sq (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    Integrable (fun x => ReferenceDensityBounds.referenceDensityFamily g L (lam,x) *
      ‖ambientRaisingField hF hO hD i G hG x‖^2) :=
  integrable_referenceBase_norm_sq g hg L lam _
    (contDiff_ambientRaisingField hF hO hD i G hG).continuous
    (hasCompactSupport_ambientRaisingField hF hO hD i G hG K hK hz)

lemma ambientDerivativeField_partialSum_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (n : ℕ) (x : R3) :
    (sphereHarmonicPartialSum hO hD (n+1) (ambientSphereL2 G hG x),
      sphereHarmonicPartialSum hO hD n (ambientDerivativeField hF hO hD i G hG x)) ∈
        sphereDerivativeGraph hF hO hD i :=
  sphereDerivativeGraph_partialSum hF hO hD i _ _
    (ambientDerivativeField_graph hF hO hD i G hG x) n

lemma ambientRaisingField_partialSum_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (n : ℕ) (x : R3) :
    (sphereHarmonicPartialSum hO hD n (ambientSphereL2 G hG x),
      sphereHarmonicPartialSum hO hD (n+1) (ambientRaisingField hF hO hD i G hG x)) ∈
        sphereRaisingGraph hF hO hD i :=
  sphereRaisingGraph_partialSum hF hO hD i _ _
    (ambientRaisingField_graph hF hO hD i G hG x) n

theorem tendsto_referenceBaseLift_ambientDerivativeField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    let V := ambientDerivativeField hF hO hD i G hG
    let hV := (contDiff_ambientDerivativeField hF hO hD i G hG).continuous
    let hc := hasCompactSupport_ambientDerivativeField hF hO hD i G hG K hK hz
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => sphereHarmonicPartialSum hO hD n (V x))
      ((sphereHarmonicPartialSum hO hD n).continuous.comp hV)
      (hc.comp_left (map_zero _))) atTop (𝓝 (referenceBaseLift g hg L lam V hV hc)) :=
  tendsto_referenceBaseLift_sphereHarmonicPartialSum g hg L lam hO hD _
    (contDiff_ambientDerivativeField hF hO hD i G hG).continuous
    (hasCompactSupport_ambientDerivativeField hF hO hD i G hG K hK hz)

theorem tendsto_referenceBaseLift_ambientRaisingField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    let V := ambientRaisingField hF hO hD i G hG
    let hV := (contDiff_ambientRaisingField hF hO hD i G hG).continuous
    let hc := hasCompactSupport_ambientRaisingField hF hO hD i G hG K hK hz
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => sphereHarmonicPartialSum hO hD n (V x))
      ((sphereHarmonicPartialSum hO hD n).continuous.comp hV)
      (hc.comp_left (map_zero _))) atTop (𝓝 (referenceBaseLift g hg L lam V hV hc)) :=
  tendsto_referenceBaseLift_sphereHarmonicPartialSum g hg L lam hO hD _
    (contDiff_ambientRaisingField hF hO hD i G hG).continuous
    (hasCompactSupport_ambientRaisingField hF hO hD i G hG K hK hz)

end OAI.AnisotropicCalderon.AmbientAngularShift
