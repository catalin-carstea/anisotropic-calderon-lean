import Calderon.SmoothAmbientAngularCasimir
import Calderon.WeightedAngularConvergence

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.SmoothAngularApplication
open SphereHarmonic SmoothSphereFields SmoothAmbientAngularCasimir
  SpectralCoreRegularity SpectralWeightedGraph SpectralWeightComparison
  BoundedSpectralMultiplier WeightedBaseSpectral WeightedAngularConvergence

def ambientShiftedCasimirField (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  ambientSphereL2 (ambientShiftedAngularCasimirIterate 1 G)
    (contDiff_ambientShiftedAngularCasimirIterate 1 G hG)

def ambientBesselField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (hs : s ≤ 2) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => casimirBesselMultiplier hO hD s hs (ambientShiftedCasimirField G hG x)

theorem ambientShiftedCasimirField_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientSphereL2 G hG x,ambientShiftedCasimirField G hG x) ∈
      spectralGraph hO hD casimirWeight := by
  intro k
  simpa only [ambientShiftedCasimirField,pow_one,casimirWeight] using
    sphereHarmonicCoordinate_angularCasimirLift hO hD 1 k G hG x

theorem ambientBesselField_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientSphereL2 G hG x,ambientBesselField hO hD s hs G hG x) ∈
      sphereBesselGraph hO hD s :=
  casimirBesselMultiplier_graph hO hD s hs _ _ (ambientShiftedCasimirField_graph hO hD G hG x)

lemma contDiff_ambientBesselField (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientBesselField hO hD s hs G hG) :=
  contDiff_casimirBesselMultiplier hO hD s hs _ (contDiff_angularCasimirLift 1 G hG)

lemma ambientBesselField_eq_zero (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) (x : R3) (hx : x ∉ K) :
    ambientBesselField hO hD s hs G hG x = 0 := by
  have he : ambientShiftedCasimirField G hG x = 0 :=
    ambientSphereL2_eq_zero _ (contDiff_ambientShiftedAngularCasimirIterate 1 G hG) x
      (ambientShiftedAngularCasimirIterate_sphere_zero 1 G hG K hz x hx)
  change casimirBesselMultiplier hO hD s hs (ambientShiftedCasimirField G hG x) = 0
  rw [he,map_zero]

lemma hasCompactSupport_ambientBesselField (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) :
    HasCompactSupport (ambientBesselField hO hD s hs G hG) :=
  hasCompactSupport_casimirBesselMultiplier hO hD s hs _
    (hasCompactSupport_angularCasimirLift 1 G hG K hK hz)

lemma tsupport_ambientBesselField_subset (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) :
    tsupport (ambientBesselField hO hD s hs G hG) ⊆ K := by
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hxK
  change ambientBesselField hO hD s hs G hG x ≠ 0 at hx
  exact hx (ambientBesselField_eq_zero hO hD s hs G hG K hz x hxK)

lemma tsupport_pureDerivative_ambientBesselField_subset (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) (X : R3) :
    tsupport (fun x => fderiv ℝ (ambientBesselField hO hD s hs G hG) x X) ⊆ K :=
  (tsupport_fderiv_apply_subset ℝ X).trans
    (tsupport_ambientBesselField_subset hO hD s hs G hG K hK hz)

lemma tsupport_secondPureDerivative_ambientBesselField_subset (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) (X Y : R3) :
    tsupport (fun x => fderiv ℝ (fun y => fderiv ℝ (ambientBesselField hO hD s hs G hG) y X) x Y) ⊆ K :=
  (tsupport_fderiv_apply_subset ℝ Y).trans
    (tsupport_pureDerivative_ambientBesselField_subset hO hD s hs G hG K hK hz X)

lemma fderiv_ambientBesselField (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    fderiv ℝ (ambientBesselField hO hD s hs G hG) x =
      (casimirBesselMultiplier hO hD s hs).comp (fderiv ℝ (ambientShiftedCasimirField G hG) x) :=
  fderiv_casimirBesselMultiplier hO hD s hs _ x
    ((contDiff_angularCasimirLift 1 G hG).differentiable (by simp) x)

lemma memLp_ambientBesselField (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) :
    MemLp (ambientBesselField hO hD s hs G hG) 2 (referenceBaseMeasure g L lam) :=
  memLp_referenceBase g hg L lam _ (contDiff_ambientBesselField hO hD s hs G hG).continuous
    (hasCompactSupport_ambientBesselField hO hD s hs G hG K hK hz)

theorem ambientBesselField_partialSum_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (n : ℕ) (x : R3) :
    (sphereHarmonicPartialSum hO hD n (ambientSphereL2 G hG x),
      sphereHarmonicPartialSum hO hD n (ambientBesselField hO hD s hs G hG x)) ∈
        sphereBesselGraph hO hD s :=
  casimirBesselMultiplier_partialSum_graph hO hD s hs n _ _
    (ambientShiftedCasimirField_graph hO hD G hG x)

theorem tendsto_referenceBaseLift_ambientBesselField
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) :
    let W := ambientBesselField hO hD s hs G hG
    let hW := (contDiff_ambientBesselField hO hD s hs G hG).continuous
    let hcomp := hasCompactSupport_ambientBesselField hO hD s hs G hG K hK hz
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => sphereHarmonicPartialSum hO hD n (W x))
      ((sphereHarmonicPartialSum hO hD n).continuous.comp hW)
      (hcomp.comp_left (map_zero _))) atTop
      (𝓝 (referenceBaseLift g hg L lam W hW hcomp)) :=
  tendsto_referenceBaseLift_sphereHarmonicPartialSum g hg L lam hO hD _
    (contDiff_ambientBesselField hO hD s hs G hG).continuous
    (hasCompactSupport_ambientBesselField hO hD s hs G hG K hK hz)

theorem tendsto_referenceBaseLift_pureDerivative_ambientBesselField
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) (X : R3) :
    let W := ambientBesselField hO hD s hs G hG
    let hW := contDiff_ambientBesselField hO hD s hs G hG
    let hcomp := hasCompactSupport_ambientBesselField hO hD s hs G hG K hK hz
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => sphereHarmonicPartialSum hO hD n (fderiv ℝ W x X))
      ((sphereHarmonicPartialSum hO hD n).continuous.comp (continuous_pureDerivative W hW X))
      ((hasCompactSupport_pureDerivative W hcomp X).comp_left (map_zero _))) atTop
      (𝓝 (referenceBaseLift g hg L lam (fun x => fderiv ℝ W x X)
        (continuous_pureDerivative W hW X) (hasCompactSupport_pureDerivative W hcomp X))) :=
  tendsto_referenceBaseLift_pureDerivative_full g hg L lam hO hD _
    (contDiff_ambientBesselField hO hD s hs G hG)
    (hasCompactSupport_ambientBesselField hO hD s hs G hG K hK hz) X

theorem tendsto_referenceBaseLift_secondPureDerivative_ambientBesselField
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) (X Y : R3) :
    let W := ambientBesselField hO hD s hs G hG
    let hW := contDiff_ambientBesselField hO hD s hs G hG
    let hcomp := hasCompactSupport_ambientBesselField hO hD s hs G hG K hK hz
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => sphereHarmonicPartialSum hO hD n (fderiv ℝ (fun y => fderiv ℝ W y X) x Y))
      ((sphereHarmonicPartialSum hO hD n).continuous.comp
        (continuous_pureDerivative _ (contDiff_pureDerivative W hW X) Y))
      ((hasCompactSupport_pureDerivative _ (hasCompactSupport_pureDerivative W hcomp X) Y).comp_left
        (map_zero _))) atTop
      (𝓝 (referenceBaseLift g hg L lam (fun x => fderiv ℝ (fun y => fderiv ℝ W y X) x Y)
        (continuous_pureDerivative _ (contDiff_pureDerivative W hW X) Y)
        (hasCompactSupport_pureDerivative _ (hasCompactSupport_pureDerivative W hcomp X) Y))) :=
  tendsto_referenceBaseLift_secondPureDerivative_full g hg L lam hO hD _
    (contDiff_ambientBesselField hO hD s hs G hG)
    (hasCompactSupport_ambientBesselField hO hD s hs G hG K hK hz) X Y

end OAI.AnisotropicCalderon.SmoothAngularApplication
