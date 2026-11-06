import Calderon.ActualPhysicalMixedNative
import Calderon.ActualPhysicalPureReferenceCancellation

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualPhysicalMixedReferenceCancellation
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift SmoothSphereFields SmoothAngularApplication
  AmbientAngularShift AmbientReferenceRaising ActualHorizontalNormBridge
  ActualScalarPrincipalAdjoint ActualPhysicalMixedNative ActualPhysicalPureReferenceCancellation
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection
  ConformalDepth RadiusProfile ReferenceDensityBounds

/- Genuine fullQ mixed contraction and exact reference2T allocation.
   All native raising/weighted domains retained. FullP/U/E/F remains separate. -/

def physicalMixedQFrameCoefficient (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (a b : Fin 3) (x : R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, (referenceInverseEntryFamily g L i j (lam,x) + h x i j) *
    referenceCoFrameEntry g L i a (lam,x) * referenceCoFrameEntry g L j b (lam,x)

lemma physicalMixedQFrameCoefficient_decomposition (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (h : MatrixField) (a b : Fin 3) (x : R3) :
    physicalMixedQFrameCoefficient g L lam h a b x =
      (if a = b then 1 else 0) + physicalMixedFrameCoefficient g L lam h a b x := by
  unfold physicalMixedQFrameCoefficient
  simp only [add_mul,Finset.sum_add_distrib]
  rw [referenceInverse_coFrame_contraction g hg L lam x a b]
  rfl

lemma contDiff_physicalMixedQFrameCoefficient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (a b : Fin 3) : ContDiff ℝ ∞ (physicalMixedQFrameCoefficient g L lam h a b) := by
  have he : physicalMixedQFrameCoefficient g L lam h a b =
      fun x => (if a = b then 1 else 0) + physicalMixedFrameCoefficient g L lam h a b x :=
    funext (physicalMixedQFrameCoefficient_decomposition g hg L lam h a b)
  rw [he]
  exact contDiff_const.add (contDiff_physicalMixedFrameCoefficient g hg L lam h hh a b)

def physicalMixedQNativeRaising
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ a : Fin 3, ∑ b : Fin 3, (2 * physicalMixedQFrameCoefficient g L lam h a b x) •
    normalizedRaising hF hO hD a
      (referenceWeightedBesselField hO hD g hg L lam 1 b
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x)

lemma physicalMixedQNative_term_raising_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (a b : Fin 3) (x : R3) :
    (referenceWeightedInputField hO hD g hg L lam 1 b
      (fun y => Real.log (referenceRadius δ R p L y)) G hG x,
      normalizedRaising hF hO hD a
        (referenceWeightedBesselField hO hD g hg L lam 1 b
          (fun y => Real.log (referenceRadius δ R p L y)) G hG x)) ∈ sphereRaisingGraph hF hO hD a := by
  exact normalizedRaising_graph hF hO hD a _ _
    (referenceWeightedBesselField_graph hO hD g hg L lam 1 b
      (fun y => Real.log (referenceRadius δ R p L y)) G hG x)

theorem physicalMixedQNativeRaising_decomposition
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    physicalMixedQNativeRaising hF hO hD g hg L lam δ R p h G hG x =
      (2 : ℝ) • referenceAllModeRaising hF hO hD g hg L lam
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x +
      physicalMixedNativeRaising hF hO hD g hg L lam δ R p h G hG x := by
  unfold physicalMixedQNativeRaising
  simp_rw [physicalMixedQFrameCoefficient_decomposition g hg L lam h]
  simp only [mul_add,add_smul,Finset.sum_add_distrib]
  change (∑ a : Fin 3, ∑ b : Fin 3, (2 * (if a = b then 1 else 0)) •
      normalizedRaising hF hO hD a
        (referenceWeightedBesselField hO hD g hg L lam 1 b
          (fun y => Real.log (referenceRadius δ R p L y)) G hG x)) +
      physicalMixedNativeRaising hF hO hD g hg L lam δ R p h G hG x = _
  congr 1
  simp [referenceAllModeRaising,mul_ite,Finset.smul_sum]

theorem physicalMixedQNativeRaising_component_decomposition
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    physicalMixedQNativeRaising hF hO hD g hg L lam δ R p h G hG x =
      (2 : ℝ) • referenceAllModeRaising hF hO hD g hg L lam
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x +
      (physicalMixedFirstRaising hF hO hD g L lam h G hG x +
        physicalMixedProfileRaising hF hO hD g L lam δ R p h G hG x +
        physicalMixedConnectionRaising hF hO hD g L lam h G hG x) := by
  rw [physicalMixedQNativeRaising_decomposition hF hO hD g hg L lam δ R p h G hG x,
    physicalMixedNativeRaising_decomposition hF hO hD g hg L lam δ R p h G hG x]

lemma contDiff_physicalMixedQNativeRaising
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hδ : 0 < δ) (hR : 0 < R) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (physicalMixedQNativeRaising hF hO hD g hg L lam δ R p h G hG) := by
  have hf := contDiff_log_referenceRadius_profile δ R L p hδ hR
  exact ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
    (contDiff_const.mul (contDiff_physicalMixedQFrameCoefficient g hg L lam h hh a b)).smul
      ((normalizedRaising hF hO hD a).contDiff.comp
        (contDiff_referenceWeightedBesselField hO hD g hg L lam 1 b
          (fun y => Real.log (referenceRadius δ R p L y)) hf G hG))

lemma hasCompactSupport_physicalMixedQNativeRaising
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (physicalMixedQNativeRaising hF hO hD g hg L lam δ R p h G hG) := by
  exact HasCompactSupport.intro hK (by
    intro x hx
    simp only [physicalMixedQNativeRaising,
      referenceWeightedBesselField_eq_zero hO hD g hg L lam 1 _
        (fun y => Real.log (referenceRadius δ R p L y)) G hG K hK hz x hx,
      map_zero,smul_zero,Finset.sum_const_zero])

end OAI.AnisotropicCalderon.ActualPhysicalMixedReferenceCancellation
