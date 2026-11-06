import Calderon.ActualReferenceParallelRaising
import Calderon.ActualPhysicalMixedProfile

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualReferenceScaledRaisingTransport
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift HarmonicDerivativeOperator SmoothSphereFields
  SmoothAngularApplication AmbientAngularShift AmbientReferenceRaising SmoothMetricFrame
  MovingFrameConnection ActualPhysicalPureAngular ActualPhysicalMixedProfile
  ActualReferenceParallelRaising ActualUnboundedFirstPrincipalFormBound
  ReferenceDensityBounds PrincipalCommutator ConformalDepth RadiusProfile

/- Genuine native D_i+(r^-1 A_a*) transport with actual covector index.
   All modes, scalar/radius/angular/base graph domains and density support paid.
   Source-only author candidate; no fullphysicalU/J/E/F/H identification. -/

lemma inverse_referenceRadius_eq_exp_neg_log (δ R L : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
    (referenceRadius δ R p L x)⁻¹ = Real.exp (-Real.log (referenceRadius δ R p L x)) := by
  rw [Real.exp_neg,Real.exp_log (referenceRadius_pos δ R p L x hδ hR)]

lemma contDiff_inverse_referenceRadius (δ R L : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (fun x => (referenceRadius δ R p L x)⁻¹) := by
  have he : (fun x => (referenceRadius δ R p L x)⁻¹) =
      (fun x => Real.exp (-Real.log (referenceRadius δ R p L x))) :=
    funext (inverse_referenceRadius_eq_exp_neg_log δ R L p hδ hR)
  rw [he]
  exact Real.contDiff_exp.comp (contDiff_log_referenceRadius_profile δ R L p hδ hR).neg

lemma directionalFDeriv_inverse_referenceRadius (δ R L : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (x X : R3) :
    directionalFDeriv X (fun y => (referenceRadius δ R p L y)⁻¹) x =
      -(referenceRadius δ R p L x)⁻¹ *
        directionalFDeriv X (fun y => Real.log (referenceRadius δ R p L y)) x := by
  have he : (fun y => (referenceRadius δ R p L y)⁻¹) =
      (fun y => Real.exp (-Real.log (referenceRadius δ R p L y))) :=
    funext (inverse_referenceRadius_eq_exp_neg_log δ R L p hδ hR)
  have hf := ((contDiff_log_referenceRadius_profile δ R L p hδ hR).differentiable (by simp) x).hasFDerivAt
  have hexp : HasFDerivAt (fun y => Real.exp (-Real.log (referenceRadius δ R p L y)))
      (Real.exp (-Real.log (referenceRadius δ R p L x)) •
        (-fderiv ℝ (fun y => Real.log (referenceRadius δ R p L y)) x)) x := by
    simpa only [Pi.neg_apply] using hf.neg.exp
  unfold directionalFDeriv
  rw [he,hexp.fderiv]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.neg_apply,smul_eq_mul]
  rw [← inverse_referenceRadius_eq_exp_neg_log δ R L p hδ hR x]
  ring

def ambientDegreeRaisingField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => ambientRaisingBesselField hF hO hD a G hG x - ambientRaisingField hF hO hD a G hG x

lemma ambientDegreeRaisingField_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientRaisingField hF hO hD a G hG x,ambientDegreeRaisingField hF hO hD a G hG x) ∈
      spectralGraph hO hD (fun k => (k : ℝ)) := by
  intro k
  change sphereHarmonicCoordinate hO hD k (ambientDegreeRaisingField hF hO hD a G hG x) =
    (k : ℝ) • sphereHarmonicCoordinate hO hD k (ambientRaisingField hF hO hD a G hG x)
  rw [ambientDegreeRaisingField,map_sub,ambientRaisingBesselField_graph hF hO hD a G hG x k]
  simp only [besselWeight,Real.rpow_one]
  module

theorem ambientDegreeRaisingField_commutator
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ambientDegreeRaisingField hF hO hD a G hG x - ambientMixedRaisingDegreeField hF hO hD a G hG x =
      ambientRaisingField hF hO hD a G hG x := by
  have hBA := ambientDegreeRaisingField_graph hF hO hD a G hG x
  have hAB := ambientMixedRaisingDegreeField_graph hF hO hD a G hG x
  have hA := ambientRaisingField_graph hF hO hD a G hG x
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k
      (ambientDegreeRaisingField hF hO hD a G hG x - ambientMixedRaisingDegreeField hF hO hD a G hG x) =
    sphereHarmonicCoordinate hO hD k (ambientRaisingField hF hO hD a G hG x)
  rw [map_sub,hBA k]
  cases k with
  | zero => rw [hAB.1,hA.1]; simp only [smul_zero,sub_zero]
  | succ m =>
    rw [hAB.2 m,ambientDegreeField_coordinate hO hD G hG m x,map_smul]
    simp_rw [hA.2 m]
    simp only [Nat.cast_add,Nat.cast_one]
    module

lemma contDiff_ambientDegreeRaisingField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientDegreeRaisingField hF hO hD a G hG) := by
  exact (contDiff_ambientRaisingBesselField hF hO hD a G hG).sub
    (contDiff_ambientRaisingField hF hO hD a G hG)

def inverseRadiusRaisingField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (δ R L : ℝ) (p : ℕ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => (referenceRadius δ R p L x)⁻¹ • ambientRaisingField hF hO hD a G hG x

lemma inverseRadiusRaisingField_besselGraph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (δ R L : ℝ) (p : ℕ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (inverseRadiusRaisingField hF hO hD δ R L p a G hG x,
      (referenceRadius δ R p L x)⁻¹ • ambientRaisingBesselField hF hO hD a G hG x) ∈
      sphereBesselGraph hO hD 1 := by
  exact (sphereBesselGraph hO hD 1).smul_mem (referenceRadius δ R p L x)⁻¹
    (ambientRaisingBesselField_graph hF hO hD a G hG x)

lemma inverseRadiusRaisingField_degreeGraph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (δ R L : ℝ) (p : ℕ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (inverseRadiusRaisingField hF hO hD δ R L p a G hG x,
      (referenceRadius δ R p L x)⁻¹ • ambientDegreeRaisingField hF hO hD a G hG x) ∈
      spectralGraph hO hD (fun k => (k : ℝ)) := by
  exact (spectralGraph hO hD (fun k => (k : ℝ))).smul_mem (referenceRadius δ R p L x)⁻¹
    (ambientDegreeRaisingField_graph hF hO hD a G hG x)

lemma inverseRadiusRaisingField_angularConnectionGraph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    (inverseRadiusRaisingField hF hO hD δ R L p a G hG x,
      normalizedReferenceAngularConnection hO hD g L lam x X
        ((referenceRadius δ R p L x)⁻¹ • ambientRaisingBesselField hF hO hD a G hG x)) ∈
      referenceAngularConnectionGraph hO hD g L lam x X := by
  exact normalizedReferenceAngularConnection_graph hO hD g L lam x X _ _
    (inverseRadiusRaisingField_besselGraph hF hO hD δ R L p a G hG x)

def inverseRadiusRaisingCovectorDerivative
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) : SphereL2 :=
  directionalFDeriv X (inverseRadiusRaisingField hF hO hD δ R L p a G hG) x +
    normalizedReferenceAngularConnection hO hD g L lam x X
      ((referenceRadius δ R p L x)⁻¹ • ambientRaisingBesselField hF hO hD a G hG x) -
    ∑ b : Fin 3, referenceFrameConnectionCoefficient g L lam x X b a •
      inverseRadiusRaisingField hF hO hD δ R L p b G hG x

lemma inverseRadiusRaisingCovectorDerivative_expansion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    inverseRadiusRaisingCovectorDerivative hF hO hD g L lam δ R p a G hG x X =
      directionalFDeriv X (fun y => (referenceRadius δ R p L y)⁻¹) x •
        ambientRaisingField hF hO hD a G hG x +
      (referenceRadius δ R p L x)⁻¹ • ambientRaisingCovectorDerivative hF hO hD g L lam a G hG x X := by
  unfold inverseRadiusRaisingCovectorDerivative inverseRadiusRaisingField
  rw [directionalFDeriv_smul X (fun y => (referenceRadius δ R p L y)⁻¹)
    (ambientRaisingField hF hO hD a G hG)
    (contDiff_inverse_referenceRadius δ R L p hδ hR)
    (contDiff_ambientRaisingField hF hO hD a G hG) x,map_smul]
  unfold ambientRaisingCovectorDerivative ambientReferenceAngularConnectionRaising
  simp only [smul_add,smul_sub,Fin.sum_univ_three,smul_smul]
  module

def weightedInverseRadiusRaisingCovectorDerivative
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) : SphereL2 :=
  inverseRadiusRaisingCovectorDerivative hF hO hD g L lam δ R p a G hG x X +
    directionalFDeriv X (fun y => Real.log (referenceRadius δ R p L y)) x •
      ((referenceRadius δ R p L x)⁻¹ • ambientDegreeRaisingField hF hO hD a G hG x)

theorem weightedInverseRadiusRaisingCovectorDerivative_eq
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    weightedInverseRadiusRaisingCovectorDerivative hF hO hD g L lam δ R p a G hG x X =
      (referenceRadius δ R p L x)⁻¹ • normalizedRaising hF hO hD a
        (directionalFDeriv X (ambientBesselField hO hD 1 (by norm_num) G hG) x +
          ambientReferenceAngularConnectionBessel hO hD g L lam G hG x X +
          directionalFDeriv X (fun y => Real.log (referenceRadius δ R p L y)) x •
            ambientMixedDegreeBesselField hO hD G hG x) := by
  unfold weightedInverseRadiusRaisingCovectorDerivative
  rw [inverseRadiusRaisingCovectorDerivative_expansion hF hO hD g L lam δ R p hδ hR a G hG x X,
    directionalFDeriv_inverse_referenceRadius δ R L p hδ hR x X,
    ambientRaisingCovectorDerivative_eq_normalizedRaising hF hO hD g hg L lam a G hG x X]
  have hc := ambientDegreeRaisingField_commutator hF hO hD a G hG x
  have hBA : ambientDegreeRaisingField hF hO hD a G hG x =
      ambientRaisingField hF hO hD a G hG x + ambientMixedRaisingDegreeField hF hO hD a G hG x :=
    sub_eq_iff_eq_add.mp hc
  rw [hBA]
  unfold ambientMixedRaisingDegreeField
  simp only [map_add,map_smul,smul_add,smul_smul]
  module

theorem referenceWeighted_inverseRadiusRaising_transport
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (i a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    weightedInverseRadiusRaisingCovectorDerivative hF hO hD g L lam δ R p a G hG x
      (referenceMetricGramFrame g L (lam,x) i) =
      (referenceRadius δ R p L x)⁻¹ • normalizedRaising hF hO hD a
        (referenceWeightedBesselField hO hD g hg L lam 1 i
          (fun y => Real.log (referenceRadius δ R p L y)) G hG x) := by
  rw [weightedInverseRadiusRaisingCovectorDerivative_eq hF hO hD g hg L lam δ R p hδ hR a G hG x
    (referenceMetricGramFrame g L (lam,x) i)]
  unfold referenceWeightedBesselField
  rw [one_smul,referenceHorizontalBesselField_eq_base_add_angularConnection hO hD g hg L lam i G hG x]
  rfl

theorem referenceWeighted_inverseRadiusRaising_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (i a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ((referenceRadius δ R p L x)⁻¹ • referenceWeightedInputField hO hD g hg L lam 1 i
      (fun y => Real.log (referenceRadius δ R p L y)) G hG x,
      weightedInverseRadiusRaisingCovectorDerivative hF hO hD g L lam δ R p a G hG x
        (referenceMetricGramFrame g L (lam,x) i)) ∈ sphereRaisingGraph hF hO hD a := by
  rw [referenceWeighted_inverseRadiusRaising_transport hF hO hD g hg L lam δ R p hδ hR i a G hG x]
  exact (sphereRaisingGraph hF hO hD a).smul_mem (referenceRadius δ R p L x)⁻¹
    (normalizedRaising_graph hF hO hD a _ _
      (referenceWeightedBesselField_graph hO hD g hg L lam 1 i
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x))

lemma contDiff_inverseRadiusRaisingField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (δ R L : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (inverseRadiusRaisingField hF hO hD δ R L p a G hG) := by
  exact (contDiff_inverse_referenceRadius δ R L p hδ hR).smul
    (contDiff_ambientRaisingField hF hO hD a G hG)

lemma contDiff_referenceWeighted_inverseRadiusRaising
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (i a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun x => weightedInverseRadiusRaisingCovectorDerivative hF hO hD g L lam δ R p a G hG x
      (referenceMetricGramFrame g L (lam,x) i)) := by
  have he : (fun x => weightedInverseRadiusRaisingCovectorDerivative hF hO hD g L lam δ R p a G hG x
      (referenceMetricGramFrame g L (lam,x) i)) =
      fun x => (referenceRadius δ R p L x)⁻¹ • normalizedRaising hF hO hD a
        (referenceWeightedBesselField hO hD g hg L lam 1 i
          (fun y => Real.log (referenceRadius δ R p L y)) G hG x) :=
    funext (referenceWeighted_inverseRadiusRaising_transport hF hO hD g hg L lam δ R p hδ hR i a G hG)
  rw [he]
  exact (contDiff_inverse_referenceRadius δ R L p hδ hR).smul
    ((normalizedRaising hF hO hD a).contDiff.comp
      (contDiff_referenceWeightedBesselField hO hD g hg L lam 1 i
        (fun y => Real.log (referenceRadius δ R p L y))
        (contDiff_log_referenceRadius_profile δ R L p hδ hR) G hG))

lemma hasCompactSupport_inverseRadiusRaisingField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (δ R L : ℝ) (p : ℕ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (inverseRadiusRaisingField hF hO hD δ R L p a G hG) := by
  exact HasCompactSupport.intro hK (by
    intro x hx
    rw [inverseRadiusRaisingField,ambientRaisingField_eq_zero hF hO hD a G hG K hz x hx,smul_zero])

lemma hasCompactSupport_referenceWeighted_inverseRadiusRaising
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (i a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (fun x => weightedInverseRadiusRaisingCovectorDerivative hF hO hD g L lam δ R p a G hG x
      (referenceMetricGramFrame g L (lam,x) i)) := by
  exact HasCompactSupport.intro hK (by
    intro x hx
    rw [referenceWeighted_inverseRadiusRaising_transport hF hO hD g hg L lam δ R p hδ hR i a G hG x,
      referenceWeightedBesselField_eq_zero hO hD g hg L lam 1 i
        (fun y => Real.log (referenceRadius δ R p L y)) G hG K hK hz x hx,map_zero,smul_zero])

lemma integrable_referenceWeighted_inverseRadiusRaising_density_pair
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (i a : Fin 3) (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K : Set R3) (hK : IsCompact K) (hzH : ∀ x ∉ K, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪weightedInverseRadiusRaisingCovectorDerivative hF hO hD g L lam δ R p a G hG x
        (referenceMetricGramFrame g L (lam,x) i),ambientSphereL2 H hH x⟫_ℝ) := by
  exact integrable_density_pair_of_contDiff g hg L lam _ (ambientSphereL2 H hH)
    (contDiff_referenceWeighted_inverseRadiusRaising hF hO hD g hg L lam δ R p hδ hR i a G hG)
    (contDiff_ambientSphereL2 H hH) (hasCompactSupport_ambientSphereL2 H hH K hK hzH)

end OAI.AnisotropicCalderon.ActualReferenceScaledRaisingTransport
