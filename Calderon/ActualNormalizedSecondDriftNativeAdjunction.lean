import Calderon.ActualNormalizedSecondDriftAngularAllocation
import Calderon.ActualReferenceConnectionAngular
import Calderon.BaseDensityAdjoint
import Calderon.ActualUnboundedFirstPrincipalFormBound

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondDriftNativeAdjunction
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift BoundedSpectralMultiplier SmoothSphereFields SmoothAngularApplication
  AmbientAngularShift AmbientReferenceRaising SmoothMetricFrame MovingFrameConnection
  ActualReferenceParallelRaising ActualNormalizedSphereRotation ActualReferenceScaledRaisingTransport
  ActualReferenceModelTrace ActualReferenceDecomposition ActualReferenceOrdinaryPrincipal
  ActualNormalizedSecondMetricDrift ActualNormalizedSecondDriftAngularAllocation
  ReferenceDensityBounds PrincipalCommutator ConformalDepth RadiusProfile ActualScalarPrincipalAdjoint
  ActualUnboundedFirstPrincipalFormBound

/- Actual native second-metric drift only.
   No complete E/F/U/H identity or bounded raw angular-arrow assumption. -/

def normalizedSecondDriftDensityDivergence (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) : R3 → ℝ :=
  fun x => (referenceDensityFamily g1 L (lam,x))⁻¹ * ∑ j : Fin 3,
  directionalFDeriv (coordinateDirection j)
    (fun y => referenceDensityFamily g1 L (lam,y) * referenceRadius δ R p L y *
      normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) x

def normalizedSecondDriftFirstAdjointField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => -(referenceDensityFamily g1 L (lam,x))⁻¹ • ∑ j : Fin 3,
  directionalFDeriv (coordinateDirection j)
    (fun y => (referenceDensityFamily g1 L (lam,y) * referenceRadius δ R p L y *
      normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) • ambientSphereL2 G hG y) x

def normalizedSecondDriftAngularConnectionField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => referenceRadius δ R p L x • ∑ a : Fin 3,
  normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
    normalizedReferenceAngularConnection hO hD g1 L lam x (referenceMetricGramFrame g1 L (lam,x) a)
      (ambientBesselField hO hD 1 (by norm_num) G hG x)

def normalizedSecondDriftDegreeField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => referenceRadius δ R p L x • ∑ a : Fin 3,
  (normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) *
    referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)) x) •
      ambientDegreeField hO hD G hG x

def normalizedSecondWeightedDriftAdjointField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => normalizedSecondDriftFirstAdjointField hO hD g1 g2 hg1 L lam δ R p G hG x - normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p G hG x + normalizedSecondDriftDegreeField hO hD g1 g2 hg1 L lam δ R p G hG x

def normalizedSecondWeightedDriftAdjointDefect (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => normalizedSecondWeightedDriftAdjointField hO hD g1 g2 hg1 L lam δ R p G hG x - normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG x

lemma normalizedReferenceAngularConnection_bessel_inner_skew (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (x X : R3) (u U v V : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD 1)
    (hV : (v,V) ∈ sphereBesselGraph hO hD 1) :
  ⟪normalizedReferenceAngularConnection hO hD g L lam x X U,v⟫_ℝ =
    -⟪u,normalizedReferenceAngularConnection hO hD g L lam x X V⟫_ℝ := by
  have hs (i j : Fin 3) :
      ⟪normalizedRotation hO hD i j U,v⟫_ℝ = -⟪u,normalizedRotation hO hD i j V⟫_ℝ :=
    sphereRotationGraph_inner_skew hO hD i j u _ v _
      (normalizedRotation_graph hO hD i j u U hU)
      (normalizedRotation_graph hO hD i j v V hV)
  unfold normalizedReferenceAngularConnection
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum]
  simp_rw [hs, mul_neg]
  simp only [Finset.sum_neg_distrib, mul_neg]

lemma ambientDegreeField_inner_symm (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
  ⟪ambientDegreeField hO hD G hG x,ambientSphereL2 H hH x⟫_ℝ =
    ⟪ambientSphereL2 G hG x,ambientDegreeField hO hD H hH x⟫_ℝ := by
  exact spectralGraph_inner_symm hO hD (fun k => (k : ℝ))
    (ambientSphereL2 G hG x) (ambientDegreeField hO hD G hG x)
    (ambientSphereL2 H hH x) (ambientDegreeField hO hD H hH x)
    (fun k => ambientDegreeField_coordinate hO hD G hG k x)
    (fun k => ambientDegreeField_coordinate hO hD H hH k x)

theorem normalizedSecondWeightedDriftField_base_angular_degree_split (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
  normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG x = normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x + normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p G hG x + normalizedSecondDriftDegreeField hO hD g1 g2 hg1 L lam δ R p G hG x := by
  rw [normalizedSecondWeightedDriftField_ordinary_split hO hD g1 g2 hg1 L lam δ R p G hG x]
  unfold normalizedSecondDriftZeroBaseField normalizedSecondDriftAngularConnectionField
    normalizedSecondDriftDegreeField referenceWeightedZeroBaseField ambientDegreeField
  simp only [smul_add, Finset.sum_add_distrib, smul_smul]
  module

theorem normalizedSecondDriftFirstAdjointField_expansion (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
  normalizedSecondDriftFirstAdjointField hO hD g1 g2 hg1 L lam δ R p G hG x = -(normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x) -
    normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p x • ambientSphereL2 G hG x := by
  have hm : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g1 L (lam,x)) :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have hb (j : Fin 3) : ContDiff ℝ ∞
      (fun x : R3 => normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)) :=
    (contDiff_normalizedSecondDriftCoordinateJoint g1 g2 hg1 hg2 L j).comp
      (contDiff_const.prodMk contDiff_id)
  let c (j : Fin 3) (y : R3) : ℝ := referenceDensityFamily g1 L (lam,y) *
    referenceRadius δ R p L y * normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)
  have hc (j : Fin 3) : ContDiff ℝ ∞ (c j) := (hm.mul hr).mul (hb j)
  have hprod (j : Fin 3) :
      directionalFDeriv (coordinateDirection j) (fun y => c j y • ambientSphereL2 G hG y) x =
      directionalFDeriv (coordinateDirection j) (c j) x • ambientSphereL2 G hG x +
        c j x • directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x := by
    simpa only [BaseDensityAdjoint.directionalDeriv, directionalFDeriv] using
      BaseDensityAdjoint.directionalDeriv_smul (coordinateDirection j) (c j)
        (ambientSphereL2 G hG) (hc j) (contDiff_ambientSphereL2 G hG) x
  have hfirst : (∑ j : Fin 3, c j x •
      directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x) =
      referenceDensityFamily g1 L (lam,x) •
        normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x := by
    unfold normalizedSecondDriftFirstBaseField
    simp only [Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    dsimp [c]
    ring
  have hmu : referenceDensityFamily g1 L (lam,x) ≠ 0 :=
    (referenceDensityFamily_pos g1 hg1 L (lam,x)).ne'
  change -(referenceDensityFamily g1 L (lam,x))⁻¹ •
      (∑ j : Fin 3, directionalFDeriv (coordinateDirection j)
        (fun y => c j y • ambientSphereL2 G hG y) x) = _
  simp_rw [hprod]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, hfirst]
  simp only [smul_add, smul_smul, neg_mul]
  rw [inv_mul_cancel₀ hmu]
  simp only [one_smul, neg_smul]
  unfold normalizedSecondDriftDensityDivergence
  change _ = -normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x -
    ((referenceDensityFamily g1 L (lam,x))⁻¹ *
      ∑ j : Fin 3, directionalFDeriv (coordinateDirection j) (c j) x) • ambientSphereL2 G hG x
  module

lemma normalizedSecondDriftAngularConnectionField_inner_skew (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
  ⟪normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 H hH x⟫_ℝ =
    -⟪ambientSphereL2 G hG x,
      normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p H hH x⟫_ℝ := by
  have hs (a : Fin 3) := normalizedReferenceAngularConnection_bessel_inner_skew hO hD
    g1 L lam x (referenceMetricGramFrame g1 L (lam,x) a)
    (ambientSphereL2 G hG x) (ambientBesselField hO hD 1 (by norm_num) G hG x)
    (ambientSphereL2 H hH x) (ambientBesselField hO hD 1 (by norm_num) H hH x)
    (ambientBesselField_graph hO hD 1 (by norm_num) G hG x)
    (ambientBesselField_graph hO hD 1 (by norm_num) H hH x)
  unfold normalizedSecondDriftAngularConnectionField
  simp only [real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum]
  simp_rw [hs, mul_neg]
  simp only [Finset.sum_neg_distrib, mul_neg]

lemma normalizedSecondDriftDegreeField_inner_symm (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
  ⟪normalizedSecondDriftDegreeField hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 H hH x⟫_ℝ =
    ⟪ambientSphereL2 G hG x,
      normalizedSecondDriftDegreeField hO hD g1 g2 hg1 L lam δ R p H hH x⟫_ℝ := by
  unfold normalizedSecondDriftDegreeField
  simp only [real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum]
  rw [ambientDegreeField_inner_symm hO hD G H hG hH x]

lemma contDiff_normalizedSecondDriftFirstAdjointField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) : ContDiff ℝ ∞ (normalizedSecondDriftFirstAdjointField hO hD g1 g2 hg1 L lam δ R p G hG) := by
  have hm : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g1 L (lam,x)) :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have hb (j : Fin 3) : ContDiff ℝ ∞
      (fun x : R3 => normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)) :=
    (contDiff_normalizedSecondDriftCoordinateJoint g1 g2 hg1 hg2 L j).comp
      (contDiff_const.prodMk contDiff_id)
  have hmi : ContDiff ℝ ∞ (fun x : R3 => (referenceDensityFamily g1 L (lam,x))⁻¹) :=
    (contDiff_referenceDensityFamily_inv g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hv (j : Fin 3) : ContDiff ℝ ∞ (fun x : R3 =>
      directionalFDeriv (coordinateDirection j)
        (fun y => (referenceDensityFamily g1 L (lam,y) * referenceRadius δ R p L y *
          normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) • ambientSphereL2 G hG y) x) :=
    (((hm.mul hr).mul (hb j)).smul (contDiff_ambientSphereL2 G hG)).fderiv_right
      (m := ∞) (by simp) |>.clm_apply contDiff_const
  have hs : ContDiff ℝ ∞ (fun x : R3 => ∑ j : Fin 3,
      directionalFDeriv (coordinateDirection j)
        (fun y => (referenceDensityFamily g1 L (lam,y) * referenceRadius δ R p L y *
          normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) • ambientSphereL2 G hG y) x) :=
    ContDiff.sum (fun j _ => hv j)
  unfold normalizedSecondDriftFirstAdjointField
  exact hmi.neg.smul hs

lemma contDiff_normalizedSecondDriftAngularConnectionField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) : ContDiff ℝ ∞ (normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p G hG) := by
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have hb (a : Fin 3) : ContDiff ℝ ∞
      (fun x : R3 => normalizedSecondDriftFrameJoint g1 g2 L a (lam,x)) :=
    (contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a).comp
      (contDiff_const.prodMk contDiff_id)
  have hs : ContDiff ℝ ∞ (fun x : R3 => ∑ a : Fin 3,
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
        normalizedReferenceAngularConnection hO hD g1 L lam x
          (referenceMetricGramFrame g1 L (lam,x) a)
          (ambientBesselField hO hD 1 (by norm_num) G hG x)) :=
    ContDiff.sum (fun a _ => (hb a).smul
      ((contDiff_normalizedReferenceAngularConnection_frame hO hD g1 hg1 L lam a).clm_apply
        (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG)))
  unfold normalizedSecondDriftAngularConnectionField
  exact hr.smul hs

lemma contDiff_normalizedSecondDriftDegreeField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) : ContDiff ℝ ∞ (normalizedSecondDriftDegreeField hO hD g1 g2 hg1 L lam δ R p G hG) := by
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have hb (a : Fin 3) : ContDiff ℝ ∞
      (fun x : R3 => normalizedSecondDriftFrameJoint g1 g2 L a (lam,x)) :=
    (contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a).comp
      (contDiff_const.prodMk contDiff_id)
  have hf (a : Fin 3) := contDiff_referenceFrameDerivative g1 hg1 L lam a
    (fun y => Real.log (referenceRadius δ R p L y))
    (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hs : ContDiff ℝ ∞ (fun x : R3 => ∑ a : Fin 3,
      (normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) *
        referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)) x) •
          ambientDegreeField hO hD G hG x) :=
    ContDiff.sum (fun a _ => ((hb a).mul (hf a)).smul
      (contDiff_ambientDegreeField hO hD G hG))
  unfold normalizedSecondDriftDegreeField
  exact hr.smul hs

lemma contDiff_normalizedSecondDriftDensityDivergence (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
  ContDiff ℝ ∞ (normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p) := by
  have hm : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g1 L (lam,x)) :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have hb (j : Fin 3) : ContDiff ℝ ∞
      (fun x : R3 => normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)) :=
    (contDiff_normalizedSecondDriftCoordinateJoint g1 g2 hg1 hg2 L j).comp
      (contDiff_const.prodMk contDiff_id)
  have hmi : ContDiff ℝ ∞ (fun x : R3 => (referenceDensityFamily g1 L (lam,x))⁻¹) :=
    (contDiff_referenceDensityFamily_inv g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hv (j : Fin 3) : ContDiff ℝ ∞ (fun x : R3 =>
      directionalFDeriv (coordinateDirection j)
        (fun y => referenceDensityFamily g1 L (lam,y) * referenceRadius δ R p L y *
          normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) x) :=
    (((hm.mul hr).mul (hb j)).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hs : ContDiff ℝ ∞ (fun x : R3 => ∑ j : Fin 3,
      directionalFDeriv (coordinateDirection j)
        (fun y => referenceDensityFamily g1 L (lam,y) * referenceRadius δ R p L y *
          normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) x) :=
    ContDiff.sum (fun j _ => hv j)
  unfold normalizedSecondDriftDensityDivergence
  exact hmi.mul hs

lemma contDiff_normalizedSecondWeightedDriftAdjointField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) : ContDiff ℝ ∞ (normalizedSecondWeightedDriftAdjointField hO hD g1 g2 hg1 L lam δ R p G hG) := by
  unfold normalizedSecondWeightedDriftAdjointField
  exact ((contDiff_normalizedSecondDriftFirstAdjointField hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR).sub
    (contDiff_normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR)).add
      (contDiff_normalizedSecondDriftDegreeField hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR)

lemma normalizedSecondDriftFirstAdjointField_eq_zero_outside (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
  normalizedSecondDriftFirstAdjointField hO hD g1 g2 hg1 L lam δ R p G hG x = 0 := by
  have he (j : Fin 3) :
      (fun y => (referenceDensityFamily g1 L (lam,y) * referenceRadius δ R p L y *
        normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) • ambientSphereL2 G hG y)
        =ᶠ[𝓝 x] (fun _ : R3 => (0 : SphereL2)) := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    rw [ambientSphereL2_eq_zero G hG y (hz y hy), smul_zero]
  have hd (j : Fin 3) : directionalFDeriv (coordinateDirection j)
      (fun y => (referenceDensityFamily g1 L (lam,y) * referenceRadius δ R p L y *
        normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) • ambientSphereL2 G hG y) x = 0 := by
    unfold directionalFDeriv
    rw [(he j).fderiv_eq]
    simp
  unfold normalizedSecondDriftFirstAdjointField
  simp_rw [hd]
  simp only [Finset.sum_const_zero, smul_zero]

lemma normalizedSecondDriftAngularConnectionField_eq_zero_outside (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
  normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p G hG x = 0 := by
  unfold normalizedSecondDriftAngularConnectionField
  rw [ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx]
  simp only [map_zero, smul_zero, Finset.sum_const_zero]

lemma normalizedSecondDriftDegreeField_eq_zero_outside (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
  normalizedSecondDriftDegreeField hO hD g1 g2 hg1 L lam δ R p G hG x = 0 := by
  unfold normalizedSecondDriftDegreeField ambientDegreeField
  rw [ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx,
    ambientSphereL2_eq_zero G hG x (hz x hx)]
  simp only [sub_self, smul_zero, Finset.sum_const_zero]

lemma normalizedSecondWeightedDriftAdjointField_eq_zero_outside (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
  normalizedSecondWeightedDriftAdjointField hO hD g1 g2 hg1 L lam δ R p G hG x = 0 := by
  unfold normalizedSecondWeightedDriftAdjointField
  rw [normalizedSecondDriftFirstAdjointField_eq_zero_outside hO hD g1 g2 hg1 L lam δ R p G hG K hK hz x hx,
    normalizedSecondDriftAngularConnectionField_eq_zero_outside hO hD g1 g2 hg1 L lam δ R p G hG K hK hz x hx,
    normalizedSecondDriftDegreeField_eq_zero_outside hO hD g1 g2 hg1 L lam δ R p G hG K hK hz x hx]
  simp

theorem compact_normalizedSecondDriftFirstBase_adjoint (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (K : Set R3) (hK : IsCompact K)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ K, ∀ theta : UnitSphere, H (x,theta.val)=0) :
  (∫ x : R3, referenceDensityFamily g1 L (lam,x) *
    ⟪normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 H hH x⟫_ℝ) =
  ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
    ⟪ambientSphereL2 G hG x,
      normalizedSecondDriftFirstAdjointField hO hD g1 g2 hg1 L lam δ R p H hH x⟫_ℝ := by
  let mu (x : R3) : ℝ := referenceDensityFamily g1 L (lam,x)
  let a (j : Fin 3) (x : R3) : ℝ := referenceRadius δ R p L x *
    normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)
  let u := ambientSphereL2 G hG
  let v := ambientSphereL2 H hH
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have ha (j : Fin 3) : ContDiff ℝ ∞ (a j) :=
    (contDiff_referenceRadius_actual δ R p L hδ hR).mul
      ((contDiff_normalizedSecondDriftCoordinateJoint g1 g2 hg1 hg2 L j).comp
        (contDiff_const.prodMk contDiff_id))
  have hu : ContDiff ℝ ∞ u := contDiff_ambientSphereL2 G hG
  have hv : ContDiff ℝ ∞ v := contDiff_ambientSphereL2 H hH
  have hcG : HasCompactSupport u := hasCompactSupport_ambientSphereL2 G hG K hK hzG
  have hcH : HasCompactSupport v := hasCompactSupport_ambientSphereL2 H hH K hK hzH
  have hd (j : Fin 3) : ContDiff ℝ ∞
      (fun x => directionalFDeriv (coordinateDirection j) u x) :=
    (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hwd (j : Fin 3) : ContDiff ℝ ∞ (fun x => directionalFDeriv (coordinateDirection j)
      (fun y => (mu y*a j y) • v y) x) :=
    (((hm.mul (ha j)).smul hv).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hleft (j : Fin 3) : Integrable (fun x => mu x*a j x*
      ⟪directionalFDeriv (coordinateDirection j) u x,v x⟫_ℝ) := by
    have hi := BaseDensityAdjoint.compact_inner_integrable (fun x => (mu x*a j x) • v x)
      (fun x => directionalFDeriv (coordinateDirection j) u x)
      ((hm.mul (ha j)).smul hv).continuous (hd j).continuous
      (hcG.fderiv_apply (𝕜 := ℝ) (coordinateDirection j))
    have he : (fun x => ⟪(mu x*a j x) • v x,
        directionalFDeriv (coordinateDirection j) u x⟫_ℝ) =
        (fun x => mu x*a j x*⟪directionalFDeriv (coordinateDirection j) u x,v x⟫_ℝ) := by
      funext x
      rw [real_inner_smul_left,real_inner_comm]
    rw [he] at hi
    exact hi
  have hright (j : Fin 3) : Integrable (fun x =>
      ⟪directionalFDeriv (coordinateDirection j) (fun y => (mu y*a j y) • v y) x,u x⟫_ℝ) :=
    BaseDensityAdjoint.compact_inner_integrable _ u (hwd j).continuous hu.continuous hcG
  have hadj (j : Fin 3) :
      (∫ x : R3, mu x*a j x*⟪directionalFDeriv (coordinateDirection j) u x,v x⟫_ℝ) =
      -(∫ x : R3, ⟪directionalFDeriv (coordinateDirection j)
        (fun y => (mu y*a j y) • v y) x,u x⟫_ℝ) := by
    simpa only [BaseDensityAdjoint.directionalDeriv, directionalFDeriv] using
      BaseDensityAdjoint.compact_weighted_first_adjoint (coordinateDirection j) mu (a j) u v
        hm (ha j) hu hv hcG
  have hL (x : R3) : mu x *
      ⟪normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x,v x⟫_ℝ =
      ∑ j : Fin 3, mu x*a j x*⟪directionalFDeriv (coordinateDirection j) u x,v x⟫_ℝ := by
    unfold normalizedSecondDriftFirstBaseField
    simp only [real_inner_smul_left, sum_inner, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [a,u]
    ring
  have hRhs (x : R3) : mu x *
      ⟪u x,normalizedSecondDriftFirstAdjointField hO hD g1 g2 hg1 L lam δ R p H hH x⟫_ℝ =
      -(∑ j : Fin 3, ⟪directionalFDeriv (coordinateDirection j)
        (fun y => (mu y*a j y) • v y) x,u x⟫_ℝ) := by
    have hmu : mu x ≠ 0 := (referenceDensityFamily_pos g1 hg1 L (lam,x)).ne'
    have hc : mu x * -(mu x)⁻¹ = -1 := by rw [mul_neg, mul_inv_cancel₀ hmu]
    unfold normalizedSecondDriftFirstAdjointField
    simp only [mul_assoc]
    change mu x * ⟪u x,-(mu x)⁻¹ • (∑ j : Fin 3,
      directionalFDeriv (coordinateDirection j) (fun y => (mu y*a j y) • v y) x)⟫_ℝ = _
    rw [real_inner_smul_right, ← mul_assoc, hc]
    simp only [neg_one_mul, inner_sum, real_inner_comm]
  change (∫ x : R3, mu x *
      ⟪normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x,v x⟫_ℝ) =
    ∫ x : R3, mu x *
      ⟪u x,normalizedSecondDriftFirstAdjointField hO hD g1 g2 hg1 L lam δ R p H hH x⟫_ℝ
  simp_rw [hL,hRhs]
  rw [integral_finset_sum _ (fun j _ => hleft j), integral_neg,
    integral_finset_sum _ (fun j _ => hright j)]
  simp_rw [hadj]
  simp only [Finset.sum_neg_distrib]

theorem compact_normalizedSecondWeightedDrift_adjoint (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (K : Set R3) (hK : IsCompact K)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ K, ∀ theta : UnitSphere, H (x,theta.val)=0) :
  (∫ x : R3, referenceDensityFamily g1 L (lam,x) *
    ⟪normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 H hH x⟫_ℝ) =
  ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
    ⟪ambientSphereL2 G hG x,
      normalizedSecondWeightedDriftAdjointField hO hD g1 g2 hg1 L lam δ R p H hH x⟫_ℝ := by
  let mu (x : R3) : ℝ := referenceDensityFamily g1 L (lam,x)
  let u := ambientSphereL2 G hG
  let v := ambientSphereL2 H hH
  let f := normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG
  let omega := normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p G hG
  let degree := normalizedSecondDriftDegreeField hO hD g1 g2 hg1 L lam δ R p G hG
  let fa := normalizedSecondDriftFirstAdjointField hO hD g1 g2 hg1 L lam δ R p H hH
  let oa := normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p H hH
  let ba := normalizedSecondDriftDegreeField hO hD g1 g2 hg1 L lam δ R p H hH
  have hcG : HasCompactSupport u := hasCompactSupport_ambientSphereL2 G hG K hK hzG
  have hcH : HasCompactSupport v := hasCompactSupport_ambientSphereL2 H hH K hK hzH
  have hu : ContDiff ℝ ∞ u := contDiff_ambientSphereL2 G hG
  have hv : ContDiff ℝ ∞ v := contDiff_ambientSphereL2 H hH
  have hFirstS : ContDiff ℝ ∞ f := by
    have hb (j : Fin 3) : ContDiff ℝ ∞
        (fun x : R3 => normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)) :=
      (contDiff_normalizedSecondDriftCoordinateJoint g1 g2 hg1 hg2 L j).comp
        (contDiff_const.prodMk contDiff_id)
    have hd (j : Fin 3) : ContDiff ℝ ∞
        (fun x => directionalFDeriv (coordinateDirection j) u x) :=
      (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hs : ContDiff ℝ ∞ (fun x : R3 => ∑ j : Fin 3,
        normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x) •
          directionalFDeriv (coordinateDirection j) u x) :=
      ContDiff.sum (fun j _ => (hb j).smul (hd j))
    exact (contDiff_referenceRadius_actual δ R p L hδ hR).smul hs
  have hFirstPair : Integrable (fun x => mu x*⟪f x,v x⟫_ℝ) :=
    integrable_density_pair_of_contDiff g1 hg1 L lam f v hFirstS hv hcH
  have hAngularPair : Integrable (fun x => mu x*⟪omega x,v x⟫_ℝ) :=
    integrable_density_pair_of_contDiff g1 hg1 L lam omega v
      (contDiff_normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR) hv hcH
  have hDegreePair : Integrable (fun x => mu x*⟪degree x,v x⟫_ℝ) :=
    integrable_density_pair_of_contDiff g1 hg1 L lam degree v
      (contDiff_normalizedSecondDriftDegreeField hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR) hv hcH
  have hFA : Integrable (fun x => mu x*⟪u x,fa x⟫_ℝ) := by
    have hi := integrable_density_pair_of_contDiff g1 hg1 L lam fa u
      (contDiff_normalizedSecondDriftFirstAdjointField hO hD g1 g2 hg1 L lam δ R p H hH hg2 hδ hR) hu hcG
    simpa only [real_inner_comm] using hi
  have hOA : Integrable (fun x => mu x*⟪u x,oa x⟫_ℝ) := by
    have hi := integrable_density_pair_of_contDiff g1 hg1 L lam oa u
      (contDiff_normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p H hH hg2 hδ hR) hu hcG
    simpa only [real_inner_comm] using hi
  have hBA : Integrable (fun x => mu x*⟪u x,ba x⟫_ℝ) := by
    have hi := integrable_density_pair_of_contDiff g1 hg1 L lam ba u
      (contDiff_normalizedSecondDriftDegreeField hO hD g1 g2 hg1 L lam δ R p H hH hg2 hδ hR) hu hcG
    simpa only [real_inner_comm] using hi
  have hSplit : (∫ x : R3, mu x*⟪f x+omega x+degree x,v x⟫_ℝ) =
      (∫ x : R3, mu x*⟪f x,v x⟫_ℝ) + (∫ x : R3, mu x*⟪omega x,v x⟫_ℝ) +
        (∫ x : R3, mu x*⟪degree x,v x⟫_ℝ) := by
    simp only [inner_add_left, mul_add]
    exact (integral_add (hFirstPair.add hAngularPair) hDegreePair).trans
      (congrArg (fun z => z + (∫ x : R3, mu x*⟪degree x,v x⟫_ℝ))
        (integral_add hFirstPair hAngularPair))
  have hAdjSplit : (∫ x : R3, mu x*⟪u x,fa x-oa x+ba x⟫_ℝ) =
      (∫ x : R3, mu x*⟪u x,fa x⟫_ℝ) - (∫ x : R3, mu x*⟪u x,oa x⟫_ℝ) +
        (∫ x : R3, mu x*⟪u x,ba x⟫_ℝ) := by
    simp only [inner_add_right, inner_sub_right, mul_add, mul_sub]
    exact (integral_add (hFA.sub hOA) hBA).trans
      (congrArg (fun z => z + (∫ x : R3, mu x*⟪u x,ba x⟫_ℝ))
        (integral_sub hFA hOA))
  have hFirst := compact_normalizedSecondDriftFirstBase_adjoint hO hD g1 g2 hg1
    L lam δ R p G H hG hH hg2 hδ hR K hK hzG hzH
  have hOmega : (∫ x : R3, mu x*⟪omega x,v x⟫_ℝ) =
      -(∫ x : R3, mu x*⟪u x,oa x⟫_ℝ) := by
    have he (x : R3) : mu x*⟪omega x,v x⟫_ℝ = -(mu x*⟪u x,oa x⟫_ℝ) := by
      rw [normalizedSecondDriftAngularConnectionField_inner_skew hO hD g1 g2 hg1
        L lam δ R p G H hG hH x]
      ring
    simp_rw [he]
    exact integral_neg _
  have hDegree : (∫ x : R3, mu x*⟪degree x,v x⟫_ℝ) =
      (∫ x : R3, mu x*⟪u x,ba x⟫_ℝ) := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [normalizedSecondDriftDegreeField_inner_symm hO hD g1 g2 hg1 L lam δ R p G H hG hH x]
  simp_rw [normalizedSecondWeightedDriftField_base_angular_degree_split hO hD g1 g2 hg1
    L lam δ R p G hG]
  change (∫ x : R3, mu x*⟪f x+omega x+degree x,v x⟫_ℝ) =
    ∫ x : R3, mu x*⟪u x,fa x-oa x+ba x⟫_ℝ
  rw [hSplit,hAdjSplit,hFirst,hOmega,hDegree]
  ring

theorem normalizedSecondWeightedDriftAdjointDefect_normal_form (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
  normalizedSecondWeightedDriftAdjointDefect hO hD g1 g2 hg1 L lam δ R p G hG x =
    (-2 : ℝ) • (normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x) + (-2 : ℝ) • (normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p G hG x) -
      normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p x • ambientSphereL2 G hG x := by
  unfold normalizedSecondWeightedDriftAdjointDefect normalizedSecondWeightedDriftAdjointField
  rw [normalizedSecondDriftFirstAdjointField_expansion hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR x,
    normalizedSecondWeightedDriftField_base_angular_degree_split hO hD g1 g2 hg1 L lam δ R p G hG x]
  module

end OAI.AnisotropicCalderon.ActualNormalizedSecondDriftNativeAdjunction
