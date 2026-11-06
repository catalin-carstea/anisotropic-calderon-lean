import Calderon.ActualNormalizedSphereRotation
import Calderon.ActualReferenceDecomposition
import Calderon.BalancedAngularShift

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualReferenceConnectionAngular
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph AngularWeightedCore BoundedAngularShift BalancedAngularShift
  HarmonicDerivativeOperator SmoothSphereFields SmoothAngularApplication AmbientAngularShift
  SmoothMovingFrameFields SmoothAmbientAngularCasimir SmoothSphereRotationProjection
  WeightedSphereRotation ActualNormalizedSphereRotation ActualReferenceDecomposition WeightedBaseSpectral

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
  dsimp only [Prod.fst]
  have hsub := (sub_smul (besselWeight 2 (m+1)) (besselWeight 1 (m+1))
    (sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG x))).symm
  rw [hsub,smul_smul,map_smul,inverseDegreeWeight_second_difference,
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

/-- R_ab A_i u in the genuine operator order; constructed without a commutator premise. -/
def ambientRotatedDerivativeField (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => normalizedRotation hO hD a b (ambientDerivativeBesselField hF hO hD i G hG x)

lemma ambientRotatedDerivativeField_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientDerivativeField hF hO hD i G hG x,
      ambientRotatedDerivativeField hF hO hD i a b G hG x) ∈
        sphereRotationGraph hO hD a b :=
  normalizedRotation_graph hO hD a b _ _
    (ambientDerivativeBesselField_graph hF hO hD i G hG x)

lemma contDiff_ambientRotatedDerivativeField (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientRotatedDerivativeField hF hO hD i a b G hG) :=
  (normalizedRotation hO hD a b).contDiff.comp
    (contDiff_ambientDerivativeBesselField hF hO hD i G hG)

lemma ambientRotatedDerivativeField_eq_zero (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    ambientRotatedDerivativeField hF hO hD i a b G hG x = 0 := by
  rw [ambientRotatedDerivativeField,
    ambientDerivativeBesselField_eq_zero hF hO hD i G hG K hz x hx,map_zero]

lemma ambientRotationField_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientSphereL2 G hG x,
      ambientSphereL2 (ambientAngularRotation a b G)
        (contDiff_ambientAngularRotation a b G hG) x) ∈ sphereRotationGraph hO hD a b :=
  fun k => sphereHarmonicCoordinate_ambientAngularRotation hO hD k a b G hG x

/-- Genuine individual angular adjunction, with the adjoint order R_ab A_i. -/
theorem inner_ambientRaising_rotation (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i a b : Fin 3)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    ⟪ambientRaisingField hF hO hD i (ambientAngularRotation a b G)
        (contDiff_ambientAngularRotation a b G hG) x,ambientSphereL2 H hH x⟫_ℝ =
      -⟪ambientSphereL2 G hG x,ambientRotatedDerivativeField hF hO hD i a b H hH x⟫_ℝ := by
  calc
    _ = ⟪ambientSphereL2 (ambientAngularRotation a b G)
        (contDiff_ambientAngularRotation a b G hG) x,
        ambientDerivativeField hF hO hD i H hH x⟫_ℝ := by
      have h := sphereDerivativeGraph_inner_adjoint hF hO hD i
        (ambientSphereL2 H hH x) (ambientDerivativeField hF hO hD i H hH x)
        (ambientSphereL2 (ambientAngularRotation a b G)
          (contDiff_ambientAngularRotation a b G hG) x)
        (ambientRaisingField hF hO hD i (ambientAngularRotation a b G)
          (contDiff_ambientAngularRotation a b G hG) x)
        (ambientDerivativeField_graph hF hO hD i H hH x)
        (ambientRaisingField_graph hF hO hD i (ambientAngularRotation a b G)
          (contDiff_ambientAngularRotation a b G hG) x)
      simpa only [real_inner_comm] using h.symm
    _ = _ := sphereRotationGraph_inner_skew hO hD a b _ _ _ _
      (ambientRotationField_graph hO hD a b G hG x)
      (ambientRotatedDerivativeField_graph hF hO hD i a b H hH x)

lemma norm_half_ambientRaising_rotation_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ‖halfDegreeMultiplier hO hD
      (ambientRaisingField hF hO hD i (ambientAngularRotation a b G)
        (contDiff_ambientAngularRotation a b G hG) x)‖ ≤
      4 * ‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ := by
  rw [← balancedRaising_ambient_realization hF hO hD i (ambientAngularRotation a b G)
    (contDiff_ambientAngularRotation a b G hG) x]
  have hR : ‖ambientBesselField hO hD (1/2 : ℝ) (by norm_num)
        (ambientAngularRotation a b G) (contDiff_ambientAngularRotation a b G hG) x‖^2 ≤
      2 * ‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖^2 := by
    convert norm_sq_ambient_weighted_rotation_le hO hD (1/2 : ℝ) (by norm_num) a b G hG x using 1 <;> norm_num
  have hR' : ‖ambientBesselField hO hD (1/2 : ℝ) (by norm_num)
        (ambientAngularRotation a b G) (contDiff_ambientAngularRotation a b G hG) x‖ ≤
      2 * ‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ := by
    nlinarith [norm_nonneg (ambientBesselField hO hD (1/2 : ℝ) (by norm_num)
      (ambientAngularRotation a b G) (contDiff_ambientAngularRotation a b G hG) x),
      norm_nonneg (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x)]
  have hA := ((balancedRaising hF hO hD i).le_opNorm
    (ambientBesselField hO hD (1/2 : ℝ) (by norm_num)
      (ambientAngularRotation a b G) (contDiff_ambientAngularRotation a b G hG) x)).trans
    (mul_le_mul_of_nonneg_right (norm_balancedRaising_le hF hO hD i) (norm_nonneg _))
  nlinarith

lemma abs_inner_ambientRaising_rotation_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i a b : Fin 3)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    |⟪ambientRaisingField hF hO hD i (ambientAngularRotation a b G)
        (contDiff_ambientAngularRotation a b G hG) x,ambientSphereL2 H hH x⟫_ℝ| ≤
      4 * ‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ *
        ‖ambientBesselField hO hD (1/2 : ℝ) (by norm_num) H hH x‖ := by
  rw [inner_eq_halfDegreeMultiplier hO hD _ _ _
    (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) H hH x)]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_half_ambientRaising_rotation_le hF hO hD i a b G hG x)
      (norm_nonneg _))

/-- The actual angular adjoint contribution, in the true order R_ab A_i. -/
def referenceConnectionAdjoint (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ i : Fin 3, (-1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
    referenceConnectionEntry g L lam i a b x •
      ambientRotatedDerivativeField hF hO hD i a b G hG x

theorem referenceConnectionRaising_inner_adjoint (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    ⟪referenceConnectionRaising hF hO hD g L lam G hG x,ambientSphereL2 H hH x⟫_ℝ =
      ⟪ambientSphereL2 G hG x,referenceConnectionAdjoint hF hO hD g L lam H hH x⟫_ℝ := by
  simp only [referenceConnectionRaising,referenceConnectionAdjoint,sum_inner,inner_sum,
    real_inner_smul_left,real_inner_smul_right,Finset.mul_sum,
    inner_ambientRaising_rotation hF hO hD _ _ _ G H hG hH x]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma contDiff_referenceConnectionRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceConnectionRaising hF hO hD g L lam G hG) :=
  ContDiff.sum fun i _ => (ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
    (contDiff_referenceConnectionEntry g hg L lam i a b).smul
      (contDiff_ambientRaisingField hF hO hD i (ambientAngularRotation a b G)
        (contDiff_ambientAngularRotation a b G hG))).const_smul (1/2 : ℝ)

lemma contDiff_referenceConnectionAdjoint (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceConnectionAdjoint hF hO hD g L lam G hG) :=
  ContDiff.sum fun i _ => (ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
    (contDiff_referenceConnectionEntry g hg L lam i a b).smul
      (contDiff_ambientRotatedDerivativeField hF hO hD i a b G hG)).const_smul (-1/2 : ℝ)

lemma referenceConnectionRaising_eq_zero (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceConnectionRaising hF hO hD g L lam G hG x = 0 := by
  unfold referenceConnectionRaising
  have he (i a b : Fin 3) := ambientRaisingField_eq_zero hF hO hD i
    (ambientAngularRotation a b G) (contDiff_ambientAngularRotation a b G hG) K
    (ambientAngularRotation_sphere_zero a b G hG K hz) x hx
  simp only [he,smul_zero,Finset.sum_const_zero]

lemma referenceConnectionAdjoint_eq_zero (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceConnectionAdjoint hF hO hD g L lam G hG x = 0 := by
  simp only [referenceConnectionAdjoint,
    ambientRotatedDerivativeField_eq_zero hF hO hD _ _ _ G hG K hz x hx,
    smul_zero,Finset.sum_const_zero]

lemma hasCompactSupport_referenceConnectionRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (referenceConnectionRaising hF hO hD g L lam G hG) :=
  HasCompactSupport.intro hK
    (fun x hx => referenceConnectionRaising_eq_zero hF hO hD g L lam G hG K hz x hx)

lemma hasCompactSupport_referenceConnectionAdjoint (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (referenceConnectionAdjoint hF hO hD g L lam G hG) :=
  HasCompactSupport.intro hK
    (fun x hx => referenceConnectionAdjoint_eq_zero hF hO hD g L lam G hG K hz x hx)

/-- The literal actual coefficient mass, rather than a supplied operator bound. -/
def referenceConnectionMass (g : MatrixField) (L lam : ℝ) (x : R3) : ℝ :=
  (1/2 : ℝ) * ∑ i : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
    |referenceConnectionEntry g L lam i a b x|

lemma referenceConnectionMass_nonneg (g : MatrixField) (L lam : ℝ) (x : R3) :
    0 ≤ referenceConnectionMass g L lam x := by
  unfold referenceConnectionMass
  positivity

/-- Actual full finite connection contribution, with every input degree retained. -/
theorem norm_half_referenceConnectionRaising_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ‖halfDegreeMultiplier hO hD (referenceConnectionRaising hF hO hD g L lam G hG x)‖ ≤
      4 * referenceConnectionMass g L lam x *
        ‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ := by
  let V (i a b : Fin 3) := halfDegreeMultiplier hO hD
    (ambientRaisingField hF hO hD i (ambientAngularRotation a b G)
      (contDiff_ambientAngularRotation a b G hG) x)
  let C : ℝ := 4 * ‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖
  have hV (i a b : Fin 3) : ‖V i a b‖ ≤ C :=
    norm_half_ambientRaising_rotation_le hF hO hD i a b G hG x
  have hb (i a b : Fin 3) :
      ‖referenceConnectionEntry g L lam i a b x • V i a b‖ ≤
        |referenceConnectionEntry g L lam i a b x| * C := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hV i a b) (abs_nonneg _)
  have ha (i a : Fin 3) :
      ‖∑ b : Fin 3, referenceConnectionEntry g L lam i a b x • V i a b‖ ≤
        ∑ b : Fin 3, |referenceConnectionEntry g L lam i a b x| * C :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb i a b)
  have hi (i : Fin 3) :
      ‖(1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
        referenceConnectionEntry g L lam i a b x • V i a b‖ ≤
      (1/2 : ℝ) * ∑ a : Fin 3, ∑ b : Fin 3,
        |referenceConnectionEntry g L lam i a b x| * C := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : 0 < (1/2 : ℝ))]
    exact mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ha i a)) (by norm_num)
  have hall : ‖∑ i : Fin 3, (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
      referenceConnectionEntry g L lam i a b x • V i a b‖ ≤
      ∑ i : Fin 3, (1/2 : ℝ) * ∑ a : Fin 3, ∑ b : Fin 3,
        |referenceConnectionEntry g L lam i a b x| * C :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hi i)
  simp only [referenceConnectionRaising,map_sum,map_smul]
  change ‖∑ i : Fin 3, (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
    referenceConnectionEntry g L lam i a b x • V i a b‖ ≤ _
  calc
    _ ≤ ∑ i : Fin 3, (1/2 : ℝ) * ∑ a : Fin 3, ∑ b : Fin 3,
        |referenceConnectionEntry g L lam i a b x| * C := hall
    _ = _ := by
      simp only [← Finset.sum_mul,← Finset.mul_sum,referenceConnectionMass,C]
      ring

theorem abs_inner_referenceConnectionRaising_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    |⟪referenceConnectionRaising hF hO hD g L lam G hG x,ambientSphereL2 H hH x⟫_ℝ| ≤
      4 * referenceConnectionMass g L lam x *
        ‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ *
        ‖ambientBesselField hO hD (1/2 : ℝ) (by norm_num) H hH x‖ := by
  rw [inner_eq_halfDegreeMultiplier hO hD _ _ _
    (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) H hH x)]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_half_referenceConnectionRaising_le hF hO hD g L lam G hG x)
      (norm_nonneg _))

lemma halfDegreeMultiplier_normalizedRotation (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) (u : SphereL2) :
    halfDegreeMultiplier hO hD (normalizedRotation hO hD a b u) =
      normalizedRotation hO hD a b (halfDegreeMultiplier hO hD u) := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k
      (halfDegreeMultiplier hO hD (normalizedRotation hO hD a b u)) =
    sphereHarmonicCoordinate hO hD k
      (normalizedRotation hO hD a b (halfDegreeMultiplier hO hD u))
  have hN (v : SphereL2) : sphereHarmonicCoordinate hO hD k
      (normalizedRotation hO hD a b v) =
      harmonicSphereRotation k a b (sphereHarmonicCoordinate hO hD k
        (inverseDegreeMultiplier hO hD v)) := normalizedRotationOutput_graph hO hD a b v k
  rw [halfDegreeMultiplier_coordinate,hN u,hN (halfDegreeMultiplier hO hD u),
    inverseDegreeMultiplier_coordinate,inverseDegreeMultiplier_coordinate,
    halfDegreeMultiplier_coordinate]
  simp only [map_smul,smul_smul]
  congr 1
  ring

lemma halfDegreeWeight_mul_one (k : ℕ) :
    halfDegreeWeight k * besselWeight 1 k = besselWeight (1/2 : ℝ) k := by
  unfold halfDegreeWeight besselWeight
  rw [← Real.rpow_add (by positivity)]
  norm_num

lemma half_ambientDerivativeBesselField_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientDerivativeField hF hO hD i G hG x,
      halfDegreeMultiplier hO hD (ambientDerivativeBesselField hF hO hD i G hG x)) ∈
        sphereBesselGraph hO hD (1/2 : ℝ) := by
  intro k
  rw [halfDegreeMultiplier_coordinate,ambientDerivativeBesselField_graph hF hO hD i G hG x k,
    smul_smul,halfDegreeWeight_mul_one]

lemma norm_half_ambientRotatedDerivativeField_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ‖halfDegreeMultiplier hO hD (ambientRotatedDerivativeField hF hO hD i a b G hG x)‖ ≤
      4 * ‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ := by
  have hU : (ambientSphereL2 G hG x,
      ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x) ∈
      sphereBesselGraph hO hD ((1/2 : ℝ)+1) := by
    convert ambientBesselField_graph hO hD (3/2 : ℝ) (by norm_num) G hG x using 1 <;> norm_num
  have hD2 := norm_sq_weighted_derivative_le hF hO hD i (1/2 : ℝ) (by norm_num)
    (ambientSphereL2 G hG x) (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x)
    (ambientDerivativeField hF hO hD i G hG x)
    (halfDegreeMultiplier hO hD (ambientDerivativeBesselField hF hO hD i G hG x)) hU
    (ambientDerivativeField_graph hF hO hD i G hG x)
    (half_ambientDerivativeBesselField_graph hF hO hD i G hG x)
  have hderivative : ‖halfDegreeMultiplier hO hD (ambientDerivativeBesselField hF hO hD i G hG x)‖ ≤
      2 * ‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ := by
    nlinarith [norm_nonneg (halfDegreeMultiplier hO hD
      (ambientDerivativeBesselField hF hO hD i G hG x)),
      norm_nonneg (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x)]
  have hs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
  have hN : ‖normalizedRotation hO hD a b‖ ≤ 2 :=
    (norm_normalizedRotation_le hO hD a b).trans hs
  rw [ambientRotatedDerivativeField,halfDegreeMultiplier_normalizedRotation]
  have h := ((normalizedRotation hO hD a b).le_opNorm
    (halfDegreeMultiplier hO hD (ambientDerivativeBesselField hF hO hD i G hG x))).trans
    (mul_le_mul_of_nonneg_right hN (norm_nonneg _))
  nlinarith

theorem norm_half_referenceConnectionAdjoint_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ‖halfDegreeMultiplier hO hD (referenceConnectionAdjoint hF hO hD g L lam G hG x)‖ ≤
      4 * referenceConnectionMass g L lam x *
        ‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ := by
  let V (i a b : Fin 3) := halfDegreeMultiplier hO hD
    (ambientRotatedDerivativeField hF hO hD i a b G hG x)
  let C : ℝ := 4 * ‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖
  have hV (i a b : Fin 3) : ‖V i a b‖ ≤ C :=
    norm_half_ambientRotatedDerivativeField_le hF hO hD i a b G hG x
  have hb (i a b : Fin 3) :
      ‖referenceConnectionEntry g L lam i a b x • V i a b‖ ≤
        |referenceConnectionEntry g L lam i a b x| * C := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hV i a b) (abs_nonneg _)
  have ha (i a : Fin 3) :
      ‖∑ b : Fin 3, referenceConnectionEntry g L lam i a b x • V i a b‖ ≤
        ∑ b : Fin 3, |referenceConnectionEntry g L lam i a b x| * C :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb i a b)
  have hi (i : Fin 3) :
      ‖(-1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
        referenceConnectionEntry g L lam i a b x • V i a b‖ ≤
      (1/2 : ℝ) * ∑ a : Fin 3, ∑ b : Fin 3,
        |referenceConnectionEntry g L lam i a b x| * C := by
    rw [norm_smul,Real.norm_eq_abs,show |(-1/2 : ℝ)| = (1/2 : ℝ) by norm_num]
    exact mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ha i a)) (by norm_num)
  have hall : ‖∑ i : Fin 3, (-1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
      referenceConnectionEntry g L lam i a b x • V i a b‖ ≤
      ∑ i : Fin 3, (1/2 : ℝ) * ∑ a : Fin 3, ∑ b : Fin 3,
        |referenceConnectionEntry g L lam i a b x| * C :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hi i)
  simp only [referenceConnectionAdjoint,map_sum,map_smul]
  change ‖∑ i : Fin 3, (-1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
    referenceConnectionEntry g L lam i a b x • V i a b‖ ≤ _
  calc
    _ ≤ ∑ i : Fin 3, (1/2 : ℝ) * ∑ a : Fin 3, ∑ b : Fin 3,
        |referenceConnectionEntry g L lam i a b x| * C := hall
    _ = _ := by
      simp only [← Finset.sum_mul,← Finset.mul_sum,referenceConnectionMass,C]
      ring

theorem abs_inner_referenceConnectionAdjoint_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    |⟪referenceConnectionAdjoint hF hO hD g L lam G hG x,ambientSphereL2 H hH x⟫_ℝ| ≤
      4 * referenceConnectionMass g L lam x *
        ‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ *
        ‖ambientBesselField hO hD (1/2 : ℝ) (by norm_num) H hH x‖ := by
  rw [inner_eq_halfDegreeMultiplier hO hD _ _ _
    (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) H hH x)]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_half_referenceConnectionAdjoint_le hF hO hD g L lam G hG x)
      (norm_nonneg _))

/-- Genuine compact adjunction for the actual reference density, with no base differentiation. -/
theorem referenceBaseLift_connection_adjoint (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (G H : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    ⟪referenceBaseLift g hg L lam (referenceConnectionRaising hF hO hD g L lam G hG)
        (contDiff_referenceConnectionRaising hF hO hD g hg L lam G hG).continuous
        (hasCompactSupport_referenceConnectionRaising hF hO hD g L lam G hG K hK hzG),
      referenceBaseLift g hg L lam (ambientSphereL2 H hH) (contDiff_ambientSphereL2 H hH).continuous
        (hasCompactSupport_ambientSphereL2 H hH J hJ hzH)⟫_ℝ =
    ⟪referenceBaseLift g hg L lam (ambientSphereL2 G hG) (contDiff_ambientSphereL2 G hG).continuous
        (hasCompactSupport_ambientSphereL2 G hG K hK hzG),
      referenceBaseLift g hg L lam (referenceConnectionAdjoint hF hO hD g L lam H hH)
        (contDiff_referenceConnectionAdjoint hF hO hD g hg L lam H hH).continuous
        (hasCompactSupport_referenceConnectionAdjoint hF hO hD g L lam H hH J hJ hzH)⟫_ℝ := by
  rw [inner_referenceBaseLift,inner_referenceBaseLift]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => congrArg
    (fun t : ℝ => ReferenceDensityBounds.referenceDensityFamily g L (lam,x) * t)
    (referenceConnectionRaising_inner_adjoint hF hO hD g L lam G H hG hH x)

end OAI.AnisotropicCalderon.ActualReferenceConnectionAngular
