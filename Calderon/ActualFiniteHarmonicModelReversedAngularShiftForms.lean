import Calderon.ActualFiniteHarmonicModelHalfShiftNorms
import Calderon.ActualFiniteHarmonicModelReferenceZeroBalanced

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SpectralCoreRegularity
  BoundedAngularShift BalancedAngularShift AngularShiftGraph ActualReferenceDDSpectralTransport
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev reversedShiftFormFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] reversedShiftFormFunction

lemma abs_inner_normalizedDerivative_weight_two_le_half_threehalf
    (hF : SphereFischerInner) (a : Fin 3) (M : SphereL2 →L[ℝ] SphereL2)
    (hM : PreservesSphereSpectralGraphs hO hD M)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪normalizedDerivative hF hO hD a (M (coreWeightOperator hO hD (besselWeight 2) F x)),G x⟫_ℝ| ≤
      ((2 * (2 : ℝ)^(1/2 : ℝ)) * ‖M‖) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  have hu1 : (coreWeightOperator hO hD (besselWeight 1) F x,
      coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1 := by
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1)
      (coreWeightOperator hO hD (besselWeight 1) F) x
  have huh : (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x,
      coreWeightOperator hO hD (besselWeight 1) F x) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [(coreWeightOperator_graph hO hD (besselWeight 1) F x) k,
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x) k,smul_smul,
      ← SectionFiveErrorForms.besselWeight_add]
    norm_num
  have hInv : halfDegreeMultiplier hO hD (M (coreWeightOperator hO hD (besselWeight 1) F x)) =
      M (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x) :=
    halfDegreeMultiplier_of_positive_half_graph hO hD _ _ (hM _ _ _ huh)
  have he := sphereDerivativeGraph_inner_adjoint hF hO hD a
    (M (coreWeightOperator hO hD (besselWeight 1) F x))
    (normalizedDerivative hF hO hD a (M (coreWeightOperator hO hD (besselWeight 2) F x)))
    (G x) (coreRaising hO hD hF a G x)
    (normalizedDerivative_graph hF hO hD a _ _ (hM _ _ _ hu1))
    (coreRaising_graph hO hD hF a G x)
  rw [he,inner_eq_halfDegreeMultiplier hO hD
    (M (coreWeightOperator hO hD (besselWeight 1) F x))
    (coreRaising hO hD hF a G x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreRaising hO hD hF a G) x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) (coreRaising hO hD hF a G) x),hInv]
  have hOp := M.le_opNorm (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x)
  have hShift := norm_coreWeight_half_raising_le hO hD hF a G x
  calc
    _ ≤ ‖M (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x)‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreRaising hO hD hF a G) x‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖M‖ * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖) *
        ((2 * (2 : ℝ)^(1/2 : ℝ)) * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖) :=
      mul_le_mul hOp hShift (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

lemma abs_inner_normalizedRaising_weight_two_le_half_threehalf
    (hF : SphereFischerInner) (a : Fin 3) (M : SphereL2 →L[ℝ] SphereL2)
    (hM : PreservesSphereSpectralGraphs hO hD M)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪normalizedRaising hF hO hD a (M (coreWeightOperator hO hD (besselWeight 2) F x)),G x⟫_ℝ| ≤
      (2 * ‖M‖) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  have hu1 : (coreWeightOperator hO hD (besselWeight 1) F x,
      coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1 := by
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1)
      (coreWeightOperator hO hD (besselWeight 1) F) x
  have huh : (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x,
      coreWeightOperator hO hD (besselWeight 1) F x) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [(coreWeightOperator_graph hO hD (besselWeight 1) F x) k,
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x) k,smul_smul,
      ← SectionFiveErrorForms.besselWeight_add]
    norm_num
  have hInv : halfDegreeMultiplier hO hD (M (coreWeightOperator hO hD (besselWeight 1) F x)) =
      M (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x) :=
    halfDegreeMultiplier_of_positive_half_graph hO hD _ _ (hM _ _ _ huh)
  have he :
      ⟪normalizedRaising hF hO hD a (M (coreWeightOperator hO hD (besselWeight 2) F x)),G x⟫_ℝ =
      ⟪M (coreWeightOperator hO hD (besselWeight 1) F x),coreDerivative hO hD hF a G x⟫_ℝ := by
    have ht := sphereDerivativeGraph_inner_adjoint hF hO hD a
      (G x) (coreDerivative hO hD hF a G x)
      (M (coreWeightOperator hO hD (besselWeight 1) F x))
      (normalizedRaising hF hO hD a (M (coreWeightOperator hO hD (besselWeight 2) F x)))
      (coreDerivative_graph hO hD hF a G x)
      (normalizedRaising_graph hF hO hD a _ _ (hM _ _ _ hu1))
    simpa only [real_inner_comm] using ht.symm
  rw [he,inner_eq_halfDegreeMultiplier hO hD
    (M (coreWeightOperator hO hD (besselWeight 1) F x))
    (coreDerivative hO hD hF a G x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF a G) x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF a G) x),hInv]
  have hOp := M.le_opNorm (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x)
  have hShift := norm_coreWeight_half_derivative_le hO hD hF a G x
  calc
    _ ≤ ‖M (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x)‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF a G) x‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖M‖ * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖) *
        (2 * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖) :=
      mul_le_mul hOp hShift (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring


end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
