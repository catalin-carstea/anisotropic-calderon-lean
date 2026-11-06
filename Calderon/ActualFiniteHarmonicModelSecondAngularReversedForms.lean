import Calderon.ActualFiniteHarmonicModelAngularCompositionForms
import Calderon.ActualFiniteHarmonicModelZeroAngularNormalization

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SpectralCoreRegularity
  BoundedAngularShift BalancedAngularShift AngularShiftGraph ActualReferenceDDSpectralTransport
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev secondReversedFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] secondReversedFunction

lemma abs_inner_preserving_weight_two_le_half_threehalf
    (M : SphereL2 →L[ℝ] SphereL2) (hM : PreservesSphereSpectralGraphs hO hD M)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪M (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ| ≤
      ‖M‖*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  have hG : (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x,
      coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD (3/2 : ℝ) := by
    intro k
    rw [(coreWeightOperator_graph hO hD (besselWeight 2) F x) k,
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x) k,
      smul_smul,← SectionFiveErrorForms.besselWeight_add]
    norm_num
  rw [spectralGraph_inner_symm hO hD (besselWeight (3/2 : ℝ))
    (M (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x))
    (M (coreWeightOperator hO hD (besselWeight 2) F x))
    (G x) (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x)
    (hM _ _ _ hG) (coreWeightOperator_graph hO hD (besselWeight (3/2 : ℝ)) G x)]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (M.le_opNorm _) (norm_nonneg _))

lemma abs_inner_raising_raising_le_half_threehalf
    (hF : SphereFischerInner) (a b : Fin 3)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪coreRaising hO hD hF a (coreRaising hO hD hF b F) x,G x⟫_ℝ| ≤
      8*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  have he : ⟪coreRaising hO hD hF a (coreRaising hO hD hF b F) x,G x⟫_ℝ =
      ⟪coreRaising hO hD hF b F x,coreDerivative hO hD hF a G x⟫_ℝ := by
    have ht := sphereDerivativeGraph_inner_adjoint hF hO hD a
      (G x) (coreDerivative hO hD hF a G x)
      (coreRaising hO hD hF b F x)
      (coreRaising hO hD hF a (coreRaising hO hD hF b F) x)
      (coreDerivative_graph hO hD hF a G x)
      (coreRaising_graph hO hD hF a (coreRaising hO hD hF b F) x)
    simpa only [real_inner_comm] using ht.symm
  rw [he]
  have hp := abs_inner_raising_le_half_norm hF hO hD b (F x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x)
    (coreRaising hO hD hF b F x) (coreDerivative hO hD hF a G x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF a G) x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x)
    (coreRaising_graph hO hD hF b F x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF a G) x)
  have hn := norm_coreWeight_half_derivative_le hO hD hF a G x
  calc
    _ ≤ 4*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF a G) x‖ := hp.trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) (norm_nonneg _)) (norm_nonneg _))
    _ ≤ 4*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      (2*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖) :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg (by norm_num) (norm_nonneg _))
    _ = _ := by ring

lemma abs_inner_normalizedRaising_twice_weight_two_le_half_threehalf
    (hF : SphereFischerInner) (a b : Fin 3)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪normalizedRaising hF hO hD a (normalizedRaising hF hO hD b
      ((ContinuousLinearMap.id ℝ SphereL2+inverseDegreeMultiplier hO hD)
        (coreWeightOperator hO hD (besselWeight 2) F x))),G x⟫_ℝ| ≤
      8*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  have he : normalizedRaising hF hO hD a (normalizedRaising hF hO hD b
      ((ContinuousLinearMap.id ℝ SphereL2+inverseDegreeMultiplier hO hD)
        (coreWeightOperator hO hD (besselWeight 2) F x))) =
      coreRaising hO hD hF a (coreRaising hO hD hF b F) x := by
    change _ = normalizedRaising hF hO hD a
      (coreWeightOperator hO hD (besselWeight 1) (coreRaising hO hD hF b F) x)
    rw [coreWeight_one_raising_apply_eq_normalized_shift]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.id_apply,
      inverseDegreeMultiplier_coreWeight_two_apply]
  rw [he]
  exact abs_inner_raising_raising_le_half_threehalf hO hD hF a b F G x

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
