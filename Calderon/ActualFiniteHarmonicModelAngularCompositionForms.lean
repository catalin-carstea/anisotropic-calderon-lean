import Calderon.ActualFiniteHarmonicModelReversedAngularShiftForms
import Calderon.ActualFiniteHarmonicModelAngularSecondEnergyPointwise

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SpectralCoreRegularity
  BoundedAngularShift BalancedAngularShift AngularShiftGraph ActualReferenceDDSpectralTransport
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularCompositionFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularCompositionFunction

lemma abs_inner_preserving_weight_derivative_le_half_threehalf
    (hF : SphereFischerInner) (a : Fin 3) (M : SphereL2 →L[ℝ] SphereL2)
    (hM : PreservesSphereSpectralGraphs hO hD M)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪M (coreWeightOperator hO hD (besselWeight 1)
        (coreDerivative hO hD hF a F) x),G x⟫_ℝ| ≤
      (4*‖M‖)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  let A := M.adjoint
  have hA : PreservesSphereSpectralGraphs hO hD A :=
    preservesSphereSpectralGraphs_adjoint hO hD M hM
  have hG : (coreWeightOperator hO hD (besselWeight 1) G x,
      coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x) ∈
      sphereBesselGraph hO hD (1/2 : ℝ) := by
    rw [← coreWeight_half_one_apply hO hD G x]
    exact coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ))
      (coreWeightOperator hO hD (besselWeight 1) G) x
  have he : ⟪M (coreWeightOperator hO hD (besselWeight 1)
      (coreDerivative hO hD hF a F) x),G x⟫_ℝ =
      ⟪coreDerivative hO hD hF a F x,A (coreWeightOperator hO hD (besselWeight 1) G x)⟫_ℝ := by
    rw [← M.adjoint_inner_right]
    exact spectralGraph_inner_symm hO hD (besselWeight 1)
      (coreDerivative hO hD hF a F x)
      (coreWeightOperator hO hD (besselWeight 1) (coreDerivative hO hD hF a F) x)
      (A (G x)) (A (coreWeightOperator hO hD (besselWeight 1) G x))
      (coreWeightOperator_graph hO hD (besselWeight 1) (coreDerivative hO hD hF a F) x)
      (hA _ _ _ (coreWeightOperator_graph hO hD (besselWeight 1) G x))
  rw [he]
  have hp := abs_inner_derivative_le_half_norm hF hO hD a (F x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x)
    (coreDerivative hO hD hF a F x)
    (A (coreWeightOperator hO hD (besselWeight 1) G x))
    (A (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x))
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x)
    (coreDerivative_graph hO hD hF a F x) (hA _ _ _ hG)
  have hn : ‖A (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x)‖ ≤
      ‖M‖*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
    have hnorm : ‖M.adjoint‖ = ‖M‖ :=
      (ContinuousLinearMap.adjoint : (SphereL2 →L[ℝ] SphereL2) ≃ₗᵢ[ℝ]
        (SphereL2 →L[ℝ] SphereL2)).norm_map M
    simpa only [A,hnorm] using
      A.le_opNorm (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x)
  calc
    _ ≤ 4*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      ‖A (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x)‖ := hp
    _ ≤ 4*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      (‖M‖*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖) :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg (by norm_num) (norm_nonneg _))
    _ = _ := by ring

lemma abs_inner_raising_derivative_le_half_threehalf
    (hF : SphereFischerInner) (a b : Fin 3)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪coreRaising hO hD hF b (coreDerivative hO hD hF a F) x,G x⟫_ℝ| ≤
      8*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  have he : ⟪coreRaising hO hD hF b (coreDerivative hO hD hF a F) x,G x⟫_ℝ =
      ⟪coreDerivative hO hD hF a F x,coreDerivative hO hD hF b G x⟫_ℝ := by
    have ht := sphereDerivativeGraph_inner_adjoint hF hO hD b
      (G x) (coreDerivative hO hD hF b G x)
      (coreDerivative hO hD hF a F x)
      (coreRaising hO hD hF b (coreDerivative hO hD hF a F) x)
      (coreDerivative_graph hO hD hF b G x)
      (coreRaising_graph hO hD hF b (coreDerivative hO hD hF a F) x)
    simpa only [real_inner_comm] using ht.symm
  rw [he]
  have hp := abs_inner_coreDerivative_le_half hO hD hF a F (coreDerivative hO hD hF b G) x
  have hn := norm_coreWeight_half_derivative_le hO hD hF b G x
  calc
    _ ≤ 4*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF b G) x‖ := hp
    _ ≤ 4*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      (2*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖) :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg (by norm_num) (norm_nonneg _))
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
