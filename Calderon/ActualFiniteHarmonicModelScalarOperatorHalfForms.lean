import Calderon.ActualFiniteHarmonicCoreCoefficientDerivative
import Calderon.ActualFiniteHarmonicModelSourceEnergy

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph PrincipalCommutator
  ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev scalarOperatorHalfFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] scalarOperatorHalfFunction

lemma coefficientDerivative_coreScalar_mul (v : R3) (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c)
    (T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) :
    coefficientDerivative (coreDirectionalDerivative hO hD v) (coreScalar hO hD c hc*T) =
      coreScalar hO hD (directionalFDeriv v c) (contDiff_directionalFDeriv v c hc)*T +
      coreScalar hO hD c hc*coefficientDerivative (coreDirectionalDerivative hO hD v) T := by
  have he {R : Type} [Ring R] (d A B : R) :
      coefficientDerivative d (A*B) = coefficientDerivative d A*B+A*coefficientDerivative d B := by
    unfold coefficientDerivative ActualModelCommutatorWords.commutator
    noncomm_ring
  rw [he,coefficientDerivative_coreScalar]

lemma abs_inner_coreScalar_mul_le_half_forms
    (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c)
    (T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (U V : smoothCompactFiniteSphereCore hO hD) (x : R3) (B : ℝ)
    (hT : |⟪T U x,V x⟫_ℝ| ≤ B*
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖) :
    |⟪(coreScalar hO hD c hc*T) U x,V x⟫_ℝ| ≤ (|c x| *B)*
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖ := by
  change |⟪c x • T U x,V x⟫_ℝ| ≤ _
  rw [real_inner_smul_left,abs_mul]
  calc
    _ ≤ |c x| *(B*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖) :=
      mul_le_mul_of_nonneg_left hT (abs_nonneg _)
    _ = _ := by ring

lemma abs_inner_coefficientDerivative_coreScalar_mul_le_half_forms
    (v : R3) (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c)
    (T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (U V : smoothCompactFiniteSphereCore hO hD) (x : R3) (B0 B1 : ℝ)
    (hT : |⟪T U x,V x⟫_ℝ| ≤ B0*
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖)
    (hDT : |⟪coefficientDerivative (coreDirectionalDerivative hO hD v) T U x,V x⟫_ℝ| ≤ B1*
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖) :
    |⟪coefficientDerivative (coreDirectionalDerivative hO hD v) (coreScalar hO hD c hc*T) U x,V x⟫_ℝ| ≤
      (|directionalFDeriv v c x| *B0+|c x| *B1)*
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖ := by
  rw [coefficientDerivative_coreScalar_mul]
  simp only [LinearMap.add_apply,Submodule.coe_add,Pi.add_apply,inner_add_left]
  calc
    _ ≤ |⟪(coreScalar hO hD (directionalFDeriv v c) (contDiff_directionalFDeriv v c hc)*T) U x,V x⟫_ℝ| +
        |⟪(coreScalar hO hD c hc*coefficientDerivative (coreDirectionalDerivative hO hD v) T) U x,V x⟫_ℝ| := abs_add_le _ _
    _ ≤ (|directionalFDeriv v c x| *B0)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖ +
        (|c x| *B1)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖ :=
      add_le_add (abs_inner_coreScalar_mul_le_half_forms hO hD _ _ T U V x B0 hT)
        (abs_inner_coreScalar_mul_le_half_forms hO hD c hc _ U V x B1 hDT)
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
