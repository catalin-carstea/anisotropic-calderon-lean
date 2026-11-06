import Calderon.ActualFiniteHarmonicModelHBHalfBounds
import Calderon.SectionFiveNormalizedSecondForm
import Calderon.SectionFiveErrorBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  SectionFiveErrorForms ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeSourceEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeSourceEnergyFunction

def finiteCoreSourceEnergy (beta : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  sourceNormSquareIntegrand beta
    (fun k : Fin 3 => coreDirectionalDerivative hO hD (coordinateDirection k) F x)
    (coreWeightOperator hO hD (besselWeight 1) F x)
    (fun k : Fin 3 => coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
      (coreDirectionalDerivative hO hD (coordinateDirection k) F) x)
    (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x)

lemma finiteCoreSourceEnergy_nonneg (beta : ℝ) (hb : 0 ≤ beta)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    0 ≤ finiteCoreSourceEnergy hO hD beta F x :=
  sourceNormSquareIntegrand_nonneg beta hb _ _ _ _

lemma norm_half_mul_gradient_half_le_finiteCoreSourceEnergy
    (beta : ℝ) (hb : 0 < beta) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (j : Fin 3) :
    ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (coreDirectionalDerivative hO hD (coordinateDirection j) F) x‖ ≤
      finiteCoreSourceEnergy hO hD beta F x := by
  let H (k : Fin 3) := coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
    (coreDirectionalDerivative hO hD (coordinateDirection k) F) x
  let V := coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x
  have hhalf := norm_bessel_half_le_threehalf hO hD (F x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x) V
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x)
    (coreWeightOperator_graph hO hD (besselWeight (3/2 : ℝ)) F x)
  calc
    _ ≤ ‖V‖ * ‖H j‖ := mul_le_mul_of_nonneg_right hhalf (norm_nonneg _)
    _ = ‖H j‖ * ‖V‖ := mul_comm _ _
    _ ≤ beta⁻¹ * ‖H j‖^2 + beta * ‖V‖^2 :=
      mul_le_weighted_sq beta ‖H j‖ ‖V‖ hb
    _ ≤ beta⁻¹ * (∑ k, ‖H k‖^2) + beta * ‖V‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_sq_le_sum H j) (inv_nonneg.mpr hb.le)) le_rfl
    _ ≤ _ := angular_error_terms_le_sourceNormSquareIntegrand beta _ _ _ _

lemma inv_beta_mul_gradient_norms_le_finiteCoreSourceEnergy
    (beta : ℝ) (hb : 0 ≤ beta) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (i j : Fin 3) :
    beta⁻¹ * (‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
      (coreDirectionalDerivative hO hD (coordinateDirection i) F) x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (coreDirectionalDerivative hO hD (coordinateDirection j) F) x‖) ≤
      finiteCoreSourceEnergy hO hD beta F x := by
  let H (k : Fin 3) := coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
    (coreDirectionalDerivative hO hD (coordinateDirection k) F) x
  calc
    _ ≤ beta⁻¹ * (∑ k, ‖H k‖^2) :=
      mul_le_mul_of_nonneg_left (norm_mul_norm_le_sum H i j) (inv_nonneg.mpr hb)
    _ ≤ _ := weighted_gradient_square_le_sourceNormSquareIntegrand beta hb _ _ _ _

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
