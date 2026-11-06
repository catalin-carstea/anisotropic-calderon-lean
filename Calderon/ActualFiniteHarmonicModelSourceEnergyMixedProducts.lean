import Calderon.ActualFiniteHarmonicModelAngularZeroEnergyIntegral

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  SectionFiveErrorForms ReferenceDensityBounds BaseDensityAdjoint
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev sourceMixedEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] sourceMixedEnergyFunction

lemma beta_mul_threehalf_norm_sq_le_finiteCoreSourceEnergy
    (beta : ℝ) (hb : 0 ≤ beta) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    beta * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖^2 ≤
      finiteCoreSourceEnergy hO hD beta F x := by
  let H (k : Fin 3) := coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
    (coreDirectionalDerivative hO hD (coordinateDirection k) F) x
  let V := coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x
  have he : beta⁻¹*(∑ k, ‖H k‖^2)+beta*‖V‖^2 ≤
      finiteCoreSourceEnergy hO hD beta F x :=
    angular_error_terms_le_sourceNormSquareIntegrand beta _ _ _ _
  have hn : 0 ≤ beta⁻¹*(∑ k, ‖H k‖^2) :=
    mul_nonneg (inv_nonneg.mpr hb) (Finset.sum_nonneg (fun k _ => sq_nonneg ‖H k‖))
  change beta*‖V‖^2 ≤ _
  linarith

lemma norm_gradient_half_mul_threehalf_le_finiteCoreSourceEnergy
    (beta : ℝ) (hb : 0 < beta) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (j : Fin 3) :
    ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
      (coreDirectionalDerivative hO hD (coordinateDirection j) F) x‖ *
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ ≤
      finiteCoreSourceEnergy hO hD beta F x := by
  let H (k : Fin 3) := coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
    (coreDirectionalDerivative hO hD (coordinateDirection k) F) x
  let V := coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x
  calc
    _ ≤ beta⁻¹*‖H j‖^2+beta*‖V‖^2 := mul_le_weighted_sq beta ‖H j‖ ‖V‖ hb
    _ ≤ beta⁻¹*(∑ k, ‖H k‖^2)+beta*‖V‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_sq_le_sum H j) (inv_nonneg.mpr hb.le)) le_rfl
    _ ≤ _ := angular_error_terms_le_sourceNormSquareIntegrand beta _ _ _ _

lemma beta_mul_half_threehalf_le_finiteCoreSourceEnergy
    (beta : ℝ) (hb : 0 ≤ beta) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    beta * (‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖) ≤
      finiteCoreSourceEnergy hO hD beta F x := by
  have hh := norm_bessel_half_le_threehalf hO hD (F x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x)
    (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x)
    (coreWeightOperator_graph hO hD (besselWeight (3/2 : ℝ)) F x)
  calc
    _ ≤ beta*(‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh (norm_nonneg _)) hb
    _ = beta*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖^2 := by rw [pow_two]
    _ ≤ _ := beta_mul_threehalf_norm_sq_le_finiteCoreSourceEnergy hO hD beta hb F x

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
