import Calderon.ActualFiniteHarmonicCoreDerivative
import Calderon.ActualFiniteHarmonicCoreRaising
import Calderon.AngularWeightedCore

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph AngularWeightedCore
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeHalfShiftNormFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeHalfShiftNormFunction
lemma norm_coreWeight_half_derivative_le
    (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF i F) x‖ ≤
      2 * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := by
  have hw : (F x,coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) ∈
      sphereBesselGraph hO hD ((1/2 : ℝ)+1) := by
    simpa only [sphereBesselGraph,show (1/2 : ℝ)+1=3/2 by norm_num] using
      coreWeightOperator_graph hO hD (besselWeight (3/2 : ℝ)) F x
  have ht := norm_sq_weighted_derivative_le hF hO hD i (1/2 : ℝ) (by norm_num)
    (F x) (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x)
    (coreDerivative hO hD hF i F x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF i F) x)
    hw (coreDerivative_graph hO hD hF i F x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF i F) x)
  nlinarith [norm_nonneg (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF i F) x),
    norm_nonneg (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x)]


lemma norm_coreWeight_half_raising_le
    (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreRaising hO hD hF i F) x‖ ≤
      (2 * (2 : ℝ)^(1/2 : ℝ)) * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := by
  have hw : (F x,coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) ∈
      sphereBesselGraph hO hD ((1/2 : ℝ)+1) := by
    simpa only [sphereBesselGraph,show (1/2 : ℝ)+1=3/2 by norm_num] using
      coreWeightOperator_graph hO hD (besselWeight (3/2 : ℝ)) F x
  have ht := norm_sq_weighted_raising_le hF hO hD i (1/2 : ℝ) (by norm_num)
    (F x) (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x)
    (coreRaising hO hD hF i F x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreRaising hO hD hF i F) x)
    hw (coreRaising_graph hO hD hF i F x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) (coreRaising hO hD hF i F) x)
  have hc : 0 ≤ 2*(2 : ℝ)^(1/2 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  have hn : 0 ≤ (2*(2 : ℝ)^(1/2 : ℝ))*
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := mul_nonneg hc (norm_nonneg _)
  nlinarith [norm_nonneg (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreRaising hO hD hF i F) x)]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
