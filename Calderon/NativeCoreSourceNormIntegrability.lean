import Calderon.ActualFiniteHarmonicCoreWeights
import Calderon.SectionFiveErrorForms
import Calderon.ActualFiniteHarmonicCoreBase

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph PrincipalCommutator
  ReferenceDensityBounds SectionFiveErrorForms WeightedBaseSpectral
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev NativeSourceNormFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] NativeSourceNormFunction

theorem integrable_native_core_weighted_norm_sq
    (c : R3 → ℝ) (hc : Continuous c) (F : smoothCompactFiniteSphereCore hO hD) :
    Integrable (fun x => c x * ‖F x‖^2) := by
  have hSquare : HasCompactSupport (fun x => ‖F x‖^2) :=
    F.property.2.1.comp_left (g := fun u : SphereL2 => ‖u‖^2) (by simp)
  exact (hc.mul (F.property.1.continuous.norm.pow 2)).integrable_of_hasCompactSupport
    hSquare.mul_left

theorem integrable_native_core_density_pair
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) * ⟪F x,G x⟫_ℝ) := by
  have hPair : Continuous (fun x => ⟪F x,G x⟫_ℝ) :=
    F.property.1.continuous.inner G.property.1.continuous
  have hSupport : HasCompactSupport (fun x => ⟪F x,G x⟫_ℝ) :=
    HasCompactSupport.intro G.property.2.1 (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx,inner_zero_right])
  exact ((continuous_referenceBaseDensity g hg L lam).mul hPair).integrable_of_hasCompactSupport
    hSupport.mul_left

theorem integrable_native_core_source_norm
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (beta : R3 → ℝ) (hbeta : Continuous beta) (hpos : ∀ x, 0 < beta x)
    (F : smoothCompactFiniteSphereCore hO hD) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      sourceNormSquareIntegrand (beta x)
        (fun j : Fin 3 => coreDirectionalDerivative hO hD (coordinateDirection j) F x)
        (coreWeightOperator hO hD (besselWeight 1) F x)
        (fun j : Fin 3 => coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
          (coreDirectionalDerivative hO hD (coordinateDirection j) F) x)
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x)) := by
  have hrho := continuous_referenceBaseDensity g hg L lam
  have hinv : Continuous (fun x => (beta x)⁻¹) := hbeta.inv₀ (fun x => (hpos x).ne')
  have hZero : Integrable (fun x => ∑ j : Fin 3,
      referenceDensityFamily g L (lam,x) *
        ‖coreDirectionalDerivative hO hD (coordinateDirection j) F x‖^2) :=
    integrable_finsetSum _ (fun j _ => integrable_native_core_weighted_norm_sq hO hD
      _ hrho (coreDirectionalDerivative hO hD (coordinateDirection j) F))
  have hOne : Integrable (fun x =>
      (referenceDensityFamily g L (lam,x) * (beta x)^2) *
        ‖coreWeightOperator hO hD (besselWeight 1) F x‖^2) :=
    integrable_native_core_weighted_norm_sq hO hD _ (hrho.mul (hbeta.pow 2)) _
  have hHalf : Integrable (fun x => ∑ j : Fin 3,
      (referenceDensityFamily g L (lam,x) * (beta x)⁻¹) *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
          (coreDirectionalDerivative hO hD (coordinateDirection j) F) x‖^2) :=
    integrable_finsetSum _ (fun j _ => integrable_native_core_weighted_norm_sq hO hD
      _ (hrho.mul hinv) _)
  have hThree : Integrable (fun x => (referenceDensityFamily g L (lam,x) * beta x) *
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖^2) :=
    integrable_native_core_weighted_norm_sq hO hD _ (hrho.mul hbeta) _
  apply (((hZero.add hOne).add hHalf).add hThree).congr
  apply Filter.Eventually.of_forall
  intro x
  simp only [Pi.add_apply,sourceNormSquareIntegrand,mul_add,Finset.mul_sum,mul_assoc]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
