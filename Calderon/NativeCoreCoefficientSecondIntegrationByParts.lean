import Calderon.NativeCoreReferenceDensityIntegrationByParts
import Calderon.NativeCoreSourceNormIntegrability
import Calderon.ActualModelCommutatorWords

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore PrincipalCommutator ReferenceDensityBounds
  ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev NativeCoreSecondIBPFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] NativeCoreSecondIBPFunction

theorem native_core_coefficient_second_integration_by_parts
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (i k : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪T (coreDirectionalDerivative hO hD (coordinateDirection i)
        (coreDirectionalDerivative hO hD (coordinateDirection k) F)) x,G x⟫_ℝ) =
      -(∫ x, referenceDensityFamily g L (lam,x) *
        ⟪T (coreDirectionalDerivative hO hD (coordinateDirection k) F) x,
          coreDirectionalDerivative hO hD (coordinateDirection i) G x⟫_ℝ) -
      (∫ x, referenceDensityFamily g L (lam,x) *
        ⟪(coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i)) T)
          (coreDirectionalDerivative hO hD (coordinateDirection k) F) x,G x⟫_ℝ) -
      ∫ x, directionalFDeriv (coordinateDirection i)
        (fun y => referenceDensityFamily g L (lam,y)) x *
        ⟪T (coreDirectionalDerivative hO hD (coordinateDirection k) F) x,G x⟫_ℝ := by
  let rho : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)
  let d := coreDirectionalDerivative hO hD (coordinateDirection i)
  let U := coreDirectionalDerivative hO hD (coordinateDirection k) F
  let S := coefficientDerivative d T
  have hAlg : T (d U) = d (T U) - S U := by
    change T (d U) = d (T U) - (d (T U) - T (d U))
    abel
  have hValue (x : R3) : T (d U) x = d (T U) x - S U x :=
    congrArg (fun V : smoothCompactFiniteSphereCore hO hD => V x) hAlg
  have hSplit : (fun x => rho x * ⟪T (d U) x,G x⟫_ℝ) =
      fun x => rho x * ⟪d (T U) x,G x⟫_ℝ - rho x * ⟪S U x,G x⟫_ℝ := by
    funext x
    rw [hValue x,inner_sub_left,mul_sub]
  have hFirst : Integrable (fun x => rho x * ⟪d (T U) x,G x⟫_ℝ) :=
    integrable_native_core_density_pair hO hD g hg L lam (d (T U)) G
  have hSecond : Integrable (fun x => rho x * ⟪S U x,G x⟫_ℝ) :=
    integrable_native_core_density_pair hO hD g hg L lam (S U) G
  have hParts := native_core_referenceDensity_integration_by_parts hO hD g hg L lam i (T U) G
  change (∫ x, rho x * ⟪d (T U) x,G x⟫_ℝ) =
    -(∫ x, rho x * ⟪T U x,d G x⟫_ℝ) -
      ∫ x, directionalFDeriv (coordinateDirection i) rho x * ⟪T U x,G x⟫_ℝ at hParts
  change (∫ x, rho x * ⟪T (d U) x,G x⟫_ℝ) =
    -(∫ x, rho x * ⟪T U x,d G x⟫_ℝ) -
      (∫ x, rho x * ⟪S U x,G x⟫_ℝ) -
      ∫ x, directionalFDeriv (coordinateDirection i) rho x * ⟪T U x,G x⟫_ℝ
  rw [hSplit,integral_sub hFirst hSecond,hParts]
  ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
