import Calderon.ActualFiniteHarmonicCoreBase
import Calderon.BaseDensityAdjoint
import Calderon.ReferenceDensityBounds

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore PrincipalCommutator ReferenceDensityBounds
  BaseDensityAdjoint
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev NativeCoreDensityIBPFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] NativeCoreDensityIBPFunction

theorem native_core_referenceDensity_integration_by_parts
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (i : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪coreDirectionalDerivative hO hD (coordinateDirection i) F x,G x⟫_ℝ) =
      -(∫ x, referenceDensityFamily g L (lam,x) *
        ⟪F x,coreDirectionalDerivative hO hD (coordinateDirection i) G x⟫_ℝ) -
      ∫ x, directionalFDeriv (coordinateDirection i)
        (fun y => referenceDensityFamily g L (lam,y)) x * ⟪F x,G x⟫_ℝ := by
  let rho : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)
  let v := coordinateDirection i
  have hrho : ContDiff ℝ ∞ rho :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hdrho : ContDiff ℝ ∞ (directionalFDeriv v rho) :=
    contDiff_directionalFDeriv v rho hrho
  have hFirst : Integrable (fun x => rho x *
      ⟪F x,coreDirectionalDerivative hO hD v G x⟫_ℝ) := by
    have hi := compact_inner_integrable (fun x => rho x • F x)
      (coreDirectionalDerivative hO hD v G : R3 → SphereL2)
      (hrho.smul F.property.1).continuous
      (coreDirectionalDerivative hO hD v G).property.1.continuous
      (coreDirectionalDerivative hO hD v G).property.2.1
    simpa only [inner_smul_left,starRingEnd_apply,star_trivial] using hi
  have hDensity : Integrable (fun x => directionalFDeriv v rho x * ⟪F x,G x⟫_ℝ) := by
    have hi := compact_inner_integrable (fun x => directionalFDeriv v rho x • F x)
      (G : R3 → SphereL2) (hdrho.smul F.property.1).continuous
      G.property.1.continuous G.property.2.1
    simpa only [inner_smul_left,starRingEnd_apply,star_trivial] using hi
  have hParts : (∫ x, rho x * ⟪coreDirectionalDerivative hO hD v F x,G x⟫_ℝ) =
      -(∫ x, ⟪directionalFDeriv v (fun y => rho y • G y) x,F x⟫_ℝ) := by
    simpa only [mul_one,BaseDensityAdjoint.directionalDeriv,PrincipalCommutator.directionalFDeriv,
      coreDirectionalDerivative,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk] using
      compact_weighted_first_adjoint v rho (fun _ => (1 : ℝ))
        (F : R3 → SphereL2) (G : R3 → SphereL2)
        hrho contDiff_const F.property.1 G.property.1 F.property.2.1
  have hExpand : (fun x => ⟪directionalFDeriv v (fun y => rho y • G y) x,F x⟫_ℝ) =
      fun x => rho x * ⟪F x,coreDirectionalDerivative hO hD v G x⟫_ℝ +
        directionalFDeriv v rho x * ⟪F x,G x⟫_ℝ := by
    funext x
    change ⟪directionalFDeriv v (fun y => rho y • G y) x,F x⟫_ℝ =
      rho x * ⟪F x,directionalFDeriv v (G : R3 → SphereL2) x⟫_ℝ +
        directionalFDeriv v rho x * ⟪F x,G x⟫_ℝ
    rw [directionalFDeriv_smul v rho (G : R3 → SphereL2) hrho G.property.1 x]
    simp only [inner_add_left,inner_smul_left,starRingEnd_apply,star_trivial]
    rw [real_inner_comm (G x) (F x),
      real_inner_comm (directionalFDeriv v (G : R3 → SphereL2) x) (F x)]
    ring
  change (∫ x, rho x * ⟪coreDirectionalDerivative hO hD v F x,G x⟫_ℝ) =
    -(∫ x, rho x * ⟪F x,coreDirectionalDerivative hO hD v G x⟫_ℝ) -
      ∫ x, directionalFDeriv v rho x * ⟪F x,G x⟫_ℝ
  rw [hParts,hExpand,integral_add hFirst hDensity]
  ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
