import Calderon.ActualFiniteHarmonicModelPrincipalZScalarAction
import Calderon.SectionFiveErrorForms

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  BaseDensityAdjoint SectionFiveErrorForms
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeAngularScalarOnePartsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeAngularScalarOnePartsFunction

theorem coreDerivative_secondBase_scalar_one_parts
    (hF : SphereFischerInner) (a : Fin 3) (i j : R3)
    (mu c : R3 → ℝ) (hm : ContDiff ℝ ∞ mu) (hc : ContDiff ℝ ∞ c)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    (∫ x : R3, mu x * c x * ⟪coreDerivative hO hD hF a
      (coreDirectionalDerivative hO hD i (coreDirectionalDerivative hO hD j F)) x,G x⟫_ℝ) =
      -(∫ x : R3, directionalDeriv i (fun y => mu y * c y) x *
        ⟪G x,coreDerivative hO hD hF a (coreDirectionalDerivative hO hD j F) x⟫_ℝ) -
      (∫ x : R3, mu x * c x *
        ⟪coreDirectionalDerivative hO hD i G x,
          coreDerivative hO hD hF a (coreDirectionalDerivative hO hD j F) x⟫_ℝ) := by
  have hparts := compact_second_form_one_parts_expanded i j mu c
    (coreDerivative hO hD hF a F : R3 → SphereL2) (G : R3 → SphereL2)
    hm hc (coreDerivative hO hD hF a F).property.1 G.property.1
    (coreDerivative hO hD hF a F).property.2.1
  have hfirst (x : R3) : directionalDeriv j
      (coreDerivative hO hD hF a F : R3 → SphereL2) x =
      coreDerivative hO hD hF a (coreDirectionalDerivative hO hD j F) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreDirectionalDerivative_coreDerivative_commute hO hD hF j a).eq
  simp only [← coreDerivative_secondBaseDerivative_apply hO hD hF a i j F,
    hfirst] at hparts
  simpa only [coreDirectionalDerivative,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
    BaseDensityAdjoint.directionalDeriv,PrincipalCommutator.directionalFDeriv] using hparts

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
