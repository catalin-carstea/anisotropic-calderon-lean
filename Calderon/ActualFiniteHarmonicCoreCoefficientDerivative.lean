import Calderon.ActualFiniteHarmonicCoreScalarCentral
import Calderon.ActualFiniteHarmonicCoreLeibniz

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  BoundedAngularShift AngularShiftGraph HarmonicDerivativeOperator PrincipalCommutator
  ActualReferenceDDSpectralTransport ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeDerivativeFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeDerivativeFunction

lemma coefficientDerivative_coreCoefficientAction (v : R3) (A : R3 → SphereL2 →L[ℝ] SphereL2) (hA : ContDiff ℝ ∞ A)
    (hgraph : ∀ x, PreservesSphereSpectralGraphs hO hD (A x)):
    coefficientDerivative (coreDirectionalDerivative hO hD v)
      (coreCoefficientAction hO hD A hA hgraph) =
    coreCoefficientAction hO hD (directionalFDeriv v A)
      (contDiff_directionalFDeriv v A hA)
      (fun x => preservesSphereSpectralGraphs_directionalFDeriv hO hD A hA hgraph x v) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  simp only [coefficientDerivative, ActualModelCommutatorWords.commutator, Module.End.mul_apply,
    LinearMap.sub_apply, coreDirectionalDerivative, coreCoefficientAction,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk, Submodule.coe_sub, Pi.sub_apply]
  rw [directionalFDeriv_clm_apply v A (F : R3 → SphereL2) hA F.property.1 x]
  abel

lemma coefficientDerivative_second_coreCoefficientAction (v w : R3) (A : R3 → SphereL2 →L[ℝ] SphereL2)
    (hA : ContDiff ℝ ∞ A)
    (hgraph : ∀ x, PreservesSphereSpectralGraphs hO hD (A x)) :
    coefficientDerivative (coreDirectionalDerivative hO hD v)
      (coefficientDerivative (coreDirectionalDerivative hO hD w)
        (coreCoefficientAction hO hD A hA hgraph)) =
    coreCoefficientAction hO hD (directionalFDeriv v (directionalFDeriv w A))
      (contDiff_directionalFDeriv v _ (contDiff_directionalFDeriv w A hA))
      (fun x => preservesSphereSpectralGraphs_directionalFDeriv hO hD _
        (contDiff_directionalFDeriv w A hA)
        (fun y => preservesSphereSpectralGraphs_directionalFDeriv hO hD A hA hgraph y w) x v) := by
  rw [coefficientDerivative_coreCoefficientAction,
    coefficientDerivative_coreCoefficientAction]

lemma coreDirectionalDerivative_normalizedDerivative_commute (v : R3) (hF : SphereFischerInner) (i : Fin 3) :
    Commute (coreDirectionalDerivative hO hD v) (coreNormalizedDerivative hO hD hF i) := by
  change coreDirectionalDerivative hO hD v * coreNormalizedDerivative hO hD hF i =
    coreNormalizedDerivative hO hD hF i * coreDirectionalDerivative hO hD v
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change directionalFDeriv v (fun y => normalizedDerivative hF hO hD i (F y)) x =
    normalizedDerivative hF hO hD i (directionalFDeriv v (F : R3 → SphereL2) x)
  have he := directionalFDeriv_clm_apply v
    (fun _ : R3 => normalizedDerivative hF hO hD i) (F : R3 → SphereL2)
    contDiff_const F.property.1 x
  simpa only [directionalFDeriv, fderiv_const_apply, ContinuousLinearMap.zero_apply,
    zero_add] using he

lemma coreDirectionalDerivative_normalizedRaising_commute (v : R3) (hF : SphereFischerInner) (i : Fin 3) :
    Commute (coreDirectionalDerivative hO hD v) (coreNormalizedRaising hO hD hF i) := by
  change coreDirectionalDerivative hO hD v * coreNormalizedRaising hO hD hF i =
    coreNormalizedRaising hO hD hF i * coreDirectionalDerivative hO hD v
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change directionalFDeriv v (fun y => normalizedRaising hF hO hD i (F y)) x =
    normalizedRaising hF hO hD i (directionalFDeriv v (F : R3 → SphereL2) x)
  have he := directionalFDeriv_clm_apply v
    (fun _ : R3 => normalizedRaising hF hO hD i) (F : R3 → SphereL2)
    contDiff_const F.property.1 x
  simpa only [directionalFDeriv, fderiv_const_apply, ContinuousLinearMap.zero_apply,
    zero_add] using he

lemma commutator_commutator_right_identity {AType : Type*} [Ring AType] (d A S : AType) :
    commutator (commutator d A) S =
      commutator d (commutator A S) - commutator A (commutator d S) := by
  unfold ActualModelCommutatorWords.commutator
  noncomm_ring

lemma scalarCentral_coefficientDerivative (v : R3) (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hA : ScalarCentral hO hD A) :
    ScalarCentral hO hD (coefficientDerivative (coreDirectionalDerivative hO hD v) A) := by
  intro c hc
  let d := coreDirectionalDerivative hO hD v
  let S := coreScalar hO hD c hc
  have hAS : commutator A S = 0 := sub_eq_zero.mpr (hA c hc).eq
  have hder := coefficientDerivative_coreScalar hO hD v c hc
  have hADS : commutator A (commutator d S) = 0 := by
    change commutator A
      (coefficientDerivative (coreDirectionalDerivative hO hD v) (coreScalar hO hD c hc)) = 0
    rw [hder]
    exact sub_eq_zero.mpr (hA (directionalFDeriv v c) (contDiff_directionalFDeriv v c hc)).eq
  change coefficientDerivative d A * S = S * coefficientDerivative d A
  apply sub_eq_zero.mp
  change commutator (commutator d A) S = 0
  rw [commutator_commutator_right_identity, hAS, hADS]
  simp only [ActualModelCommutatorWords.commutator, mul_zero, zero_mul, sub_self, sub_zero]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
