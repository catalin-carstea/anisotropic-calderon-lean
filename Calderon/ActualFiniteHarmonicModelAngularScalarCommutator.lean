import Calderon.ActualFiniteHarmonicModelAngularGenerators
import Calderon.ActualFiniteHarmonicCoreScalarCentral

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularScalarCommutatorFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularScalarCommutatorFunction

lemma scalarCentral_coreAngularGenerator (hF : SphereFischerInner) (i : CoreAngularGeneratorIndex) :
    ScalarCentral hO hD (coreAngularGenerator hO hD hF i) := by
  rcases i with a | (a | (ab | b))
  · exact scalarCentral_coreDerivative hO hD hF a
  · exact scalarCentral_coreRaising hO hD hF a
  · exact scalarCentral_coreRotation hO hD ab.1 ab.2
  · cases b with
    | false => exact fun c hc => Commute.one_left _
    | true => exact scalarCentral_coreWeightOperator hO hD _

lemma coreAngular_scalar_commutator_eq
    (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hA : ScalarCentral hO hD A) (hB : ScalarCentral hO hD B)
    (c d : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d) :
    commutator (coreScalar hO hD c hc*A) (coreScalar hO hD d hd*B) =
      coreScalar hO hD c hc*coreScalar hO hD d hd*commutator A B := by
  have halg {R : Type} [Ring R] (a b c d : R)
      (had : Commute a d) (hbc : Commute b c) (hcd : Commute c d) :
      ActualModelCommutatorWords.commutator (c*a) (d*b) =
        c*d*ActualModelCommutatorWords.commutator a b := by
    have h1 : (c*a)*(d*b) = c*d*(a*b) := by
      calc
        _ = c*(a*d)*b := by noncomm_ring
        _ = c*(d*a)*b := by rw [had.eq]
        _ = _ := by noncomm_ring
    have h2 : (d*b)*(c*a) = c*d*(b*a) := by
      calc
        _ = d*(b*c)*a := by noncomm_ring
        _ = d*(c*b)*a := by rw [hbc.eq]
        _ = (d*c)*(b*a) := by noncomm_ring
        _ = _ := by rw [hcd.eq]
    unfold ActualModelCommutatorWords.commutator
    rw [h1,h2]
    noncomm_ring
  exact halg A B _ _ (hA d hd) (hB c hc) (scalarCentral_coreScalar hO hD c hc d hd)

lemma abs_inner_coreAngular_scalar_commutator
    (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hA : ScalarCentral hO hD A) (hB : ScalarCentral hO hD B)
    (c d : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪commutator (coreScalar hO hD c hc*A) (coreScalar hO hD d hd*B) F x,G x⟫_ℝ| =
      |c x| *|d x| *|⟪commutator A B F x,G x⟫_ℝ| := by
  rw [coreAngular_scalar_commutator_eq hO hD A B hA hB c d hc hd]
  change |⟪c x • (d x • commutator A B F x),G x⟫_ℝ| = _
  rw [real_inner_smul_left,real_inner_smul_left,abs_mul,abs_mul]
  ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
