import Calderon.ActualFiniteHarmonicModelScalarExpansionClosure
import Calderon.ActualFiniteHarmonicModelScalarExpansionProducts

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma hasCoreScalarExpansionBound_generator (hF : SphereFischerInner)
    (i : CoreAngularGeneratorIndex) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (coreAngularGenerator hO hD hF i) x 1 := by
  simpa only [coreScalar_const_mul_eq_smul,one_smul,abs_one] using
    hasCoreScalarExpansionBound_single hO hD (coreAngularGenerator hO hD hF) i
      (fun _ => (1 : ℝ)) contDiff_const x

lemma hasCoreScalarExpansionBound_identity (hF : SphereFischerInner) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF) 1 x 1 := by
  exact hasCoreScalarExpansionBound_generator hO hD hF (Sum.inr (Sum.inr (Sum.inr false))) x

lemma hasCoreScalarExpansionBound_coreScalar (hF : SphereFischerInner)
    (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (coreScalar hO hD c hc) x |c x| := by
  have ht := hasCoreScalarExpansionBound_single hO hD (coreAngularGenerator hO hD hF)
    (Sum.inr (Sum.inr (Sum.inr false))) c hc x
  simpa only [coreAngularGenerator,mul_one] using ht

lemma hasCoreScalarExpansionBound_linear_to_quadratic (hF : SphereFischerInner)
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF) A x C) :
    HasCoreScalarExpansionBound hO hD
      (fun p : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF p.1*coreAngularGenerator hO hD hF p.2) A x C := by
  simpa only [mul_one] using hasCoreScalarExpansionBound_product hO hD
    (coreAngularGenerator hO hD hF) (coreAngularGenerator hO hD hF)
    (scalarCentral_coreAngularGenerator hO hD hF) A 1 x C 1 hA
    (hasCoreScalarExpansionBound_identity hO hD hF x)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
