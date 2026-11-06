import Calderon.ActualFiniteHarmonicModelScalarOperatorHalfForms
import Calderon.ActualFiniteHarmonicModelAngularGenerators
import Calderon.ActualFiniteHarmonicModelScalarExpansion
import Calderon.ActualFiniteHarmonicModelCoefficientCore

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SphereHilbertDecomposition
  SpectralWeightedGraph PrincipalCommutator ActualModelCommutatorWords SmoothSphereRotationProjection
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularBaseCommutationFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] angularBaseCommutationFunction

lemma coreBlockOperator_directionalDerivative_commute
    (K : ∀ k, harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k) (v : R3) :
    Commute (coreBlockOperator hO hD K) (coreDirectionalDerivative hO hD v) := by
  change coreBlockOperator hO hD K*coreDirectionalDerivative hO hD v =
    coreDirectionalDerivative hO hD v*coreBlockOperator hO hD K
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k
    (coreBlockOperator hO hD K (coreDirectionalDerivative hO hD v F) x) =
    SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k (coreDirectionalDerivative hO hD v (coreBlockOperator hO hD K F) x)
  rw [coreBlockOperator_coordinate]
  have hcoordinate : ContDiff ℝ ∞ (fun y => SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k (F y)) :=
    (SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k).contDiff.comp F.property.1
  have heq : (fun y => SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k (coreBlockOperator hO hD K F y)) =
      (fun y => K k (SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k (F y))) :=
    funext (fun y => coreBlockOperator_coordinate hO hD K F y k)
  have hd := congrArg (fun H : R3 → harmonicSphereSubspace k => directionalFDeriv v H x) heq
  rw [ActualReferenceDecomposition.directionalFDeriv_fixed_map (K k) _ hcoordinate v x] at hd
  unfold directionalFDeriv at hd
  rw [SpectralCoreRegularity.fderiv_sphereHarmonicCoordinate hO hD k (coreBlockOperator hO hD K F : R3 → SphereL2) x
    ((coreBlockOperator hO hD K F).property.1.differentiable (by simp) x),
    SpectralCoreRegularity.fderiv_sphereHarmonicCoordinate hO hD k (F : R3 → SphereL2) x
      (F.property.1.differentiable (by simp) x)] at hd
  exact hd.symm

lemma coreDirectionalDerivative_coreAngularGenerator_commute
    (hF : SphereFischerInner) (v : R3) (i : CoreAngularGeneratorIndex) :
    Commute (coreDirectionalDerivative hO hD v) (coreAngularGenerator hO hD hF i) := by
  rcases i with a | (a | (ab | b))
  · exact (coreDirectionalDerivative_normalizedDerivative_commute hO hD v hF a).mul_right
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).symm
  · exact (coreDirectionalDerivative_normalizedRaising_commute hO hD v hF a).mul_right
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).symm
  · exact (coreBlockOperator_directionalDerivative_commute hO hD (fun k => harmonicSphereRotation k ab.1 ab.2) v).symm
  · cases b with
    | false => exact Commute.one_right _
    | true => exact (coreWeightOperator_directionalDerivative_commute hO hD (fun k => (k:ℝ)) v).symm

lemma coefficientDerivative_angular_quadratic_scalar_word
    (hF : SphereFischerInner) (v : R3) (i j : CoreAngularGeneratorIndex)
    (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c) :
    coefficientDerivative (coreDirectionalDerivative hO hD v)
      (coreScalar hO hD c hc*(coreAngularGenerator hO hD hF i*coreAngularGenerator hO hD hF j)) =
      coreScalar hO hD (directionalFDeriv v c) (contDiff_directionalFDeriv v c hc)*
        (coreAngularGenerator hO hD hF i*coreAngularGenerator hO hD hF j) := by
  have hcomm := (coreDirectionalDerivative_coreAngularGenerator_commute hO hD hF v i).mul_right
    (coreDirectionalDerivative_coreAngularGenerator_commute hO hD hF v j)
  have hz : coefficientDerivative (coreDirectionalDerivative hO hD v)
      (coreAngularGenerator hO hD hF i*coreAngularGenerator hO hD hF j) = 0 := sub_eq_zero.mpr hcomm.eq
  rw [coefficientDerivative_coreScalar_mul,hz,mul_zero,add_zero]

lemma coefficientDerivative_angular_quadratic_scalar_combination
    (hF : SphereFischerInner) (v : R3)
    (c : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex → R3 → ℝ)
    (hc : ∀ ij, ContDiff ℝ ∞ (c ij)) :
    coefficientDerivative (coreDirectionalDerivative hO hD v)
      (coreScalarCombination hO hD (fun ij => coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2) c hc) =
    coreScalarCombination hO hD (fun ij => coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
      (fun ij => directionalFDeriv v (c ij)) (fun ij => contDiff_directionalFDeriv v (c ij) (hc ij)) := by
  unfold coreScalarCombination
  change ActualModelCommutatorWords.commutator _ (∑ ij, _) = _
  rw [ActualModelCommutatorWords.commutator_sum_right]
  apply Finset.sum_congr rfl
  intro ij _
  exact coefficientDerivative_angular_quadratic_scalar_word hO hD hF v ij.1 ij.2 (c ij) (hc ij)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
