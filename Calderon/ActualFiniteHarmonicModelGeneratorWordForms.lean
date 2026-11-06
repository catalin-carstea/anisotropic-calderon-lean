import Calderon.ActualFiniteHarmonicModelGeneratorCommutatorBounds
import Calderon.ActualFiniteHarmonicModelQuadraticCommutatorForms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev generatorWordFormsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] generatorWordFormsFunction

lemma coreAngularGenerator_quadratic_linear_commutator_bound
    (hF : SphereFischerInner) (i j k : CoreAngularGeneratorIndex)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪commutator (coreAngularGenerator hO hD hF i*coreAngularGenerator hO hD hF j)
      (coreAngularGenerator hO hD hF k) F x,G x⟫_ℝ| ≤
      (8*(coreAngularGeneratorBound hO hD)^2)*
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  obtain ⟨V,hV⟩ := exists_coreAngularGenerator_commutator_bounds hO hD hF j k x
  obtain ⟨U,hU⟩ := exists_coreAngularGenerator_commutator_bounds hO hD hF i k x
  have ht := coreAngular_quadratic_linear_commutator_bound hO hD
    _ _ _ _ _ V U _ _ x
    (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF i x)
    (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF j x) hV hU F G
  convert ht using 1 <;> ring

lemma coreAngularGenerator_quadratic_quadratic_commutator_bound
    (hF : SphereFischerInner) (i j k l : CoreAngularGeneratorIndex)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪commutator (coreAngularGenerator hO hD hF i*coreAngularGenerator hO hD hF j)
      (coreAngularGenerator hO hD hF k*coreAngularGenerator hO hD hF l) F x,G x⟫_ℝ| ≤
      (16*(coreAngularGeneratorBound hO hD)^3)*
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  obtain ⟨Vjk,hjk⟩ := exists_coreAngularGenerator_commutator_bounds hO hD hF j k x
  obtain ⟨Vjl,hjl⟩ := exists_coreAngularGenerator_commutator_bounds hO hD hF j l x
  obtain ⟨Vik,hik⟩ := exists_coreAngularGenerator_commutator_bounds hO hD hF i k x
  obtain ⟨Vil,hil⟩ := exists_coreAngularGenerator_commutator_bounds hO hD hF i l x
  have ht := coreAngular_quadratic_quadratic_commutator_bound hO hD
    _ _ _ _ _ _ _ _ Vjk Vjl Vik Vil _ _ x
    (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF i x)
    (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF j x)
    (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF k x)
    (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF l x)
    hjk hjl hik hil F G
  convert ht using 1 <;> ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
