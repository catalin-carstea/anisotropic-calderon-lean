import Calderon.ActualFiniteHarmonicModelAngularGenerators
import Calderon.ActualFiniteHarmonicModelAngularCommutatorBoundRules
import Calderon.ActualFiniteHarmonicModelRotationShiftCommutator
import Calderon.ActualFiniteHarmonicModelRotationLieCommutator

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma exists_coreRotation_coreDerivative_commutator_bounds
    (hF : SphereFischerInner) (i j a : Fin 3) (x : R3) :
    ∃ V, HasCoreAngularFirstOrderBounds hO hD
      (commutator (coreRotation hO hD i j) (coreDerivative hO hD hF a)) V
      (2*coreAngularGeneratorBound hO hD) x := by
  have hb := coreAngularGeneratorBound_bounds hO hD
  have hd (b : Fin 3) := hasCoreAngularFirstOrderBounds_mono hO hD _ _ _ _ x
    (hasCoreAngularFirstOrderBounds_coreDerivative hO hD hF b x) hb.2.1
  have hi := hasCoreAngularFirstOrderBounds_ite hO hD (a=j) _ _ _ x (hd i)
  have hj := hasCoreAngularFirstOrderBounds_ite hO hD (a=i) _ _ _ x (hd j)
  refine ⟨(if a=j then coreRaising hO hD hF i else 0)-
    (if a=i then coreRaising hO hD hF j else 0), ?_⟩
  rw [coreRotation_derivative_commutator hO hD hF i j a]
  simpa only [two_mul] using hasCoreAngularFirstOrderBounds_sub hO hD _ _ _ _ _ _ x hi hj

lemma exists_coreRotation_coreRaising_commutator_bounds
    (hF : SphereFischerInner) (i j a : Fin 3) (x : R3) :
    ∃ V, HasCoreAngularFirstOrderBounds hO hD
      (commutator (coreRotation hO hD i j) (coreRaising hO hD hF a)) V
      (2*coreAngularGeneratorBound hO hD) x := by
  have hb := coreAngularGeneratorBound_bounds hO hD
  have hd (b : Fin 3) := hasCoreAngularFirstOrderBounds_mono hO hD _ _ _ _ x
    (hasCoreAngularFirstOrderBounds_coreRaising hO hD hF b x) hb.2.1
  have hi := hasCoreAngularFirstOrderBounds_ite hO hD (a=j) _ _ _ x (hd i)
  have hj := hasCoreAngularFirstOrderBounds_ite hO hD (a=i) _ _ _ x (hd j)
  refine ⟨(if a=j then coreDerivative hO hD hF i else 0)-
    (if a=i then coreDerivative hO hD hF j else 0), ?_⟩
  rw [coreRotation_raising_commutator hO hD hF i j a]
  simpa only [two_mul] using hasCoreAngularFirstOrderBounds_sub hO hD _ _ _ _ _ _ x hi hj

lemma exists_coreRotation_coreRotation_commutator_bounds
    (i j a b : Fin 3) (x : R3) :
    ∃ V, HasCoreAngularFirstOrderBounds hO hD
      (commutator (coreRotation hO hD i j) (coreRotation hO hD a b)) V
      (4*coreAngularGeneratorBound hO hD) x := by
  have hb := coreAngularGeneratorBound_bounds hO hD
  have hr (c d : Fin 3) := hasCoreAngularFirstOrderBounds_mono hO hD _ _ _ _ x
    (hasCoreAngularFirstOrderBounds_coreRotation hO hD c d x) (hb.2.2.2.2 c d)
  have h1 := hasCoreAngularFirstOrderBounds_ite hO hD (j=a) _ _ _ x (hr i b)
  have h2 := hasCoreAngularFirstOrderBounds_ite hO hD (j=b) _ _ _ x (hr i a)
  have h3 := hasCoreAngularFirstOrderBounds_ite hO hD (i=a) _ _ _ x (hr j b)
  have h4 := hasCoreAngularFirstOrderBounds_ite hO hD (i=b) _ _ _ x (hr j a)
  have h12 := hasCoreAngularFirstOrderBounds_sub hO hD _ _ _ _ _ _ x h1 h2
  have h123 := hasCoreAngularFirstOrderBounds_sub hO hD _ _ _ _ _ _ x h12 h3
  have ht := hasCoreAngularFirstOrderBounds_add hO hD _ _ _ _ _ _ x h123 h4
  refine ⟨((if j=a then -coreRotation hO hD i b else 0) -
    (if j=b then -coreRotation hO hD i a else 0) -
    (if i=a then -coreRotation hO hD j b else 0) +
    (if i=b then -coreRotation hO hD j a else 0)), ?_⟩
  rw [coreRotation_lie_commutator hO hD i j a b]
  convert ht using 1 <;> ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
