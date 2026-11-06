import Calderon.ActualFiniteHarmonicModelAngularLinearBounds
import Calderon.ActualFiniteHarmonicModelPreservingAngularBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualReferenceDDSpectralTransport
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularFiniteBoundsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularFiniteBoundsFunction

lemma hasCoreAngularFirstOrderBounds_sum
    {ι : Type} (s : Finset ι)
    (T Tstar : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (C : ι → ℝ) (x : R3)
    (h : ∀ i ∈ s, HasCoreAngularFirstOrderBounds hO hD (T i) (Tstar i) (C i) x) :
    HasCoreAngularFirstOrderBounds hO hD (∑ i ∈ s, T i) (∑ i ∈ s, Tstar i) (∑ i ∈ s, C i) x := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro h
    simpa only [Finset.sum_empty] using hasCoreAngularFirstOrderBounds_zero hO hD x
  | @insert a s ha ih =>
    intro h
    simp only [Finset.sum_insert ha]
    exact hasCoreAngularFirstOrderBounds_add hO hD _ _ _ _ _ _ x
      (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma hasCoreAngularFirstOrderBounds_one (x : R3) :
    HasCoreAngularFirstOrderBounds hO hD 1 1 ‖inverseDegreeMultiplier hO hD‖ x := by
  let M := inverseDegreeMultiplier hO hD
  have hM : PreservesSphereSpectralGraphs hO hD M :=
    preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD
  apply hasCoreAngularFirstOrderBounds_of_preserving_actions hO hD 1 1 M M ‖M‖ x
    (norm_nonneg _) hM hM le_rfl le_rfl
    (fun F => (inverseDegreeMultiplier_coreWeight_one_apply hO hD F x).symm)
    (fun F => (inverseDegreeMultiplier_coreWeight_one_apply hO hD F x).symm)
  intro F G
  rfl

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
