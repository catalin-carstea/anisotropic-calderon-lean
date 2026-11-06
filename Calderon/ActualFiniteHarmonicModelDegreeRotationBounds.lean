import Calderon.ActualFiniteHarmonicModelPreservingAngularBounds
import Calderon.ActualFiniteHarmonicModelConnectionFrameDerivative

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition ActualFiniteHarmonicCore SpectralWeightedGraph
  SpectralCoreRegularity BoundedAngularShift ActualNormalizedSphereRotation
  ActualReferenceDDSpectralTransport
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev degreeRotationBoundFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] degreeRotationBoundFunction

lemma coreDegree_apply_eq_normalized_degree
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreDegree hO hD F x =
      (ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD)
        (coreWeightOperator hO hD (besselWeight 1) F x) := by
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
    inverseDegreeMultiplier_coreWeight_one_apply hO hD F x]
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k (coreDegree hO hD F x) =
    sphereHarmonicCoordinate hO hD k (coreWeightOperator hO hD (besselWeight 1) F x-F x)
  have hd : sphereHarmonicCoordinate hO hD k (coreDegree hO hD F x) =
      (k : ℝ) • sphereHarmonicCoordinate hO hD k (F x) :=
    coreWeightOperator_graph hO hD (fun k => (k : ℝ)) F x k
  rw [map_sub,hd,coreWeightOperator_graph hO hD (besselWeight 1) F x k]
  simp only [besselWeight,Real.rpow_one]
  module

lemma hasCoreAngularFirstOrderBounds_coreDegree (x : R3) :
    HasCoreAngularFirstOrderBounds hO hD (coreDegree hO hD) (coreDegree hO hD)
      ‖ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD‖ x := by
  let M : SphereL2 →L[ℝ] SphereL2 := ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD
  have hM : PreservesSphereSpectralGraphs hO hD M :=
    preservesSphereSpectralGraphs_sub hO hD _ _ (preservesSphereSpectralGraphs_id hO hD)
      (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)
  apply hasCoreAngularFirstOrderBounds_of_preserving_actions hO hD _ _ M M ‖M‖ x
    (norm_nonneg _) hM hM le_rfl le_rfl
    (fun F => coreDegree_apply_eq_normalized_degree hO hD F x)
    (fun F => coreDegree_apply_eq_normalized_degree hO hD F x)
  intro F G
  exact spectralGraph_inner_symm hO hD (fun k => (k : ℝ))
    (F x) (coreDegree hO hD F x) (G x) (coreDegree hO hD G x)
    (coreWeightOperator_graph hO hD (fun k => (k : ℝ)) F x)
    (coreWeightOperator_graph hO hD (fun k => (k : ℝ)) G x)

lemma hasCoreAngularFirstOrderBounds_coreRotation (i j : Fin 3) (x : R3) :
    HasCoreAngularFirstOrderBounds hO hD (coreRotation hO hD i j) (-coreRotation hO hD i j)
      ‖normalizedRotation hO hD i j‖ x := by
  let M := normalizedRotation hO hD i j
  have hM : PreservesSphereSpectralGraphs hO hD M :=
    preservesSphereSpectralGraphs_normalizedRotation hO hD i j
  have hN : PreservesSphereSpectralGraphs hO hD (-M) := by
    rw [← _root_.neg_one_smul ℝ M]
    exact preservesSphereSpectralGraphs_smul hO hD (-1 : ℝ) M hM
  apply hasCoreAngularFirstOrderBounds_of_preserving_actions hO hD _ _ M (-M) ‖M‖ x
    (norm_nonneg _) hM hN le_rfl (by rw [norm_neg])
    (fun F => coreRotation_apply_eq_normalizedRotation hO hD i j F x)
  · intro F
    change -(coreRotation hO hD i j F x) = (-M) (coreWeightOperator hO hD (besselWeight 1) F x)
    rw [coreRotation_apply_eq_normalizedRotation]
    rfl
  · intro F G
    change ⟪coreRotation hO hD i j F x,G x⟫_ℝ = ⟪F x,-(coreRotation hO hD i j G x)⟫_ℝ
    rw [inner_neg_right]
    exact coreRotation_inner_skew hO hD i j F G x

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
