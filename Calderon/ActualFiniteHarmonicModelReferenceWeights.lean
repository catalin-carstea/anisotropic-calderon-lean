import Calderon.ActualFiniteHarmonicModelConnectionSymmetric

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity ActualFiniteHarmonicCore
  SpectralWeightedGraph BoundedAngularShift ActualReferenceParallelRaising ActualReferenceDDSpectralTransport
  SmoothMetricFrame MovingFrameConnection ActualNormalizedSphereRotation SmoothSphereRotationProjection
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceZeroWeightFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] referenceZeroWeightFunction
lemma coreRotation_apply_eq_normalizedRotation (i j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreRotation hO hD i j F x = normalizedRotation hO hD i j
      (coreWeightOperator hO hD (besselWeight 1) F x) := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k (coreBlockOperator hO hD (fun l => harmonicSphereRotation l i j) F x) =
    sphereHarmonicCoordinate hO hD k (normalizedRotation hO hD i j (coreWeightOperator hO hD (besselWeight 1) F x))
  rw [coreBlockOperator_coordinate]
  exact (normalizedRotation_graph hO hD i j (F x) (coreWeightOperator hO hD (besselWeight 1) F x)
    (coreWeightOperator_graph hO hD (besselWeight 1) F x) k).symm

lemma coreWeight_one_twice_apply (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x =
      coreWeightOperator hO hD (besselWeight 2) F x := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k
    (coreWeightOperator hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x) =
    sphereHarmonicCoordinate hO hD k (coreWeightOperator hO hD (besselWeight 2) F x)
  rw [(coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x) k,
    (coreWeightOperator_graph hO hD (besselWeight 1) F x) k,
    (coreWeightOperator_graph hO hD (besselWeight 2) F x) k]
  simp only [besselWeight,Real.rpow_one,Real.rpow_two,smul_smul,pow_two]

lemma coreWeight_one_degree_apply (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight 1) (coreDegree hO hD F) x =
      coreWeightOperator hO hD (besselWeight 2) F x - coreWeightOperator hO hD (besselWeight 1) F x := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k
    (coreWeightOperator hO hD (besselWeight 1) (coreWeightOperator hO hD (fun l => (l : ℝ)) F) x) =
    sphereHarmonicCoordinate hO hD k
      (coreWeightOperator hO hD (besselWeight 2) F x - coreWeightOperator hO hD (besselWeight 1) F x)
  rw [map_sub,(coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (fun l => (l : ℝ)) F) x) k,
    (coreWeightOperator_graph hO hD (fun l => (l : ℝ)) F x) k,
    (coreWeightOperator_graph hO hD (besselWeight 2) F x) k,
    (coreWeightOperator_graph hO hD (besselWeight 1) F x) k]
  simp only [besselWeight,Real.rpow_one,Real.rpow_two,smul_smul]
  module

lemma nativeReferenceConnectionAction_apply_eq_normalized
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (a : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeReferenceConnectionAction hO hD g hg L lam a F x =
      normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)
        (coreWeightOperator hO hD (besselWeight 1) F x) := by
  simp only [nativeReferenceConnectionAction,normalizedReferenceAngularConnection,
    LinearMap.smul_apply,LinearMap.sum_apply,Module.End.mul_apply,coreScalar,
    LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,Submodule.coe_sum,Submodule.coe_smul,
    Finset.sum_apply,Pi.smul_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply]
  simp_rw [coreRotation_apply_eq_normalizedRotation hO hD]

lemma coreWeight_nativeReferenceConnectionAction_apply
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (a : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight 1) (nativeReferenceConnectionAction hO hD g hg L lam a F) x =
      normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)
        (coreWeightOperator hO hD (besselWeight 2) F x) := by
  have hW : (coreWeightOperator hO hD (besselWeight 1) F x,
      coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1 := by
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x
  have hA := preservesSphereSpectralGraphs_normalizedReferenceAngularConnection hO hD g L lam x
    (referenceMetricGramFrame g L (lam,x) a) (besselWeight 1) _ _ hW
  rw [← nativeReferenceConnectionAction_apply_eq_normalized hO hD g hg L lam a F x] at hA
  exact spectralGraph_output_unique hO hD (besselWeight 1)
    (nativeReferenceConnectionAction hO hD g hg L lam a F x) _ _
    (coreWeightOperator_graph hO hD (besselWeight 1) (nativeReferenceConnectionAction hO hD g hg L lam a F) x) hA

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
