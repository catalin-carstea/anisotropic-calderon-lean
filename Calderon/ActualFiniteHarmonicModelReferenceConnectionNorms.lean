import Calderon.ActualFiniteHarmonicModelReferenceWeights
import Calderon.ActualFiniteHarmonicModelAngularBoundRules
import Calderon.ActualReferenceDDHigherGeometryJets

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualReferenceDDSpectralTransport ActualReferenceParallelRaising ActualReferenceDDHigherGeometryJets
  SmoothMetricFrame
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceConnectionNormsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] referenceConnectionNormsFunction

theorem exists_nativeReferenceConnection_uniform_norm_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ a : Fin 3,
      ∀ F : smoothCompactFiniteSphereCore hO hD,
      ‖nativeReferenceConnectionAction hO hD g hg L lam a F x‖ ≤ C*‖coreWeightOperator hO hD (besselWeight 1) F x‖ ∧
      ‖coreWeightOperator hO hD (besselWeight (1/2:ℝ)) (nativeReferenceConnectionAction hO hD g hg L lam a F) x‖ ≤
        C*‖coreWeightOperator hO hD (besselWeight (3/2:ℝ)) F x‖ := by
  obtain ⟨M,hM,hgeom⟩ := exists_referenceDD_fixed_geometry_uniform_coordinate_word_bounds hO hD g hg L K hK 0
  refine ⟨M,lt_of_lt_of_le zero_lt_one hM,?_⟩
  intro lam hlam x hx a F
  let A := normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)
  have hn : ‖A‖ ≤ M := by
    simpa only [A,coordinateFieldWordPartial] using (hgeom lam hlam x hx [] (by simp)).2.2.2.2.2.1 a
  have hp : PreservesSphereSpectralGraphs hO hD A := preservesSphereSpectralGraphs_normalizedReferenceAngularConnection
    hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)
  have ha := nativeReferenceConnectionAction_apply_eq_normalized hO hD g hg L lam a F x
  constructor
  · rw [ha]
    exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  · exact (norm_coreWeight_half_preserving_action_le hO hD A hp _ F x ha).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
