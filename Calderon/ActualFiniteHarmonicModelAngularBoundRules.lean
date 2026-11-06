import Calderon.ActualFiniteHarmonicModelAngularProductForms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SpectralCoreRegularity
  ActualReferenceDDSpectralTransport
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularBoundRulesFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularBoundRulesFunction

lemma hasCoreAngularFirstOrderBounds_mono
    (T Tstar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (C B : ℝ) (x : R3)
    (h : HasCoreAngularFirstOrderBounds hO hD T Tstar C x) (hCB : C ≤ B) :
    HasCoreAngularFirstOrderBounds hO hD T Tstar B x := by
  refine ⟨h.1.trans hCB,h.2.1,?_,?_,?_⟩
  · intro F G
    exact (h.2.2.1 F G).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCB (norm_nonneg _)) (norm_nonneg _))
  · intro F
    exact (h.2.2.2.1 F).trans (mul_le_mul_of_nonneg_right hCB (norm_nonneg _))
  · intro F
    exact (h.2.2.2.2 F).trans (mul_le_mul_of_nonneg_right hCB (norm_nonneg _))

lemma hasCoreAngularFirstOrderBounds_adjoint
    (T Tstar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (C : ℝ) (x : R3)
    (h : HasCoreAngularFirstOrderBounds hO hD T Tstar C x) :
    HasCoreAngularFirstOrderBounds hO hD Tstar T C x := by
  have ha (F G : smoothCompactFiniteSphereCore hO hD) :
      ⟪Tstar F x,G x⟫_ℝ = ⟪F x,T G x⟫_ℝ := by
    rw [real_inner_comm,← h.2.1]
    exact real_inner_comm _ _
  refine ⟨h.1,ha,?_,h.2.2.2.2,h.2.2.2.1⟩
  intro F G
  rw [ha,real_inner_comm]
  have ht := h.2.2.1 G F
  calc
    _ ≤ C*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ := ht
    _ = _ := by ring

lemma norm_coreWeight_half_preserving_action_le
    (M : SphereL2 →L[ℝ] SphereL2) (hM : PreservesSphereSpectralGraphs hO hD M)
    (A F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hA : A x = M (coreWeightOperator hO hD (besselWeight 1) F x)) :
    ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) A x‖ ≤
      ‖M‖*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := by
  have hbetween : (coreWeightOperator hO hD (besselWeight 1) F x,
      coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    rw [← coreWeight_half_one_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ))
      (coreWeightOperator hO hD (besselWeight 1) F) x
  have hw := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) A x
  rw [hA] at hw
  have he := spectralGraph_output_unique hO hD (besselWeight (1/2 : ℝ)) _ _ _ hw (hM _ _ _ hbetween)
  rw [he]
  exact M.le_opNorm _

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
