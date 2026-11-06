import Calderon.ActualFiniteHarmonicModelAngularBoundRules

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SpectralCoreRegularity
  ActualReferenceDDSpectralTransport
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev preservingAngularBoundsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] preservingAngularBoundsFunction

lemma hasCoreAngularFirstOrderBounds_of_preserving_actions
    (T Tstar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (M N : SphereL2 →L[ℝ] SphereL2) (C : ℝ) (x : R3) (hC : 0 ≤ C)
    (hM : PreservesSphereSpectralGraphs hO hD M) (hN : PreservesSphereSpectralGraphs hO hD N)
    (hMn : ‖M‖ ≤ C) (hNn : ‖N‖ ≤ C)
    (hT : ∀ F : smoothCompactFiniteSphereCore hO hD,
      T F x = M (coreWeightOperator hO hD (besselWeight 1) F x))
    (hTs : ∀ F : smoothCompactFiniteSphereCore hO hD,
      Tstar F x = N (coreWeightOperator hO hD (besselWeight 1) F x))
    (hadj : ∀ F G : smoothCompactFiniteSphereCore hO hD,
      ⟪T F x,G x⟫_ℝ = ⟪F x,Tstar G x⟫_ℝ) :
    HasCoreAngularFirstOrderBounds hO hD T Tstar C x := by
  refine ⟨hC,hadj,?_,?_,?_⟩
  · intro F G
    have hbetween : (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x,
        coreWeightOperator hO hD (besselWeight 1) F x) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
      intro k
      rw [(coreWeightOperator_graph hO hD (besselWeight 1) F x) k,
        (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x) k,
        smul_smul,← SectionFiveErrorForms.besselWeight_add]
      norm_num
    rw [hT]
    rw [spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ))
      (M (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x))
      (M (coreWeightOperator hO hD (besselWeight 1) F x))
      (G x) (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x)
      (hM _ _ _ hbetween) (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x)]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((M.le_opNorm _).trans (mul_le_mul_of_nonneg_right hMn (norm_nonneg _))) (norm_nonneg _))
  · intro F
    exact (norm_coreWeight_half_preserving_action_le hO hD M hM (T F) F x (hT F)).trans
      (mul_le_mul_of_nonneg_right hMn (norm_nonneg _))
  · intro F
    exact (norm_coreWeight_half_preserving_action_le hO hD N hN (Tstar F) F x (hTs F)).trans
      (mul_le_mul_of_nonneg_right hNn (norm_nonneg _))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
