import Calderon.ActualFiniteHarmonicModelAngularCompositionForms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SpectralCoreRegularity
  ActualReferenceDDSpectralTransport
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev halfWeightSumFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] halfWeightSumFunction

lemma coreWeight_half_eq_preserving_add_sum
    {ι : Type} [Fintype ι] (M : SphereL2 →L[ℝ] SphereL2)
    (hM : PreservesSphereSpectralGraphs hO hD M)
    (A F : smoothCompactFiniteSphereCore hO hD) (U : ι → smoothCompactFiniteSphereCore hO hD)
    (c : ι → ℝ) (x : R3)
    (hA : A x = M (coreWeightOperator hO hD (besselWeight 1) F x)+∑ i, c i • U i x) :
    coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) A x =
      M (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x)+
        ∑ i, c i • coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (U i) x := by
  classical
  have hbetween : (coreWeightOperator hO hD (besselWeight 1) F x,
      coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    rw [← coreWeight_half_one_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) (coreWeightOperator hO hD (besselWeight 1) F) x
  have hsum : (∑ i, c i • U i x,
      ∑ i, c i • coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (U i) x) ∈
      sphereBesselGraph hO hD (1/2 : ℝ) := by
    have ht := (sphereBesselGraph hO hD (1/2 : ℝ)).sum_mem
      (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
        (sphereBesselGraph hO hD (1/2 : ℝ)).smul_mem (c i)
          (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) (U i) x))
    simpa only [Prod.smul_mk,← prod_mk_sum] using ht
  have hgraph := (sphereBesselGraph hO hD (1/2 : ℝ)).add_mem
    (hM _ _ _ hbetween) hsum
  have hw := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) A x
  rw [hA] at hw
  exact spectralGraph_output_unique hO hD (besselWeight (1/2 : ℝ)) _ _ _ hw hgraph

lemma norm_coreWeight_half_le_preserving_add_sum
    {ι : Type} [Fintype ι] (M : SphereL2 →L[ℝ] SphereL2)
    (hM : PreservesSphereSpectralGraphs hO hD M)
    (A F : smoothCompactFiniteSphereCore hO hD) (U : ι → smoothCompactFiniteSphereCore hO hD)
    (c b : ι → ℝ) (x : R3)
    (hA : A x = M (coreWeightOperator hO hD (besselWeight 1) F x)+∑ i, c i • U i x)
    (hU : ∀ i, ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (U i) x‖ ≤
      b i*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖) :
    ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) A x‖ ≤
      (‖M‖+∑ i, |c i| * b i)*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := by
  classical
  rw [coreWeight_half_eq_preserving_add_sum hO hD M hM A F U c x hA]
  calc
    _ ≤ ‖M (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x)‖+
        ‖∑ i, c i • coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (U i) x‖ := norm_add_le _ _
    _ ≤ ‖M‖*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖+
        ∑ i, ‖c i • coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (U i) x‖ :=
      add_le_add (M.le_opNorm _) (norm_sum_le _ _)
    _ ≤ ‖M‖*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖+
        ∑ i, |c i| *(b i*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖) := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hU i) (abs_nonneg _)
    _ = _ := by simp only [add_mul,Finset.sum_mul,mul_assoc]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
