import Calderon.ActualTZeroNegativeGraph
import Calderon.ActualTSPrincipalWeightedCaps

/-! Exact original first-T negative graphs and uniform included-derivative bounds.
These support the linear-zero S part of the lower T/S estimate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTFirstNegativeGraph
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualTFirstPhysicalDictionary ActualTZeroNegativeGraph ActualFiniteHarmonicCore
  ActualFiniteCoreLoweringRealization ActualHigherSPhysicalPairing AmbientReferenceRaising
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth
  FixedParameterProfilePullback FixedParameterProfileBudgets
  ActualTSPrincipalCoefficients ActualTSPrincipalGreen ActualHigherSCoordinateWeightBounds
  ActualHigherSLeadingBracketGain ActualTSPrincipalPhysicalGreen ActualTSPrincipalAngularCaps
  ActualScalarPrincipalAdjoint ActualHigherSScalarCommutatorForm ActualScalarPrincipalSelfFormBound
  ActualHigherSScalarCommutatorNativeForm ActualMixedAngularPairedGains
  ActualPiJacobiRadialGainedRows ActualJacobiAngularGainedRows
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier

private lemma norm_double_action_le {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (c : Fin 3 → Fin 3 → ℝ) (A : Fin 3 → X →L[ℝ] Y) (v : Fin 3 → X)
    (M : ℝ) (hM : 0 ≤ M) (hc : ∀ i l, |c i l| ≤ M) :
    ‖∑ l : Fin 3, ∑ i : Fin 3, c i l • A i (v l)‖ ≤
      (M*(∑ i : Fin 3, ‖A i‖))*(∑ l : Fin 3, ‖v l‖) := by
  calc
    _ ≤ ∑ l : Fin 3, ‖∑ i : Fin 3, c i l • A i (v l)‖ := norm_sum_le _ _
    _ ≤ ∑ l : Fin 3, ∑ i : Fin 3, ‖c i l • A i (v l)‖ :=
      Finset.sum_le_sum (fun l _ => norm_sum_le _ _)
    _ ≤ ∑ l : Fin 3, ∑ i : Fin 3, M*‖A i‖*‖v l‖ := by
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul (hc i l) ((A i).le_opNorm (v l))
        (norm_nonneg _) hM).trans_eq (by ring)
    _ = ∑ l : Fin 3, (M*(∑ i : Fin 3, ‖A i‖))*‖v l‖ := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum,Finset.sum_mul]
    _ = _ := (Finset.mul_sum _ _ _).symm

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def lowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def lowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] lowNormed lowSpace
variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (g : MatrixField) (L : ℝ)

/-- The identical first base sum in the original negative Sobolev endpoint. -/
def originalFirstNegative (q : ℝ) (U : R3 → Hi) (x : R3) : Neg :=
  ∑ l : Fin 3, ∑ i : Fin 3, referenceMetricGramFrame g L (q,x) i l •
    raisingLow hF hO hD i (IH (fderiv ℝ U x (coordinateDirection l)))

/-- The original negative sign of the raw adjoint first base sum is retained. -/
def originalAdjointFirstNegative (q : ℝ) (U : R3 → Hi) (x : R3) : Neg :=
  -(∑ l : Fin 3, ∑ i : Fin 3, referenceMetricGramFrame g L (q,x) i l •
    loweringLow hF hO hD i (IH (fderiv ℝ U x (coordinateDirection l))))

theorem original_first_negative_graph (q : ℝ) (U : R3 → Hi) (x : R3) :
    JL (referenceFirstHalf hO hD hF g L q U x)=originalFirstNegative hF hO hD g L q U x := by
  unfold referenceFirstHalf originalFirstNegative
  simp only [map_sum,map_smul,v017_inclusion_raisingHigh]

theorem original_adjoint_first_negative_graph (q : ℝ) (U : R3 → Hi) (x : R3) :
    JL (referenceAdjointFirstHalf hO hD hF g L q U x)=
      originalAdjointFirstNegative hF hO hD g L q U x := by
  unfold referenceAdjointFirstHalf originalAdjointFirstNegative
  simp only [map_neg,map_sum,map_smul,v017_inclusion_loweringHigh]

attribute [local irreducible] raisingLow loweringLow sphereSobolevInclusionL
  referenceFirstHalf referenceAdjointFirstHalf

/-- A single constant precedes all q and inputs, and uses only included first derivatives. -/
theorem exists_original_first_negative_uniform_bound
    (hg : IsAdmissibleMetric g) (y0 : R3) (ρ : ℝ) :
    ∃ CT : ℝ, 0 < CT ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ x ∈ closedBall y0 ρ, ∀ U : R3 → Hi,
      ‖originalFirstNegative hF hO hD g L q U x‖ ≤
        CT*(∑ l : Fin 3, ‖IH (fderiv ℝ U x (coordinateDirection l))‖) ∧
      ‖originalAdjointFirstNegative hF hO hD g L q U x‖ ≤
        CT*(∑ l : Fin 3, ‖IH (fderiv ℝ U x (coordinateDirection l))‖) := by
  let cap := exists_metricFrame_uniform_first_caps g hg L y0 ρ
  let M : ℝ := Classical.choose cap
  have hM : 1 ≤ M := (Classical.choose_spec cap).1
  have hFrame := (Classical.choose_spec cap).2
  let RA : ℝ := ∑ i : Fin 3, ‖raisingLow hF hO hD i‖
  let RL : ℝ := ∑ i : Fin 3, ‖loweringLow hF hO hD i‖
  let CT : ℝ := M*(RA+RL+1)
  have hRA : 0 ≤ RA := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hRL : 0 ≤ RL := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hCT : 0 < CT := mul_pos (zero_lt_one.trans_le hM) (by dsimp only [RA,RL] at hRA hRL; positivity)
  have hAR : M*RA ≤ CT := mul_le_mul_of_nonneg_left (by linarith only [hRL]) hM0
  have hLR : M*RL ≤ CT := mul_le_mul_of_nonneg_left (by linarith only [hRA]) hM0
  refine ⟨CT,hCT,?_⟩
  intro q hq x hx U
  let v : Fin 3 → Half := fun l => IH (fderiv ℝ U x (coordinateDirection l))
  have hv : 0 ≤ ∑ l : Fin 3, ‖v l‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hc (i l : Fin 3) : |referenceMetricGramFrame g L (q,x) i l| ≤ M :=
    (hFrame q hq x hx i l).2.1
  have hA := norm_double_action_le (fun i l => referenceMetricGramFrame g L (q,x) i l)
    (raisingLow hF hO hD) v M hM0 hc
  have hL := norm_double_action_le (fun i l => referenceMetricGramFrame g L (q,x) i l)
    (loweringLow hF hO hD) v M hM0 hc
  constructor
  · exact hA.trans (mul_le_mul_of_nonneg_right hAR hv)
  · simpa only [originalAdjointFirstNegative,norm_neg] using
      hL.trans (mul_le_mul_of_nonneg_right hLR hv)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTFirstNegativeGraph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTFirstNegativeGraph.original_first_negative_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTFirstNegativeGraph.original_adjoint_first_negative_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTFirstNegativeGraph.exists_original_first_negative_uniform_bound
