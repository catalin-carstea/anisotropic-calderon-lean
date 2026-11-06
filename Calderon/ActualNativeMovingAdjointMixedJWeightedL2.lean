import Calderon.ActualNativeMovingAdjointMixedJPointGraph
import Calderon.ActualNativeMovingAdjointMixedJSectionPreparation
import Calderon.SphereSobolevZeroLiftNegativeGraph
import Calderon.SphereSobolevHalfZeroNegativeInclusion
import Calderon.ActualNativeMovingAdjointMixedJBound
import Calderon.ActualFinitePhysicalWeakSquaredNorm
import Calderon.ContinuousLinearSectionSupport
import Calderon.SphereSobolevZeroSectionSupport
import Calderon.SphereSobolevZeroEquivIdentities
import Calderon.RealNormedGroupProjectionData

/-! Before-source: actual-physical-full-allocation-author-oct16-v001/
EXPANSION-actual-mixed-weighted-L2-bound-v022.md and
actual-covariant-leading-algebra-author-oct16-v001/EXPANSION-actual-mixed-weighted-L2-implementation-v016.md.
One canonical representative, before-profile-power uniform actual mixed bound. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ReferenceDensityBounds

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceNativeMovingAdjointParametricJ
  referenceNativeMovingAdjointHighMixedCorrection sphereSobolevInclusionL sphereSobolevZeroEquiv

include hg in
lemma exists_referenceNativeMovingAdjointHighMixedCorrection_weightedL2_bound
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ hreg : FixedDirichletRegularity,
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ R : R3 → ℝ, ContDiff ℝ ∞ R →
      ∀ u : R3 → SphereSobolev (3/2 : ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ y ∈ tsupport u, ‖y-y0‖ ≤ ρ ∧ ‖fderiv ℝ R y‖ ≤ 1) →
      ∃ j : R3 → SphereL2,
        (∀ y : R3, j y = (sphereSobolevZeroEquiv hO hD).symm
          (referenceNativeMovingAdjointParametricJ hF hO hD g g2 L ((q,y),fderiv ℝ R y)
            (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) (u y)))) ∧
        ContDiff ℝ ∞ j ∧ HasCompactSupport j ∧ MemLp j 2 (volume : Measure R3) ∧
        (∀ y : R3, sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
            (sphereSobolevZeroEquiv hO hD (j y)) =
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
            (referenceNativeMovingAdjointHighMixedCorrection
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 q y (fderiv ℝ R y) (u y))) ∧
        Integrable (fun y : R3 => referenceDensityFamily g L (q,y) * ‖j y‖^2) ∧
        Integrable (fun y : R3 => referenceDensityFamily g L (q,y) *
          ‖sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) (u y)‖^2) ∧
        (∫ y : R3, referenceDensityFamily g L (q,y) * ‖j y‖^2) ≤
          CJ^2 * (∫ y : R3, referenceDensityFamily g L (q,y) *
            ‖sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) (u y)‖^2) := by
  trace "ACTUAL_MIXED_WEIGHTED_L2_ENTER"
  obtain ⟨CJ,hCJpos,hCJ⟩ := exists_referenceNativeMovingAdjointParametricJ_uniform_bound
    hF hO hD g g2 hg hg2 L (closedBall y0 ρ) (isCompact_closedBall _ _)
  trace "ACTUAL_MIXED_WEIGHTED_L2_UNIFORM_CONSTANT_READY"
  refine ⟨CJ,hCJpos,?_⟩
  intro hreg q hq R hR u hu hcu hRoom
  trace "ACTUAL_MIXED_WEIGHTED_L2_SECTION_INTRO_READY"
  let Z := sphereSobolevZeroEquiv hO hD
  let I31 := sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num)
  let Ihalf0 := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let I0neg := sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let U : R3 → SphereSobolev 1 := fun y => I31 (u y)
  let T : R3 → SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
    fun y => referenceNativeMovingAdjointParametricJ hF hO hD g g2 L ((q,y),fderiv ℝ R y)
  trace "ACTUAL_MIXED_WEIGHTED_L2_NATIVE_FAMILY_READY"
  let j : R3 → SphereL2 := fun y => Z.symm (T y (U y))
  let mu : R3 → ℝ := fun y => referenceDensityFamily g L (q,y)
  have hPreparation := referenceNativeMovingAdjointParametricJ_lift_smooth_compact
    hF hO hD g g2 hg hg2 L q R hR u hu hcu
  have hU := hPreparation.1
  have hUSupport := hPreparation.2.1
  have hUCompact := hPreparation.2.2.1
  have hj := hPreparation.2.2.2.1
  have hjSupport := hPreparation.2.2.2.2.1
  have hjCompact := hPreparation.2.2.2.2.2.1
  have hjMem := hPreparation.2.2.2.2.2.2
  trace "ACTUAL_MIXED_WEIGHTED_L2_CANONICAL_SMOOTH_COMPACT_READY"
  have hGraph (y : R3) : I0neg (Z (j y)) =
      Iout (referenceNativeMovingAdjointHighMixedCorrection
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 q y (fderiv ℝ R y) (u y)) := by
    have hRoomOrZero : ‖y-y0‖ ≤ ρ ∨ u y = 0 := by
      by_cases hy : y ∈ tsupport u
      · exact Or.inl (hRoom y hy).1
      · exact Or.inr (image_eq_zero_of_notMem_tsupport hy)
    exact referenceNativeMovingAdjointParametricJ_lift_negative_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 hreg
        q hq y (fderiv ℝ R y) (u y) hRoomOrZero
  trace "ACTUAL_MIXED_CANONICAL_GLOBAL_GRAPH_READY"
  have hPointNorm (y : R3) : ‖j y‖ ≤ CJ * ‖U y‖ := by
    by_cases hy : y ∈ tsupport u
    · have hK : y ∈ closedBall y0 ρ := by
        simpa only [mem_closedBall,dist_eq_norm] using (hRoom y hy).1
      have hOp := hCJ q hq y hK (fderiv ℝ R y) (hRoom y hy).2
      calc
        ‖j y‖ = ‖T y (U y)‖ :=
          norm_sphereSobolevZeroEquiv_symm_apply hO hD (T y (U y))
        _ ≤ ‖T y‖ * ‖U y‖ := (T y).le_opNorm _
        _ ≤ CJ * ‖U y‖ := mul_le_mul_of_nonneg_right hOp (norm_nonneg _)
    · have hu0 : u y = 0 := image_eq_zero_of_notMem_tsupport hy
      have hU0 : U y = 0 := (congrArg I31 hu0).trans (ContinuousLinearMap.map_zero I31)
      have hj0 : j y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hjSupport h))
      simpa only [hj0,hU0,norm_zero,mul_zero] using (le_rfl : (0 : ℝ) ≤ 0)
  have hmu : Continuous mu :=
    ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)).continuous
  have hjInt : Integrable (fun y : R3 => mu y * ‖j y‖^2) :=
    integrable_weighted_norm_sq_of_continuous_compact mu hmu j hj.continuous hjCompact
  have hUInt : Integrable (fun y : R3 => mu y * ‖U y‖^2) :=
    integrable_weighted_norm_sq_of_continuous_compact mu hmu U hU.continuous hUCompact
  have hWeightedPoint (y : R3) : mu y * ‖j y‖^2 ≤ CJ^2 * (mu y * ‖U y‖^2) := by
    have hSquare : ‖j y‖^2 ≤ CJ^2 * ‖U y‖^2 :=
      ((sq_le_sq₀ (norm_nonneg (j y)) (mul_nonneg hCJpos.le (norm_nonneg (U y)))).2
        (hPointNorm y)).trans_eq (mul_pow CJ ‖U y‖ 2)
    have hMul := mul_le_mul_of_nonneg_left hSquare (referenceDensityFamily_pos g hg L (q,y)).le
    exact hMul.trans_eq (by ring)
  have hIntegral : (∫ y : R3, mu y * ‖j y‖^2) ≤ CJ^2 * (∫ y : R3, mu y * ‖U y‖^2) :=
    (integral_mono hjInt (hUInt.const_mul (CJ^2)) hWeightedPoint).trans_eq
      (integral_const_mul (CJ^2) (fun y : R3 => mu y * ‖U y‖^2))
  trace "ACTUAL_MIXED_WEIGHTED_L2_GRAPH_AND_BOUND_READY"
  exact ⟨j,(fun _ => rfl),hj,hjCompact,hjMem,hGraph,hjInt,hUInt,hIntegral⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceNativeMovingAdjointHighMixedCorrection_weightedL2_bound
