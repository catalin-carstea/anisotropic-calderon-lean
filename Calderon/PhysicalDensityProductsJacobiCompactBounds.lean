import Calderon.ActualJacobiThreeHalfBoundaryMultiplierFamily
import Calderon.PhysicalDensityProductsUniformJacobiRoom
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
A common positive bound for all nine actual Jacobi multiplier operators on
the original compact signed parameter room, in the full three-half Sobolev
endomorphism norm.
-/

set_option autoImplicit false

open Set Metric
open scoped BigOperators ContDiff Topology

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

private theorem exists_pos_compact_nine_norm_bound
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E]
    (K : Set P) (hK : IsCompact K) (A : Fin 3 → Fin 3 → P → E)
    (hA : ∀ i j, ContinuousOn (A i j) K) :
    ∃ C_N : ℝ, 0 < C_N ∧ ∀ p ∈ K, ∀ i j : Fin 3, ‖A i j p‖ ≤ C_N := by
  let S : P → ℝ := fun p => ∑ i : Fin 3, ∑ j : Fin 3, ‖A i j p‖
  have hS : ContinuousOn S K := by
    dsimp only [S]
    exact continuousOn_finsetSum Finset.univ fun i _ =>
      continuousOn_finsetSum Finset.univ fun j _ => (hA i j).norm
  obtain ⟨B_N, hB_N⟩ := hK.exists_bound_of_continuousOn hS
  refine ⟨1 + |B_N|, by positivity, ?_⟩
  intro p hp i j
  have hRow : ‖A i j p‖ ≤ ∑ k : Fin 3, ‖A i k p‖ :=
    Finset.single_le_sum (fun k _ => norm_nonneg (A i k p)) (Finset.mem_univ j)
  have hRows : (∑ k : Fin 3, ‖A i k p‖) ≤ S p := by
    dsimp only [S]
    exact Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg (fun l _ => norm_nonneg (A k l p)))
      (Finset.mem_univ i)
  calc
    ‖A i j p‖ ≤ S p := hRow.trans hRows
    _ ≤ ‖S p‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (S p)
    _ ≤ B_N := hB_N p hp
    _ ≤ |B_N| := le_abs_self B_N
    _ ≤ 1 + |B_N| := by linarith

/-- All nine actual Jacobi multipliers have one positive full endomorphism
norm bound on the original compact signed parameter room. -/
theorem exists_referencePhysicalDensityProducts_jacobi_compact_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) :
    letI jacobiOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI jacobiOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    ∃ C_N : ℝ, 0 < C_N ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ,
        ∀ r : ℝ, |r| ≤ min ρ 1 → ∀ i j : Fin 3,
          ‖nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
            (referenceJacobiBoundaryThreeHalfCoefficientFamily
              g hg L y0 Φ B ε C ρ H a w hData i j (q,(y,r)))‖ ≤ C_N := by
  letI jacobiOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI jacobiOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  let N : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := fun i j p =>
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryThreeHalfCoefficientFamily
        g hg L y0 Φ B ε C ρ H a w hData i j p)
  change ∃ C_N : ℝ, 0 < C_N ∧
    ∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ,
      ∀ r : ℝ, |r| ≤ min ρ 1 → ∀ i j : Fin 3, ‖N i j (q,(y,r))‖ ≤ C_N
  let KJ : Set (ℝ × (R3 × ℝ)) :=
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-(min ρ 1)) (min ρ 1))
  have hKJ : IsCompact KJ :=
    isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  have hN : ∀ i j, ContinuousOn (N i j) KJ := by
    intro i j p hp
    rcases hp with ⟨hq, hy, hrlo, hrhi⟩
    have hr : |p.2.2| ≤ ρ :=
      le_trans (abs_le.mpr ⟨hrlo, hrhi⟩) (min_le_left ρ 1)
    have hInv : ∀ x : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible := by
      intro x
      have hxnorm : ‖x.val‖ = (1 : ℝ) := by
        simpa only [Metric.mem_sphere, dist_zero_right] using x.property
      have hx : x.val ∈ closedBall (0 : R3) 2 := by
        simpa only [Metric.mem_closedBall, dist_zero_right, hxnorm] using
          (by norm_num : (1 : ℝ) ≤ 2)
      exact referenceFramedNormalizedJacobian_isInvertible_of_joint_framed_drift_data
        g L y0 Φ B ε C ρ H a w hData p.1 hq p.2.1 hy p.2.2 hr x.val hx
    have hSmooth :=
      contDiffAt_nativeThreeHalf_referenceJacobiBoundaryThreeHalfCoefficientFamily
        g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hInv
    have hAt : ContinuousAt (N i j) p := by
      simpa only [N] using hSmooth.continuousAt
    exact hAt.continuousWithinAt
  obtain ⟨C_N, hC_N, hBound⟩ :=
    exists_pos_compact_nine_norm_bound KJ hKJ N hN
  refine ⟨C_N, hC_N, ?_⟩
  intro q hq y hy r hr i j
  have hp : (q,(y,r)) ∈ KJ :=
    ⟨hq, hy, (abs_le.mp hr).1, (abs_le.mp hr).2⟩
  exact hBound (q,(y,r)) hp i j

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
