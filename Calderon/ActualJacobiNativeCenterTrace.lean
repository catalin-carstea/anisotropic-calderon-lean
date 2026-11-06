import Calderon.SphereContinuousScalarMultiplier
import Calderon.ActualNativeTraceOperatorFamily
import Calderon.ActualMovingNearBallHarmonicLift
import Calderon.ActualPhysicalBoundaryChainRule

/-! SAME actual Jacobi coefficients and physical center trace in the coarse
native bulk-H2 to sphere-L2 topology. No boundary order or Psi assertion. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator NormalCoordinatesFrame

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceJacobiSphereCoefficient (q : ℝ) (y : R3) (r : ℝ) (i j : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) : C(UnitSphere, ℝ) := by
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hEmbed : Continuous (fun x : UnitSphere => (q,((y,r),x.val))) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_subtype_val)
  refine ⟨fun x => referenceFramedJacobiVelocityRemainder g L Φ i (q,((y,r),x.val)) j,?_⟩
  apply continuous_iff_continuousAt.mpr
  intro x
  have hV : ContinuousAt (fun t : UnitSphere =>
      referenceFramedJacobiVelocityRemainder g L Φ i (q,((y,r),t.val))) x :=
    (contDiffAt_referenceFramedJacobiVelocityRemainder g hg L Φ hΘ i
      (q,((y,r),x.val)) (hInv x)).continuousAt.comp
        (f := fun t : UnitSphere => (q,((y,r),t.val))) hEmbed.continuousAt
  exact (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).continuous.continuousAt.comp
    (f := fun t : UnitSphere =>
      referenceFramedJacobiVelocityRemainder g L Φ i (q,((y,r),t.val))) hV

def referenceNativeJacobiTraceCorrection
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) :
    BallSobolev 2 →L[ℝ] SphereL2 :=
  ∑ j : Fin 3,
    (sphereContinuousScalarMulL
      (referenceJacobiSphereCoefficient g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)).comp
      (referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q j (y,r))

def referenceNativeCenterTraceOperator
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) :
    BallSobolev 2 →L[ℝ] SphereL2 :=
  r⁻¹ • referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i (y,r) +
  r • referenceNativeJacobiTraceCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q y r i hInv

def referenceJacobiDirectionalSphere (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible)
    (v : SmoothData) : C(UnitSphere, ℝ) :=
  ∑ j : Fin 3, referenceJacobiSphereCoefficient g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv *
    smoothSphereValue (smoothCoordinateDerivative v j)

theorem referenceJacobiDirectionalSphere_apply (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible)
    (v : SmoothData) (x : UnitSphere) :
    referenceJacobiDirectionalSphere g hg L y0 Φ B ε C ρ H a w hData q y r i hInv v x =
      fderiv ℝ v.1 x.val (referenceFramedJacobiVelocityRemainder g L Φ i (q,((y,r),x.val))) := by
  change (ContinuousMap.evalCLM ℝ x)
    (∑ j : Fin 3, referenceJacobiSphereCoefficient g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv *
      smoothSphereValue (smoothCoordinateDerivative v j)) = _
  rw [map_sum]
  exact (MetricVolume.covector_coordinate_sum (fderiv ℝ v.1 x.val)
    (referenceFramedJacobiVelocityRemainder g L Φ i (q,((y,r),x.val)))).symm

theorem norm_referenceNativeJacobiTraceCorrection_le
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) :
    ‖referenceNativeJacobiTraceCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q y r i hInv‖ ≤
      ∑ j : Fin 3,
        ‖referenceJacobiSphereCoefficient g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv‖ *
        ‖referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q j (y,r)‖ := by
  unfold referenceNativeJacobiTraceCorrection
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_sphereContinuousScalarMulL_le _) (norm_nonneg _))

theorem referenceNativeJacobiTraceCorrection_smooth
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible)
    (v : SmoothData)
    (hLift : referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r)
      (smoothBallSobolev 2 v) = smoothBallSobolev 2 v) :
    referenceNativeJacobiTraceCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q y r i hInv
      (smoothBallSobolev 2 v) =
        (ContinuousMap.toLp 2 sphereProbability ℝ)
          (referenceJacobiDirectionalSphere g hg L y0 Φ B ε C ρ H a w hData q y r i hInv v) := by
  have hS (j : Fin 3) : referenceNativeCoordinateTraceOperatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc τ0 q j (y,r) (smoothBallSobolev 2 v) =
      (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue (smoothCoordinateDerivative v j)) := by
    rw [referenceNativeCoordinateTraceOperatorFamily,ContinuousLinearMap.comp_apply,hLift]
    exact strongCoordinateTraceL_smooth hcalc τ0 j v
  simp only [referenceNativeJacobiTraceCorrection,sum_apply,ContinuousLinearMap.comp_apply]
  simp_rw [hS,sphereContinuousScalarMulL_toLp]
  exact (map_sum (ContinuousMap.toLp 2 sphereProbability ℝ) _ Finset.univ).symm

def referencePhysicalCenterHorizontalSphere (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (v : SmoothData) : C(UnitSphere, ℝ) := by
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hEmbed : ContDiff ℝ ∞ (fun z : R3 => (q,((y,r),z))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hX := (contDiff_referenceFramedPhysicalEndpoint g hg L Φ hΘ).comp hEmbed
  have hV := (contDiff_referenceFramedCenterHorizontalVelocity g hg L Φ hΘ i).comp hEmbed
  refine ⟨fun x => fderiv ℝ v.1 (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x.val)))
    (referenceFramedCenterHorizontalVelocity g L Φ i (q,((y,r),x.val))),?_⟩
  exact (((v.2.continuous_fderiv (by simp)).comp hX.continuous).clm_apply hV.continuous).comp
    continuous_subtype_val

theorem referenceNativeCenterTraceOperator_physical_smooth
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : (y,0) ∈ B) (r : ℝ) (hr : r ≠ 0)
    (i : Fin 3) (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible)
    (v : SmoothData)
    (hLift : referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r)
      (smoothBallSobolev 2 (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r v)) =
      smoothBallSobolev 2 (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r v)) :
    referenceNativeCenterTraceOperator g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q y r i hInv
      (smoothBallSobolev 2 (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r v)) =
        (ContinuousMap.toLp 2 sphereProbability ℝ)
          (referencePhysicalCenterHorizontalSphere g hg L y0 Φ B ε C ρ H a w hData q y r i v) := by
  let vPull := referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r v
  have hS : referenceNativeCoordinateTraceOperatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i (y,r) (smoothBallSobolev 2 vPull) =
      (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue (smoothCoordinateDerivative vPull i)) := by
    rw [referenceNativeCoordinateTraceOperatorFamily,ContinuousLinearMap.comp_apply,hLift]
    exact strongCoordinateTraceL_smooth hcalc τ0 i vPull
  have hJ := referenceNativeJacobiTraceCorrection_smooth
    g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q y r i hInv vPull hLift
  rw [referenceNativeCenterTraceOperator,add_apply,smul_apply,smul_apply,hS,hJ,
    ← map_smul,← map_smul,← map_add]
  apply congrArg (ContinuousMap.toLp 2 sphereProbability ℝ)
  ext x
  change r⁻¹ * fderiv ℝ vPull.1 x.val (coordinateVector i) +
    r * referenceJacobiDirectionalSphere g hg L y0 Φ B ε C ρ H a w hData q y r i hInv vPull x = _
  rw [referenceJacobiDirectionalSphere_apply]
  have hCenter := fderiv_referencePhysicalSphereValue_center_horizontal_decomposition
    g hg L y0 Φ B hData.1.1.1 q hq y x.val hy r hr i v (hInv x)
  dsimp only at hCenter
  rw [fderiv_referencePhysicalSphereValue_center_horizontal
    g hg L y0 Φ B hData.1.1.1 q y x.val r i v] at hCenter
  exact hCenter.symm

theorem exists_referenceNativeCenterTrace_of_near_ball_harmonic
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ < 4*ρ)
    (r : ℝ) (hr : |r| < 4*ρ) (hr0 : r ≠ 0)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r)).IsInvertible)
    (S : Set R3) (hS : IsOpen S) (u : R3 → ℝ) (hu : ContDiffOn ℝ ∞ u S)
    (hCover : (fun z => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z))) ''
      closedBall (0 : R3) 1 ⊆ S)
    (hphysical : ∀ x ∈ S,
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u) x = 0) :
    ∃ (v : SmoothData) (U : Set (R3 × ℝ)), HasCompactSupport v.1 ∧ IsOpen U ∧ (y,r) ∈ U ∧
      ∀ p ∈ U, ∀ hpB : (p.1,0) ∈ B,
        ∀ hInv : ∀ x : UnitSphere,
          (referenceFramedNormalizedJacobian g L Φ (q,(p,x.val))).IsInvertible,
        ∀ i : Fin 3,
          referenceNativeCenterTraceOperator g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q p.1 p.2 i hInv
            (smoothBallSobolev 2 (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q p.1 p.2 v)) =
              (ContinuousMap.toLp 2 sphereProbability ℝ)
                (referencePhysicalCenterHorizontalSphere g hg L y0 Φ B ε C ρ H a w hData q p.1 p.2 i v) ∧
          ∀ x : UnitSphere,
            referencePhysicalCenterHorizontalSphere g hg L y0 Φ B ε C ρ H a w hData q p.1 p.2 i v x =
              fderiv ℝ u (referenceFramedPhysicalEndpoint g L Φ (q,(p,x.val)))
                (referenceFramedCenterHorizontalVelocity g L Φ i (q,(p,x.val))) := by
  obtain ⟨v,U,hv,hU,hBase,hFamily⟩ := exists_referenceHarmonicLift_family_of_near_ball_harmonic
    g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 0 q hq y hy r hr hr0 hi S hS u hu hCover hphysical
  refine ⟨v,U,hv,hU,hBase,?_⟩
  intro p hp hpB hInv i
  obtain ⟨hY,hR,hNZ,hI,hCoverP,hNearP,hLift,hValue,hRad⟩ := hFamily p hp
  refine ⟨referenceNativeCenterTraceOperator_physical_smooth
    g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q hq p.1 hpB p.2 hNZ i hInv v hLift,?_⟩
  intro x
  have hn : ‖x.val‖ = 1 := by simpa [UnitSphere,Metric.sphere,dist_eq_norm] using x.property
  have hx : x.val ∈ closedBall (0 : R3) 1 := by
    simpa only [mem_closedBall,dist_zero_right,hn] using (le_refl (1 : ℝ))
  exact congrArg (fun F : R3 →L[ℝ] ℝ =>
    F (referenceFramedCenterHorizontalVelocity g L Φ i (q,(p,x.val)))) (hNearP x.val hx).fderiv_eq

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
