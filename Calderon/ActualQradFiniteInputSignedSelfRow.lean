import Calderon.ActualQradJointCoefficientCaps
import Calderon.ActualRadialCoefficientDiagonalCaps
import Calderon.QradFourIndexNormIdentity
import Calderon.ActualAdjacentGainedBracket
import Calderon.ActualRadialCoefficientPivots
import Calderon.ActualQradFiniteFirstOutputLifts
import Calderon.ActualAdjacentGainedFiniteFamilyCaps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual physical Qrad signed self-row.
Uses only first-output lifts, the CL bracket, radial coefficient pivots,
finite-family adjacent caps, and QradFourIndexNormIdentity/WeakForm. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology InnerProductSpace

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  SmoothSphereRotation NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)

attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceSharpRadialTraceFamily referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  referenceSharpRadialTraceSecondRemainder referenceLowerRadialTraceSecondRemainder
  secondTaylorRemainder sphereSobolevInclusionL nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL realHalfOperatorAdjointL harmonicSphereSubspace
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceGaugeNormalHighInvertibleLocus
  referenceRadialAdjointSharpSecondCommutatorHigh referenceRadialAdjointSharpSecondCommutator
  referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
  referenceAdjacentGainedCommutatorHigh referenceAdjacentGainedCommutatorLow

attribute [local instance] adjacentGainThreeHalfComplete adjacentGainHalfComplete adjacentGainNegativeHalfComplete adjacentGainHighHighComplete adjacentGainHighHalfComplete adjacentGainHalfHalfComplete adjacentGainHalfNegComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
  (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))))

local notation "Ihi" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "Jlo" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "Z0" => sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
local notation "Sh" => referenceSharpRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Sl" => referenceLowerRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "NMH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NML" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NMN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "RAH" => referenceAdjointThreeHalfRadialFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "RAL" => referenceAdjointHalfRadialFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "CH" => referenceAdjacentGainedCommutatorHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "CL" => referenceAdjacentGainedCommutatorLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room

attribute [local irreducible] commonSupportCoefficientFamily

/-! ### §§3–5 Actual Qrad identification and signed self-row at one physical point. -/

attribute [local irreducible] sphereSobolevPartialSum qradSignedWeakSelfExpression qradFourIndexWeakForm

include hg in
theorem exists_reference_commonRadius_qrad_signed_selfRow_finite_input
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (T : Type) [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T] :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ (m : Fin 3 → T × R3 → ℝ) (hm : ∀ i, ContDiff ℝ ∞ (m i))
        (Km : Set R3) (hKm : IsCompact Km)
        (hmz : ∀ i t x, x ∉ Km → m i (t,x) = 0) (Kt : Set T), IsCompact Kt →
        ∀ MQ : ℝ, 0 ≤ MQ →
        ∃ Cst : ℝ, 0 ≤ Cst ∧
          ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ d → ∀ t ∈ Kt,
          ∀ Q : Fin 3 → Fin 3 → ℝ, (∀ i j, |Q i j| ≤ MQ) →
          ∀ (n : ℕ) (f : Hi),
            let u : Hi := sphereSobolevPartialSum (3/2 : ℝ) n f
            let Th := secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r
            let Tl := secondTaylorRemainder (fun s : ℝ => RAL (q,(y,s))) r
            let RH : Fin 3 → Hi →L[ℝ] Half := fun i =>
              Th.comp (NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t))
            let LH : Fin 3 → Hi →L[ℝ] Half := fun i =>
              (NML (smoothMultiplierLowerJets
                (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t))).comp (Sh q y r)
            let RL : Fin 3 → Half →L[ℝ] Neg := fun i =>
              Tl.comp (NML (smoothMultiplierLowerJets
                (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t)))
            let LL : Fin 3 → Half →L[ℝ] Neg := fun i =>
              (NMN (smoothMultiplierLowerJets
                (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t))).comp (Sl q y r)
            let CHf : Fin 3 → Fin 3 → Hi →L[ℝ] Half := fun i k =>
              CH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t)
                (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) t) q y r
            let CLf : Fin 3 → Fin 3 → Half →L[ℝ] Neg := fun i k =>
              CL (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t)
                (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) t) q y r
            ∃ rL lL : Fin 3 → Hi,
              (∀ i, Ihi (rL i) = RH i u) ∧ (∀ i, Ihi (lL i) = LH i u) ∧
              -- physical Qrad = r^3 Σ Q_ij T P_i T P_j, literal low composition
              Jlo (r^3 • ∑ i, ∑ j, Q i j • RH i (rL j)) =
                r^3 • ∑ i, ∑ j, Q i j • RL i (RH j u) ∧
              -- physical Qrad† = r^3 Σ Q_ij P_j S P_i S, literal low composition
              Jlo (r^3 • ∑ i, ∑ j, Q i j • LH j (lL i)) =
                r^3 • ∑ i, ∑ j, Q i j • LL j (LH i u) ∧
              qradSignedWeakSelfExpression RH LH LL CHf CLf Q r u =
                ‖r^3 • ∑ i, ∑ j, Q i j • Z0 (RH i (rL j))‖^2 -
                  ‖r^3 • ∑ i, ∑ j, Q i j • Z0 (LH j (lL i))‖^2 ∧
              |‖r^3 • ∑ i, ∑ j, Q i j • Z0 (RH i (rL j))‖^2 -
                  ‖r^3 • ∑ i, ∑ j, Q i j • Z0 (LH j (lL i))‖^2| ≤ Cst * r^6 * ‖u‖^2 := by
  have hRootSelected1 := exists_reference_commonRadius_referenceAdjacentGainedCommutatorLow_bracket
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel
  rcases hRootSelected1 with ⟨dB,hdB,hdBρ,hBr⟩
  have hJointFull := exists_reference_commonRadius_joint_radial_and_gained_coefficient_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel T
  rcases hJointFull with ⟨dCF,hdCF,_,hJoint⟩
  let dF := dCF
  let dC := dCF
  have hdF : 0 < dF := hdCF
  have hdC : 0 < dC := hdCF
  have hRootSelected3 := exists_reference_commonRadius_finite_radial_coefficient_first_output_lifts
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel
  rcases hRootSelected3 with ⟨dLf,hdLf,_,hLift⟩
  have hRootSelected5 := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  rcases hRootSelected5 with ⟨lam,Lam,d0,_,hd0,_,hRoom0⟩
  refine ⟨min dB (min dF (min dLf (min dC (d0/2)))),
    lt_min hdB (lt_min hdF (lt_min hdLf (lt_min hdC (half_pos hd0)))),
    (min_le_left _ _).trans hdBρ, ?_⟩
  intro m hm Km hKm hmz Kt hKt MQ hMQ
  have hJointSelected := hJoint m hm Km hKm hmz Kt hKt
  rcases hJointSelected with ⟨M0,hM0,hCapC,hFamC⟩
  let MD := M0
  let MF := M0
  have hMD : 0 ≤ MD := hM0
  have hMF : 0 ≤ MF := hM0
  let Mall := max (max MD MF) MQ
  have hMallDef : Mall = max (max MD MF) MQ := rfl
  have hMDle : MD ≤ Mall := by rw [hMallDef]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hMFle : MF ≤ Mall := by rw [hMallDef]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hMQle : MQ ≤ Mall := by rw [hMallDef]; exact le_max_right _ _
  have hMall : 0 ≤ Mall := hMQ.trans hMQle
  refine ⟨324*Mall^5, mul_nonneg (by norm_num) (pow_nonneg hMall 5), ?_⟩
  intro q hq y hy r hr t ht Q hQ n f
  intro u Th Tl RH LH RL LL CHf CLf
  have hrB : |r| ≤ dB := hr.trans (min_le_left _ _)
  have hrF : |r| ≤ dF := hr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrL : |r| ≤ dLf :=
    hr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrC : |r| ≤ dC := hr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hr2 : |r| ≤ d0/2 := hr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hr0 : |r| < d0 := hr2.trans_lt (by linarith)
  have hyBall : y ∈ closedBall y0 ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hScaled (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : |θ*r| ≤ d0 := by
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_right hθabs (abs_nonneg r)).trans_eq (one_mul _)).trans hr0.le
  have hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    fun θ hθ => (hRoom0 (q,(y,θ*r)) ⟨hq,hyBall,abs_le.mp (hScaled θ hθ)⟩).2.2.1
  have hpC : (q,(y,r)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dC) dC) :=
    ⟨hq,hyBall,abs_le.mp hrC⟩
  have hpF : (q,(y,r)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dF) dF) :=
    ⟨hq,hyBall,abs_le.mp hrF⟩
  -- §3 actual hypotheses of the conditional identity
  have hR : ∀ (i : Fin 3) (v : Hi), Jlo (RH i v) = RL i (Ihi v) := fun i v =>
    (referenceRadialCoefficient_genuine_graphs_and_pivot_pairings g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 hreg (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t)
        q y r hSegment).1 v
  have hL : ∀ (i : Fin 3) (v : Hi), Jlo (LH i v) = LL i (Ihi v) := fun i v =>
    (referenceRadialCoefficient_genuine_graphs_and_pivot_pairings g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 hreg (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t)
        q y r hSegment).2.1 v
  have hLAdj : ∀ (i : Fin 3) (z : Half) (v : Hi),
      sphereSobolevDualPairing (-(1/2 : ℝ)) (LL i z) (Ihi v) = ⟪Z0 z, Z0 (RH i v)⟫_ℝ :=
    fun i z v =>
    (referenceRadialCoefficient_genuine_graphs_and_pivot_pairings g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 hreg (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t)
        q y r hSegment).2.2.1 z v
  have hRAdj : ∀ (i : Fin 3) (z : Half) (v : Hi),
      sphereSobolevDualPairing (-(1/2 : ℝ)) (RL i z) (Ihi v) = ⟪Z0 z, Z0 (LH i v)⟫_ℝ :=
    fun i z v =>
    (referenceRadialCoefficient_genuine_graphs_and_pivot_pairings g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 hreg (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t)
        q y r hSegment).2.2.2 z v
  have hC : ∀ (i k : Fin 3) (v : Hi), Jlo (CHf i k v) = CLf i k (Ihi v) := fun i k v =>
    (hFamC i k (q,(y,r)) hpF t ht t ht).2.2.2.2 v
  have hBracket : ∀ (i k : Fin 3) (v : Hi),
      CLf i k (Ihi v) = LL i (RH k v) - RL k (LH i v) := fun i k v =>
    hBr (m i) (hm i) Km hKm (hmz i) t
      (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) t) q hq y hy r hrB v
  -- genuine finite-input first-output representatives
  have hRootSelected8 := hLift q hq y hy r hrL n
    (fun i => commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t) f
  rcases hRootSelected8 with ⟨rL,lL,hrLift,hlLift⟩
  have hr' : ∀ i, Ihi (rL i) = RH i u := hrLift
  have hl' : ∀ i, Ihi (lL i) = LH i u := hlLift
  -- caps on the common room
  have hRHc : ∀ i, ‖RH i‖ ≤ Mall := fun i =>
    ((hCapC i (q,(y,r)) hpC t ht).2.2.2.2.1).trans hMDle
  have hLHc : ∀ i, ‖LH i‖ ≤ Mall := fun i =>
    ((hCapC i (q,(y,r)) hpC t ht).2.2.2.2.2.1).trans hMDle
  have hLLc : ∀ i, ‖LL i‖ ≤ Mall := fun i =>
    ((hCapC i (q,(y,r)) hpC t ht).2.2.2.2.2.2.2).trans hMDle
  have hCHc : ∀ i k, ‖CHf i k‖ ≤ Mall := fun i k =>
    ((hFamC i k (q,(y,r)) hpF t ht t ht).2.2.1).trans hMFle
  have hCLc : ∀ i k, ‖CLf i k‖ ≤ Mall := fun i k =>
    ((hFamC i k (q,(y,r)) hpF t ht t ht).2.2.2.1).trans hMFle
  have hQc : ∀ i j, |Q i j| ≤ Mall := fun i j => (hQ i j).trans hMQle
  -- §5 norm fold and 324 bound
  have hNorm := qradSignedWeakSelfExpression_eq_cubic_norm_difference
    RH LH RL LL CHf CLf hR hL hC hBracket hLAdj hRAdj Q r u rL lL hr' hl'
  have hAbs := abs_qradSignedWeakSelfExpression_le RH LH LL CHf CLf Q Mall hMall
    hRHc hLHc hLLc hCHc hCLc hQc r u
  refine ⟨rL,lL,hr',hl',?_,?_,hNorm,?_⟩
  · -- §4 physical Qrad output at the Neg endpoint
    simp only [map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact congrArg (fun z : Neg => Q i j • z) ((hR i (rL j)).trans (congrArg (RL i) (hr' j)))
  · -- §4 physical adjoint output at the Neg endpoint
    simp only [map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact congrArg (fun z : Neg => Q i j • z) ((hL j (lL i)).trans (congrArg (LL j) (hl' i)))
  · rw [← hNorm]
    exact hAbs

/-- Profile form at one point: `β ≥ 1`, `|r| β² ≤ θ ≤ 1` (highCore inequality). -/
theorem qrad_signed_selfRow_profile_bound {D Cst r β θ N : ℝ} (hCst : 0 ≤ Cst) (hN : 0 ≤ N)
    (hD : |D| ≤ Cst * r^6 * N) (hβ : 1 ≤ β) (hrθ : |r| * β^2 ≤ θ) (hθ : θ ≤ 1) :
    |D| ≤ Cst * θ * β * N :=
  abs_le_theta_beta_of_radial_pow_six hCst hN hD hβ hrθ hθ

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
