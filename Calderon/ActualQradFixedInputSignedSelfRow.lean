import Calderon.ActualQradFiniteInputSignedSelfRow
import Calderon.ActualQradJointCoefficientCaps
import Calderon.ActualRadialCoefficientDiagonalCaps
import Calderon.QradFourIndexNormIdentity
import Calderon.ActualAdjacentGainedBracket
import Calderon.ActualRadialCoefficientPivots
import Calderon.ActualQradFiniteFirstOutputLifts
import Calderon.ActualAdjacentGainedFiniteFamilyCaps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual physical Qrad signed self-row (author-only candidate, v008).
Complete expansion: output/MATHEMATICS.md, written before these declarations.
Uses ONLY the Root producers: first-output lifts, CL bracket, radial coefficient pivots,
finite-family adjacent caps, plus the checked QradFourIndexNormIdentity/WeakForm.
No compiler was run; no acceptance is claimed. -/
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
theorem exists_reference_commonRadius_qrad_signed_selfRow_fixed_input
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
          ∀ (n : ℕ) (f : Hi), sphereSobolevPartialSum (3/2 : ℝ) n f = f →
            let u : Hi := f
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
  have hFull := exists_reference_commonRadius_qrad_signed_selfRow_finite_input
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel T
  rcases hFull with ⟨d,hd,hdρ,hA⟩
  refine ⟨d,hd,hdρ,?_⟩
  intro m hm Km hKm hmz Kt hKt MQ hMQ
  have hSelected := hA m hm Km hKm hmz Kt hKt MQ hMQ
  rcases hSelected with ⟨Cst,hCst,hPt⟩
  refine ⟨Cst,hCst,?_⟩
  intro q hq y hy r hr t ht Q hQ n f hcut
  have h := hPt q hq y hy r hr t ht Q hQ n f
  simpa only [hcut] using h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
