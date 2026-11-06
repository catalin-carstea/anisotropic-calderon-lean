import Calderon.ActualPairedRadialRemainderThreeJetRoom
import Calderon.ActualJacobiNativeMultiplierJointJetBounds
import Calderon.ActualJacobiCoefficientTubeCover

/-! Full before-source: actual-covariant-leading-algebra-author-oct16-v001/
EXPANSION-common-paired-Jacobi-raw-room-implementation-v059.md.
Original paired room and three genuine Jacobi native endpoints; no profile allocation. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier

structure ReferencePairedRadialJacobiThreeJetRoom
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) where
  pairedRoom : ReferencePairedRadialRemainderThreeJetRoom
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  multiplierBounds : ReferenceJacobiNativeMultiplierJointJetBounds
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  multiplierProductSmooth :
    ∀ point ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ),
    ∀ i j : Fin 3,
      ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) =>
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryThreeHalfCoefficientFamily
            g hg L y0 Φ B ε C ρ H a w hData i j z),
         (nativeHalfCoefficientMulL hcalc hF hO hD τ0
           (referenceJacobiBoundaryCoefficientFamily
             g hg L y0 Φ B ε C ρ H a w hData i j z),
          nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
           (referenceJacobiBoundaryCoefficientFamily
             g hg L y0 Φ B ε C ρ H a w hData i j z)))) point
  multiplierProductBounds : ∀ k : ℕ, k ≤ 3 →
    ∀ point ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ),
    ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ k (fun z : ℝ × (R3 × ℝ) =>
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryThreeHalfCoefficientFamily
            g hg L y0 Φ B ε C ρ H a w hData i j z),
         (nativeHalfCoefficientMulL hcalc hF hO hD τ0
           (referenceJacobiBoundaryCoefficientFamily
             g hg L y0 Φ B ε C ρ H a w hData i j z),
          nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
           (referenceJacobiBoundaryCoefficientFamily
             g hg L y0 Φ B ε C ρ H a w hData i j z)))) point‖ ≤
        multiplierBounds.bound

theorem exists_referencePairedRadialJacobiThreeJetRoom
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) :
    Nonempty (ReferencePairedRadialJacobiThreeJetRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_JACOBI_RAW_ROOM BODY_ENTER"
    out.flush
  let paired := Classical.choice (exists_referencePairedRadialRemainderThreeJetRoom
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg)
  let multipliers := Classical.choice (exists_referenceJacobiNativeMultiplierJointJetBounds
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_JACOBI_RAW_ROOM RECORDS_READY"
    out.flush
  let Ktube : Set (ℝ × (R3 × ℝ)) :=
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)
  have hρ : 0 < ρ := paired.radius_pos.trans_le paired.radius_le
  have hCover := referenceFramedNormalizedJacobian_isInvertible_on_actual_coefficient_tube
    g L y0 Φ B ε C ρ H a w hData ρ hρ (le_refl ρ)
  have hHighSmooth (point : ℝ × (R3 × ℝ)) (hp : point ∈ Ktube) (i j : Fin 3) :=
    contDiffAt_nativeThreeHalf_referenceJacobiBoundaryThreeHalfCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j point (hCover point hp)
  have hHalfSmooth (point : ℝ × (R3 × ℝ)) (hp : point ∈ Ktube) (i j : Fin 3) :=
    contDiffAt_nativeHalf_referenceJacobiBoundaryCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j point (hCover point hp)
  have hNegativeSmooth (point : ℝ × (R3 × ℝ)) (hp : point ∈ Ktube) (i j : Fin 3) :=
    contDiffAt_nativeNegativeHalf_referenceJacobiBoundaryCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j point (hCover point hp)
  have hTupleSmooth (point : ℝ × (R3 × ℝ)) (hp : point ∈ Ktube) (i j : Fin 3) :=
    (hHighSmooth point hp i j).prodMk
      ((hHalfSmooth point hp i j).prodMk (hNegativeSmooth point hp i j))
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_JACOBI_RAW_ROOM TUPLE_SMOOTH_READY"
    out.flush
  have hTupleBounds : ∀ k : ℕ, k ≤ 3 →
    ∀ point ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ),
    ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ k (fun z : ℝ × (R3 × ℝ) =>
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryThreeHalfCoefficientFamily
            g hg L y0 Φ B ε C ρ H a w hData i j z),
         (nativeHalfCoefficientMulL hcalc hF hO hD τ0
           (referenceJacobiBoundaryCoefficientFamily
             g hg L y0 Φ B ε C ρ H a w hData i j z),
          nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
           (referenceJacobiBoundaryCoefficientFamily
             g hg L y0 Φ B ε C ρ H a w hData i j z)))) point‖ ≤
        multipliers.bound := by
    intro k hk point hp i j
    have hInnerDerivative := iteratedFDeriv_prodMk
      (hHalfSmooth point hp i j) (hNegativeSmooth point hp i j) (i := k) (by simp)
    have hOuterDerivative := iteratedFDeriv_prodMk
      (hHighSmooth point hp i j)
      ((hHalfSmooth point hp i j).prodMk (hNegativeSmooth point hp i j))
      (i := k) (by simp)
    have hInnerNorm := (congrArg norm hInnerDerivative).trans
      (ContinuousMultilinearMap.opNorm_prod _ _)
    have hOuterNorm := (congrArg norm hOuterDerivative).trans
      (ContinuousMultilinearMap.opNorm_prod _ _)
    exact hOuterNorm.trans_le (max_le (multipliers.highBound k hk point hp i j)
      (hInnerNorm.trans_le (max_le (multipliers.halfBound k hk point hp i j)
        (multipliers.negativeBound k hk point hp i j))))
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_JACOBI_RAW_ROOM TUPLE_BOUND_READY"
    out.flush
  exact ⟨{
    pairedRoom := paired
    multiplierBounds := multipliers
    multiplierProductSmooth := hTupleSmooth
    multiplierProductBounds := hTupleBounds
  }⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referencePairedRadialJacobiThreeJetRoom
