import Calderon.ActualNativeTraceGeometryRoom

/-! Full before-source: actual-covariant-leading-algebra-author-oct16-v001/
EXPANSION-actual-jacobi-coefficient-tube-cover-v036.md. -/
set_option autoImplicit false
noncomputable section
open Set Metric
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open ConnectionError MetricOperator NormalCoordinatesFrame

theorem referenceFramedNormalizedJacobian_isInvertible_on_actual_coefficient_tube
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (d : ℝ) (hd : 0 < d) (hdρ : d ≤ ρ) :
    ∀ point ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d),
      ∀ ξ : Metric.sphere (0 : R3) 1,
        (referenceFramedNormalizedJacobian g L Φ
          (point.1,(point.2,ξ.val))).IsInvertible := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-TUBE-COVER BODY_ENTER"
    out.flush
  intro point hp ξ
  have hρ : 0 < ρ := lt_of_lt_of_le hd hdρ
  have hρFour : ρ ≤ 4*ρ := by linarith only [hρ]
  have hy : ‖point.2.1-y0‖ ≤ ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hp.2.1
  have hr : |point.2.2| ≤ ρ := (abs_le.mpr hp.2.2).trans hdρ
  have hyFour : ‖point.2.1-y0‖ ≤ 4*ρ := hy.trans hρFour
  have hrFour : |point.2.2| ≤ 4*ρ := hr.trans hρFour
  have hξ : ‖ξ.val‖ = 1 := norm_eq_of_mem_sphere ξ
  have hξBall : ξ.val ∈ closedBall (0 : R3) 2 :=
    mem_closedBall_zero_iff.mpr
      (hξ.le.trans (show (1 : ℝ) ≤ 2 by norm_num))
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-TUBE-COVER FINITE_BOUNDS_READY"
    out.flush
  have hCover : (referenceFramedNormalizedJacobian g L Φ
      (point.1,(point.2,ξ.val))).IsInvertible :=
    referenceFramedNormalizedJacobian_isInvertible_on_actual_drift_room
      g L y0 Φ B ε C ρ H a w hData point.1 hp.1 point.2.1 hyFour
        point.2.2 hrFour ξ.val hξBall
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-TUBE-COVER COVER_READY"
    out.flush
  exact hCover

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
