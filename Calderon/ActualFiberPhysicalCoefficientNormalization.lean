import Calderon.ActualPhysicalMetricNormalization
import Calderon.PositiveConformalMetric

/-! Full upfront: EXPANSION-actual-fiber-physical-coefficient-normalization-v001.json.
Literal first-metric physical coefficient and volume retain all conformal factors. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator DirichletFamily.DriftBootstrap

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hg hData

theorem principalCoefficient_referencePhysicalPullback_eq
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hr0 : r ≠ 0)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    principalCoefficient (pullbackMetric (fun x => g (q • x))
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x)))) z =
      |r| • (Real.exp (L*referenceRescaledDepth g L Φ (q,(y,r)) z) •
        matrixPrincipalCoefficient H ((q,(y,r)),z)) := by
  let Hp : MatrixField := fun x => H ((q,(y,r)),x)
  let f : R3 → ℝ := fun x => Real.log |r| + L*referenceRescaledDepth g L Φ (q,(y,r)) x
  have hMetric := pullbackMetric_referenceOriginal_eq_conformal g hg L y0 Φ B ε C ρ H a w hData
    q hq y hy r hr hr0 z hz
  have hCoeff : principalCoefficient (pullbackMetric (fun x => g (q • x))
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x)))) z =
      principalCoefficient (conformalMatrix Hp f) z :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => Real.sqrt M.det • M⁻¹) hMetric
  rcases hData.1 with ⟨_,_,_,_,_,_,_,hPos,_,_,_,_,_,_,_⟩
  have hConformal := principalCoefficient_conformalMatrix Hp f
    (fun x => hPos ((q,(y,r)),x)) z
  calc
    _ = Real.exp (f z) • principalCoefficient Hp z := hCoeff.trans hConformal
    _ = _ := by
      dsimp only [f]
      rw [Real.exp_add, Real.exp_log (abs_pos.mpr hr0), mul_smul]
      rfl

theorem vol_referencePhysicalPullback_eq
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hr0 : r ≠ 0)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    vol (pullbackMetric (fun x => g (q • x))
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x)))) z =
      |r|^3 * Real.exp (3*L*referenceRescaledDepth g L Φ (q,(y,r)) z) *
        matrixVolumeDensity H ((q,(y,r)),z) := by
  let Hp : MatrixField := fun x => H ((q,(y,r)),x)
  let f : R3 → ℝ := fun x => Real.log |r| + L*referenceRescaledDepth g L Φ (q,(y,r)) x
  have hMetric := pullbackMetric_referenceOriginal_eq_conformal g hg L y0 Φ B ε C ρ H a w hData
    q hq y hy r hr hr0 z hz
  have hVol : vol (pullbackMetric (fun x => g (q • x))
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x)))) z =
      vol (conformalMatrix Hp f) z :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => Real.sqrt M.det) hMetric
  have hLog : Real.exp (3*Real.log |r|) = |r|^3 := by
    have hArg : 3*Real.log |r| = Real.log |r| + Real.log |r| + Real.log |r| := by ring
    rw [hArg]
    simp only [Real.exp_add, Real.exp_log (abs_pos.mpr hr0)]
    ring
  have hExp : Real.exp (3*f z) =
      |r|^3 * Real.exp (3*L*referenceRescaledDepth g L Φ (q,(y,r)) z) := by
    dsimp only [f]
    rw [mul_add, Real.exp_add, hLog]
    congr 2
    ring
  calc
    _ = Real.exp (3*f z) * vol Hp z := hVol.trans (vol_conformalMatrix Hp f z)
    _ = _ := by rw [hExp]; rfl

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.principalCoefficient_referencePhysicalPullback_eq
#print axioms OAI.AnisotropicCalderon.ConnectionError.vol_referencePhysicalPullback_eq
