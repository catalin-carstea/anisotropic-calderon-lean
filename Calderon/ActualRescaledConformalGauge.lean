import Calderon.JointConformalReferenceFramedDriftData
import Calderon.ConformalFluxDivergence

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator EnergyBridge DirichletFamily.DriftBootstrap

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (H : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)

def referenceRescaledDepth (p : ℝ × (R3 × ℝ)) (z : R3) : ℝ :=
  conformalReferenceCoordinateDepth
    (parameterFramedScaledEndpoint (fun t => (Φ t.1 t.2 1).1)
      (conformalReferenceGramFrameOperatorJoint g L) (p,z))

def referenceRescaledFlux (p : ℝ × (R3 × ℝ)) (u : R3 → ℝ) : R3 → R3 :=
  metricDivergenceFlux (fun z => H (p,z)) u

def referenceRescaledPositiveExpression (p : ℝ × (R3 × ℝ))
    (u : R3 → ℝ) (z : R3) : ℝ :=
  -coordinateFluxDivergence (referenceRescaledFlux H p u) z +
    inner ℝ (conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) (gradient u z)

def referenceRescaledConformalPositiveExpression (p : ℝ × (R3 × ℝ))
    (u : R3 → ℝ) (z : R3) : ℝ :=
  -coordinateFluxDivergence
    (metricDivergenceFlux (conformalMatrix (fun x => H (p,x))
      (fun x => L*referenceRescaledDepth g L Φ p x)) u) z

variable (hg : IsAdmissibleMetric g) (y0 : R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData in
theorem fderiv_referenceRescaledDepth_apply (p : ℝ × (R3 × ℝ)) (z v : R3) :
    fderiv ℝ (referenceRescaledDepth g L Φ p) z v =
      p.2.2 * fderiv ℝ conformalReferenceCoordinateDepth
        (parameterFramedScaledEndpoint (fun t => (Φ t.1 t.2 1).1)
          (conformalReferenceGramFrameOperatorJoint g L) (p,z))
        (parameterFramedNormalizedEndpointDerivative (fun t => (Φ t.1 t.2 1).1)
          (conformalReferenceGramFrameOperatorJoint g L) (p,z) v) := by
  rcases p with ⟨q,y,r⟩
  rcases hData.1.1.1 with ⟨_,_,_,_,_,_,_,hEnd,_,_,_⟩
  let Θ : R3 × R3 → R3 := fun t => (Φ q t 1).1
  let F : R3 → R3 →L[ℝ] R3 := fun x => conformalReferenceGramFrameOperatorJoint g L (q,x)
  let X : R3 → R3 := fun x => Θ (y,r • F y x)
  let J : R3 →L[ℝ] R3 := framedNormalizedEndpointDerivative Θ F ((y,r),z)
  have hΘ : ContDiff ℝ ∞ Θ := hEnd.comp (contDiff_const.prodMk contDiff_id)
  have hX : HasFDerivAt X (r • J) z :=
    hasFDerivAt_framedScaledEndpoint_slice Θ F hΘ y z r
  have hDepth : referenceRescaledDepth g L Φ (q,(y,r)) =
      conformalReferenceCoordinateDepth ∘ X := by
    funext x
    rfl
  have hPoint : parameterFramedScaledEndpoint (fun t => (Φ t.1 t.2 1).1)
      (conformalReferenceGramFrameOperatorJoint g L) ((q,(y,r)),z) = X z := rfl
  have hJ : parameterFramedNormalizedEndpointDerivative (fun t => (Φ t.1 t.2 1).1)
      (conformalReferenceGramFrameOperatorJoint g L) ((q,(y,r)),z) = J := rfl
  have hD : HasFDerivAt (conformalReferenceCoordinateDepth ∘ X)
      ((fderiv ℝ conformalReferenceCoordinateDepth (X z)).comp (r • J)) z :=
    (contDiff_conformalReferenceCoordinateDepth.differentiable (by simp)
      (X z)).hasFDerivAt.comp z hX
  have hEq : fderiv ℝ (conformalReferenceCoordinateDepth ∘ X) z =
      (fderiv ℝ conformalReferenceCoordinateDepth (X z)).comp (r • J) := hD.fderiv
  have hApply : fderiv ℝ (conformalReferenceCoordinateDepth ∘ X) z v =
      r * fderiv ℝ conformalReferenceCoordinateDepth (X z) (J v) := by
    rw [hEq]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
      map_smul,smul_eq_mul]
  rw [hDepth,hPoint,hJ]
  exact hApply

include hg hData in
theorem referenceRescaledWeightedDrift_pairing
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2)
    (u : R3 → ℝ) :
    inner ℝ (conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z))
      (gradient u z) =
    -L*fderiv ℝ (referenceRescaledDepth g L Φ (q,(y,r))) z
      (referenceRescaledFlux H (q,(y,r)) u z) := by
  have hDataCopy := hData
  rcases hDataCopy with ⟨hPositive,_,_,_,_,hBeta,_,_,_,_,hMetric,_,_,_⟩
  rcases hPositive with ⟨_,_,_,_,_,_,_,hPos,_,_,_,hLocal,_,_,_⟩
  let p : ℝ × (R3 × ℝ) := (q,(y,r))
  let G : R3 →L[ℝ] R3 := referenceFramedNormalOperatorForCoefficients g L Φ (p,z)
  let D : R3 := conformalReferenceFramedDrift g L Φ H (p,z)
  let J : R3 →L[ℝ] R3 := parameterFramedNormalizedEndpointDerivative (fun t => (Φ t.1 t.2 1).1)
    (conformalReferenceGramFrameOperatorJoint g L) (p,z)
  let X : R3 := parameterFramedScaledEndpoint (fun t => (Φ t.1 t.2 1).1)
    (conformalReferenceGramFrameOperatorJoint g L) (p,z)
  let v : R3 := matrixOperatorMap ((H (p,z))⁻¹) (gradient u z)
  have hLocalz := hLocal q hq y hy r hr z hz
  have hHG : matrixOperatorMap (H (p,z)) = G := by
    rw [hLocalz.1]
    apply ContinuousLinearMap.ext
    intro V
    exact operatorMatrixMap_apply G V
  have hwvol : vol (fun x => H (p,x)) z = w (p,z) := by
    change Real.sqrt (H (p,z)).det = w (p,z)
    rw [hLocalz.1]
    exact hLocalz.2.2.symm
  have hV : G v = gradient u z := by
    rw [← hHG]
    exact matrixOperatorMap_inverse_cancel (H (p,z)) (hPos (p,z)) _
  have hSym (V W : R3) : inner ℝ (G V) W = inner ℝ (G W) V :=
    referenceFramedNormalOperatorForCoefficients_symmetric g hg L Φ (p,z) V W
  have hMetricPoint : referenceFramedNormalOperatorForCoefficients g L Φ ((q,(y,r)),z)
      (conformalReferenceFramedDrift g L Φ H ((q,(y,r)),z)) =
      (-L*r) • ((parameterFramedNormalizedEndpointDerivative (fun t => (Φ t.1 t.2 1).1)
        (conformalReferenceGramFrameOperatorJoint g L) ((q,(y,r)),z)).adjoint
          (gradient conformalReferenceCoordinateDepth
            (parameterFramedScaledEndpoint (fun t => (Φ t.1 t.2 1).1)
              (conformalReferenceGramFrameOperatorJoint g L) ((q,(y,r)),z)))) :=
    hMetric q hq y hy r hr z hz
  have hD : G D = (-L*r) • (J.adjoint (gradient conformalReferenceCoordinateDepth X)) := by
    dsimp only [G,D,J,X,p]
    exact hMetricPoint
  have hWeighted : conformalReferenceWeightedFramedDrift g L Φ H w (p,z) =
      w (p,z) • D := by
    dsimp only [D]
    exact hBeta (p,z)
  have hFlux : referenceRescaledFlux H p u z = w (p,z) • v := by
    simp only [referenceRescaledFlux,metricDivergenceFlux,principalCoefficient,
      hwvol,map_smul,ContinuousLinearMap.smul_apply]
    rfl
  have hInner : inner ℝ D (gradient u z) =
      (-L*r)*inner ℝ (gradient conformalReferenceCoordinateDepth X) (J v) := by
    calc
      _ = inner ℝ D (G v) := congrArg (fun x : R3 => inner ℝ D x) hV.symm
      _ = inner ℝ (G v) D := (real_inner_comm D (G v)).symm
      _ = inner ℝ (G D) v := (hSym D v).symm
      _ = _ := by
        rw [hD,real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left]
  have hPair : inner ℝ (conformalReferenceWeightedFramedDrift g L Φ H w (p,z))
      (gradient u z) =
      w (p,z)*(-L*r)*inner ℝ (gradient conformalReferenceCoordinateDepth X) (J v) := by
    rw [hWeighted,real_inner_smul_left,hInner]
    ring
  change inner ℝ (conformalReferenceWeightedFramedDrift g L Φ H w (p,z))
    (gradient u z) = -L*fderiv ℝ (referenceRescaledDepth g L Φ p) z
      (referenceRescaledFlux H p u z)
  rw [hPair,fderiv_referenceRescaledDepth_apply g L Φ H w y0 B ε C ρ a hData,
    hFlux,map_smul,map_smul,smul_eq_mul,← inner_gradient_left]
  ring

include hg hData in
theorem referenceRescaledConformalPositiveExpression_eq
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2)
    (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u) :
    referenceRescaledConformalPositiveExpression g L Φ H (q,(y,r)) u z =
      Real.exp (L*referenceRescaledDepth g L Φ (q,(y,r)) z) *
        referenceRescaledPositiveExpression g L Φ H w (q,(y,r)) u z := by
  rcases hData.1 with ⟨hNormal,_,_,_,_,_,hH,hPos,_,_,_,_,_,_,_⟩
  rcases hNormal with ⟨hEndpoint,_,_,hF,_,_,_,_⟩
  rcases hEndpoint with ⟨_,_,_,_,_,_,_,hEnd,_,_,_⟩
  let p : ℝ × (R3 × ℝ) := (q,(y,r))
  let t := referenceRescaledDepth g L Φ p
  let Z := referenceRescaledFlux H p u
  have hT : ContDiff ℝ ∞ t := contDiff_conformalReferenceCoordinateDepth.comp
    ((contDiff_parameterFramedScaledEndpoint (fun v => (Φ v.1 v.2 1).1)
      (conformalReferenceGramFrameOperatorJoint g L) hEnd hF).comp
        (contDiff_const.prodMk contDiff_id))
  have hHs : ContDiff ℝ ∞ (fun x => H (p,x)) :=
    hH.comp (contDiff_const.prodMk contDiff_id)
  have hZ : ContDiff ℝ ∞ Z := contDiff_metricDivergenceFlux (fun x => H (p,x))
    (fun i j => contDiff_pi.mp (contDiff_pi.mp hHs i) j)
    (fun x => hPos (p,x)) u hu
  have hflux : metricDivergenceFlux (conformalMatrix (fun x => H (p,x))
      (fun x => L*t x)) u = fun x => Real.exp (L*t x) • Z x := by
    funext x
    simp only [metricDivergenceFlux,principalCoefficient_conformalMatrix _ _
      (fun x => hPos (p,x)),map_smul,ContinuousLinearMap.smul_apply]
    rfl
  have hdiv := coordinateFluxDivergence_exp_depth t Z (-L) z
    (hT.differentiable (by simp) z) (hZ.differentiable (by simp) z)
  simp only [neg_neg] at hdiv
  change -coordinateFluxDivergence (metricDivergenceFlux
    (conformalMatrix (fun x => H (p,x)) (fun x => L*t x)) u) z =
      Real.exp (L*t z) * (-coordinateFluxDivergence Z z +
        inner ℝ (conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) (gradient u z))
  rw [hflux,hdiv,referenceRescaledWeightedDrift_pairing g L Φ H w hg y0 B ε C ρ a hData
    q hq y hy r hr z hz u]
  ring

include hData in
theorem referenceRescaledConformalForcingWeight_eq
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    vol (conformalMatrix (fun x => H ((q,(y,r)),x))
      (fun x => L*referenceRescaledDepth g L Φ (q,(y,r)) x)) z /
        Real.exp (2*L*referenceRescaledDepth g L Φ (q,(y,r)) z) =
      Real.exp (L*referenceRescaledDepth g L Φ (q,(y,r)) z) * w ((q,(y,r)),z) := by
  rcases hData.1 with ⟨_,_,_,_,_,_,_,_,_,_,_,hLocal,_,_,_⟩
  let p : ℝ × (R3 × ℝ) := (q,(y,r))
  let t := referenceRescaledDepth g L Φ p z
  have hLocalz := hLocal q hq y hy r hr z hz
  have hwvol : vol (fun x => H (p,x)) z = w (p,z) := by
    change Real.sqrt (H (p,z)).det = w (p,z)
    rw [hLocalz.1]
    exact hLocalz.2.2.symm
  rw [vol_conformalMatrix,hwvol]
  change Real.exp (3*(L*t))*w (p,z) / Real.exp (2*L*t) = Real.exp (L*t)*w (p,z)
  calc
    _ = (Real.exp (3*(L*t)) / Real.exp (2*L*t))*w (p,z) := by ring
    _ = _ := by
      rw [← Real.exp_sub]
      congr 2
      ring

end OAI.AnisotropicCalderon.ConnectionError
