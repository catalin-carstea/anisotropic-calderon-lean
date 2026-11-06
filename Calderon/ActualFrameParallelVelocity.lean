import Calderon.ActualFramedJacobiVelocityJets
import Calderon.MovingFrameConnection

/-! Source-only realization of the same physical phase velocity by the actual
negative moving-frame connection direction. No constant-vector proxy is used. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator NormalCoordinatesFrame SmoothMetricFrame MovingFrameConnection

/-- Actual frame-coordinate velocity of a metric-parallel physical vector. -/
def framedParallelAngularVelocity (F : R3 → R3 →L[ℝ] R3)
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (y X z : R3) : R3 :=
  -ContinuousLinearMap.inverse (F y)
    (fderiv ℝ F y X z + Γ y X (F y z))

theorem frame_apply_parallelAngularVelocity (F : R3 → R3 →L[ℝ] R3)
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (y X z : R3) (hF : (F y).IsInvertible) :
    F y (framedParallelAngularVelocity F Γ y X z) =
      -(fderiv ℝ F y X z + Γ y X (F y z)) := by
  unfold framedParallelAngularVelocity
  rw [map_neg]
  have hi := congrArg (fun A : R3 →L[ℝ] R3 =>
    A (fderiv ℝ F y X z + Γ y X (F y z))) hF.self_comp_inverse
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using
    congrArg Neg.neg hi

/-- Columns of the actual sphere velocity are minus the canonical kappa coefficients. -/
theorem framedParallelAngularVelocity_frame_component
    (M : R3 → R3 →L[ℝ] R3)
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (e : R3 → Fin 3 → R3)
    (hF : ContDiff ℝ ∞ (fun x => frameOperator (e x)))
    (y X : R3) (he : IsMetricOrthonormalFrame (M y) (e y))
    (a b : Fin 3) :
    inner ℝ (framedParallelAngularVelocity (fun x => frameOperator (e x)) Γ
      y X (coordinateVector b)) (coordinateVector a) =
      -frameConnectionCoefficient M Γ e y X a b := by
  let F : R3 → R3 →L[ℝ] R3 := fun x => frameOperator (e x)
  have hInv : (F y).IsInvertible :=
    isInvertible_compactChart_endomorphism _ (frameOperator_injective _ _ he)
  have hEval : fderiv ℝ F y X (coordinateVector b) =
      fderiv ℝ (fun x => e x b) y X := by
    let A : (R3 →L[ℝ] R3) →L[ℝ] R3 :=
      ContinuousLinearMap.apply ℝ R3 (coordinateVector b)
    have hFAt : HasFDerivAt F (fderiv ℝ F y) y :=
      (hF.differentiable (by simp) y).hasFDerivAt
    have hd : HasFDerivAt (fun x : R3 => F x (coordinateVector b))
        (A.comp (fderiv ℝ F y)) y :=
      A.hasFDerivAt.comp y hFAt
    have heq : (fun x => F x (coordinateVector b)) = (fun x => e x b) :=
      funext (fun x => frameOperator_coordinateVector (e x) b)
    rw [heq] at hd
    have ha := congrArg (fun B : R3 →L[ℝ] R3 => B X) hd.fderiv
    change fderiv ℝ (fun x => e x b) y X =
      fderiv ℝ F y X (coordinateVector b) at ha
    exact ha.symm
  have hp := metric_inner_frameOperator (M y) (e y) he
    (framedParallelAngularVelocity F Γ y X (coordinateVector b)) (coordinateVector a)
  rw [frame_apply_parallelAngularVelocity F Γ y X (coordinateVector b) hInv] at hp
  simp only [F,frameOperator_coordinateVector,hEval] at hp
  rw [← hp]
  simp only [frameConnectionCoefficient,covariantFrameDerivative,map_neg,inner_neg_left]

/-- Chain rule for the actual moving center and negative frame-connection sphere direction. -/
theorem fderiv_framedEndpoint_parallel_horizontal
    (Θ : R3 × R3 → R3) (F : R3 → R3 →L[ℝ] R3)
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (hΘ : ContDiff ℝ ∞ Θ) (hF : ContDiff ℝ ∞ F)
    (y X z : R3) (r : ℝ) (hInv : (F y).IsInvertible) :
    fderiv ℝ (fun p : R3 × R3 => Θ (p.1,r • F p.1 p.2))
      (y,z) (X,framedParallelAngularVelocity F Γ y X z) =
    fderiv ℝ Θ (y,r • F y z) (X,-r • Γ y X (F y z)) := by
  have hFp : HasFDerivAt (fun p : R3 × R3 => F p.1)
      ((fderiv ℝ F y).comp (ContinuousLinearMap.fst ℝ R3 R3)) (y,z) :=
    (hF.differentiable (by simp) y).hasFDerivAt.comp (y,z)
      (hasFDerivAt_fst (𝕜 := ℝ) (p := (y,z)))
  let T : (R3 × R3) →L[ℝ] R3 :=
    (F y).comp (ContinuousLinearMap.snd ℝ R3 R3) +
      ((fderiv ℝ F y).comp (ContinuousLinearMap.fst ℝ R3 R3)).flip z
  have hV : HasFDerivAt (fun p : R3 × R3 => F p.1 p.2) T (y,z) :=
    hFp.clm_apply (hasFDerivAt_snd (𝕜 := ℝ) (p := (y,z)))
  let S : (R3 × R3) →L[ℝ] (R3 × R3) :=
    (ContinuousLinearMap.fst ℝ R3 R3).prod (r • T)
  have hP : HasFDerivAt (fun p : R3 × R3 => (p.1,r • F p.1 p.2)) S (y,z) :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (y,z))).prodMk (hV.const_smul r)
  have hc : HasFDerivAt (fun p : R3 × R3 => Θ (p.1,r • F p.1 p.2))
      ((fderiv ℝ Θ (y,r • F y z)).comp S) (y,z) :=
    (hΘ.differentiable (by simp) (y,r • F y z)).hasFDerivAt.comp (y,z) hP
  rw [hc.fderiv]
  change fderiv ℝ Θ (y,r • F y z)
    (X,r • (F y (framedParallelAngularVelocity F Γ y X z) + fderiv ℝ F y X z)) = _
  rw [frame_apply_parallelAngularVelocity F Γ y X z hInv]
  have halg : -(fderiv ℝ F y X z + Γ y X (F y z)) + fderiv ℝ F y X z =
      -Γ y X (F y z) := by abel
  rw [halg]
  simp only [smul_neg,neg_smul]

/-- No alternate endpoint is selected: the manuscript's actual horizontal
physical velocity is exactly the same phase derivative used by the jet proof. -/
theorem referenceFramedPhysicalEndpoint_center_horizontal
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1))
    (q : ℝ) (y z : R3) (r : ℝ) (i : Fin 3) :
    let F : R3 → R3 →L[ℝ] R3 := fun x => conformalReferenceGramFrameOperatorJoint g L (q,x)
    let Γ := coordinateConnectionField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
      (metricOperatorField (conformalReferenceMatrix g L q))
    fderiv ℝ (fun p : R3 × R3 =>
      referenceFramedPhysicalEndpoint g L Φ (q,((p.1,r),p.2))) (y,z)
        (F y (coordinateVector i),framedParallelAngularVelocity F Γ y (F y (coordinateVector i)) z) =
      referenceFramedCenterHorizontalVelocity g L Φ i (q,((y,r),z)) := by
  dsimp only
  let F : R3 → R3 →L[ℝ] R3 := fun x => conformalReferenceGramFrameOperatorJoint g L (q,x)
  let Γ := coordinateConnectionField
    (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
    (metricOperatorField (conformalReferenceMatrix g L q))
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_conformalReferenceGramFrameOperatorJoint g hg L).comp
      (contDiff_const.prodMk contDiff_id)
  exact fderiv_framedEndpoint_parallel_horizontal (fun p => (Φ q p 1).1) F Γ
    (hΘ.comp (contDiff_const.prodMk contDiff_id)) hF y (F y (coordinateVector i)) z r
      (referenceGramFrame_isInvertible g hg L (q,y))

end OAI.AnisotropicCalderon.ConnectionError
