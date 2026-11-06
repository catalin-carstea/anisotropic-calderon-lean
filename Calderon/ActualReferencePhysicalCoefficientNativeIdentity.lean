import Calderon.ActualPhysicalMetricNormalization
import Calderon.ActualRescaledConformalGauge
import Calderon.PositiveConformalMetric
import Calderon.WeightedCommonSupportCoefficients

/-! UNCOMPILED /tmp draft. See the preceding UPFRONT file.
No axiom or admission is supplied. The final actual orientation theorem is
still an explicitly unproved obligation described in that file. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator DirichletFamily.DriftBootstrap

lemma referenceRescaledDepth_eq_physicalEndpoint_depth
    (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (p : ℝ × (R3 × ℝ)) (z : R3) :
    referenceRescaledDepth g L Φ p z = conformalReferenceCoordinateDepth
      (referenceFramedPhysicalEndpoint g L Φ (p.1,(p.2,z))) := rfl

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData in
lemma nativePrincipal_eq_matrixPrincipal_on_doubleBall
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    a ((q,(y,r)),z) = matrixPrincipalCoefficient H ((q,(y,r)),z) := by
  rcases hData.1 with ⟨_,_,_,_,_,_,_,_,_,_,_,hLocal,_,_,_⟩
  have hl := hLocal q hq y hy r hr z hz
  simpa only [matrixPrincipalCoefficient,matrixVolumeDensity,hl.1] using hl.2.1

include hg hData in
lemma principalCoefficient_referencePhysicalPullback_eq_abs_radius_smul_native
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hr0 : r ≠ 0)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    principalCoefficient (pullbackMetric (fun x => g (q • x))
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x)))) z =
      |r| • (Real.exp (L*referenceRescaledDepth g L Φ (q,(y,r)) z) • a ((q,(y,r)),z)) := by
  let Hp : MatrixField := fun x => H ((q,(y,r)),x)
  let f : R3 → ℝ := fun x => Real.log |r| + L*referenceRescaledDepth g L Φ (q,(y,r)) x
  have hMetric := pullbackMetric_referenceOriginal_eq_conformal g hg L y0 Φ B ε C ρ H a w hData
    q hq y hy r hr hr0 z hz
  have hCoeff : principalCoefficient (pullbackMetric (fun x => g (q • x))
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x)))) z =
      principalCoefficient (conformalMatrix Hp f) z :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => Real.sqrt M.det • M⁻¹) hMetric
  have hA := nativePrincipal_eq_matrixPrincipal_on_doubleBall g L y0 Φ B ε C ρ H a w hData
    q hq y hy r hr z hz
  rcases hData.1 with ⟨_,_,_,_,_,_,_,hPos,_,_,_,_,_,_,_⟩
  rw [hCoeff,principalCoefficient_conformalMatrix Hp f (fun x => hPos ((q,(y,r)),x)) z]
  dsimp only [f]
  rw [Real.exp_add,Real.exp_log (abs_pos.mpr hr0),mul_smul]
  change |r| • (Real.exp (L*referenceRescaledDepth g L Φ (q,(y,r)) z) •
    matrixPrincipalCoefficient H ((q,(y,r)),z)) = _
  rw [← hA]

include hg hData in
lemma principalCoefficient_referencePhysicalPullback_eq_pos_radius_smul_native
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hrpos : 0 < r)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    principalCoefficient (pullbackMetric (fun x => g (q • x))
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x)))) z =
      r • (Real.exp (L*referenceRescaledDepth g L Φ (q,(y,r)) z) • a ((q,(y,r)),z)) := by
  simpa only [abs_of_pos hrpos] using
    principalCoefficient_referencePhysicalPullback_eq_abs_radius_smul_native
      g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hrpos.ne' z hz

include hg hData in
lemma contDiff_referencePhysicalGaugePrincipalCoefficient :
    ContDiff ℝ ∞ (fun v : (ℝ × (R3 × ℝ)) × R3 =>
      Real.exp (L*referenceRescaledDepth g L Φ v.1 v.2) • matrixPrincipalCoefficient H v) := by
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ (fun v : (ℝ × (R3 × ℝ)) × R3 =>
      referenceFramedPhysicalEndpoint g L Φ (v.1.1,(v.1.2,v.2))) :=
    (contDiff_referenceFramedPhysicalEndpoint g hg L Φ hTheta).comp
      (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  have ht : ContDiff ℝ ∞ (fun v : (ℝ × (R3 × ℝ)) × R3 =>
      referenceRescaledDepth g L Φ v.1 v.2) := by
    change ContDiff ℝ ∞ (conformalReferenceCoordinateDepth ∘
      (fun v : (ℝ × (R3 × ℝ)) × R3 =>
        referenceFramedPhysicalEndpoint g L Φ (v.1.1,(v.1.2,v.2))))
    exact contDiff_conformalReferenceCoordinateDepth.comp hX
  rcases hData.1 with ⟨_,_,_,_,_,_,hH,hPos,_,_,_,_,_,_,_⟩
  exact (contDiff_const.mul ht).exp.smul (contDiff_matrixPrincipalCoefficient H hH hPos)

include hData in
lemma referencePhysicalGaugePrincipalCoefficient_posDef
    (p : ℝ × (R3 × ℝ)) (z : R3) :
    (Real.exp (L*referenceRescaledDepth g L Φ p z) • matrixPrincipalCoefficient H (p,z)).PosDef := by
  rcases hData.1 with ⟨_,_,_,_,_,_,_,hPos,_,_,_,_,_,_,_⟩
  exact (matrixPrincipalCoefficient_posDef H hPos (p,z)).smul (Real.exp_pos _)

include hg hData in
lemma coordinateJacobianMatrix_referencePhysicalEndpoint_eq_radius_smul_normalized
    (q : ℝ) (y : R3) (r : ℝ) (z : R3) :
    coordinateJacobianMatrix
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))) z =
      r • operatorMatrixMap (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))) := by
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hDX := hasFDerivAt_framedScaledEndpoint_slice (fun x => (Φ q x 1).1)
    (fun x => conformalReferenceGramFrameOperatorJoint g L (q,x))
    (hTheta.comp (contDiff_const.prodMk contDiff_id)) y z r
  have hd : fderiv ℝ (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))) z =
      r • referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)) := by
    exact hDX.fderiv
  rw [coordinateJacobianMatrix_eq_operatorMatrixMap,hd,map_smul]

include hg hData in
lemma det_coordinateJacobianMatrix_referencePhysicalEndpoint
    (q : ℝ) (y : R3) (r : ℝ) (z : R3) :
    (coordinateJacobianMatrix
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))) z).det =
      r^3 * (operatorMatrixMap (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)))).det := by
  rw [coordinateJacobianMatrix_referencePhysicalEndpoint_eq_radius_smul_normalized
    g hg L y0 Φ B ε C ρ H a w hData q y r z,Matrix.det_smul,Fintype.card_fin]

lemma metricDivergenceFlux_pullbackMetric_eq_signedPiolaFlux_of_det_pos
    (g : MatrixField) (X : R3 → R3) (u : R3 → ℝ)
    (hX : ContDiff ℝ ∞ X) (hu : ContDiff ℝ ∞ u) (x : R3)
    (hdet : 0 < (coordinateJacobianMatrix X x).det) :
    metricDivergenceFlux (pullbackMetric g X) (u ∘ X) x =
      signedPiolaFlux X (metricDivergenceFlux g u) x := by
  let A := coordinateJacobianMatrix X x
  have hUnit : IsUnit A.det := (isUnit_iff_ne_zero).mpr hdet.ne'
  have hAdj : A.adjugate = A.det • A⁻¹ := by
    rw [Matrix.inv_def,Ring.inverse_eq_inv',smul_smul,mul_inv_cancel₀ hUnit.ne_zero,one_smul]
  rw [metricDivergenceFlux_pullbackMetric g X u hX hu x hUnit]
  change |A.det| • matrixOperatorMap A⁻¹ (metricDivergenceFlux g u (X x)) =
    matrixOperatorMap A.adjugate (metricDivergenceFlux g u (X x))
  rw [hAdj,map_smul,ContinuousLinearMap.smul_apply,abs_of_pos hdet]

end OAI.AnisotropicCalderon.ConnectionError
