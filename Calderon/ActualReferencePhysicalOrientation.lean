import Calderon.ActualPhysicalMetricNormalization
import Calderon.WeightedMatrixCalculus
import Mathlib.Topology.Order.IntermediateValue

/-! The full original endpoint and coefficient data are retained. No orientation
premise or radius shrink is added. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.NormalCoordinatesFrame
open MetricOperator ConnectionError

private lemma operatorMatrixMap_entry (A : R3 →L[ℝ] R3) (i j : Fin 3) :
    operatorMatrixMap A i j = (A (coordinateVector j)) i := by
  have h := congrArg (fun v : R3 => v i) (operatorMatrixMap_apply A (coordinateVector j))
  change (matrixOperatorMap (operatorMatrixMap A) (coordinateVector j)) i = _ at h
  rw [MetricVolume.matrixOperator_coordinate] at h
  simpa only [coordinateVector,PiLp.single_apply,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true] using h

/-- The standard ordered Gram construction preserves orientation. -/
theorem det_operatorMatrixMap_frameOperator_metricGramFrame_pos
    (M : R3 →L[ℝ] R3)
    (hp : ∀ v : R3, v ≠ 0 → 0 < metricPair M v v) :
    0 < (operatorMatrixMap (frameOperator (metricGramFrame M))).det := by
  have h0 := hp _ coordinateVector_zero_ne
  have h1 := hp _ (gramSecond_ne_zero M)
  have h2 := hp _ (gramThird_ne_zero M)
  have hEntry (i j : Fin 3) :
      operatorMatrixMap (frameOperator (metricGramFrame M)) i j = metricGramFrame M j i := by
    rw [operatorMatrixMap_entry,frameOperator_coordinateVector]
  have hDet : (operatorMatrixMap (frameOperator (metricGramFrame M))).det =
      (Real.sqrt (metricPair M (coordinateVector 0) (coordinateVector 0)))⁻¹ *
        (Real.sqrt (metricPair M (gramSecond M) (gramSecond M)))⁻¹ *
        (Real.sqrt (metricPair M (gramThird M) (gramThird M)))⁻¹ := by
    rw [Matrix.det_fin_three]
    simp only [hEntry]
    simp [metricGramFrame,metricNormalize,coordinateVector,PiLp.single_apply,
      gramSecond_one,gramSecond_two,gramThird_two]
  rw [hDet]
  exact mul_pos (mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr h0))
    (inv_pos.mpr (Real.sqrt_pos.mpr h1))) (inv_pos.mpr (Real.sqrt_pos.mpr h2))

end OAI.AnisotropicCalderon.NormalCoordinatesFrame
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator NormalCoordinatesFrame
  DirichletFamily.DriftBootstrap

private theorem pos_at_one_of_continuous_nonzero_unitInterval
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (h0 : 0 < f 0) (hne : ∀ s ∈ Icc (0 : ℝ) 1, f s ≠ 0) : 0 < f 1 := by
  by_contra h1
  have h1le : f 1 ≤ 0 := le_of_not_gt h1
  obtain ⟨s,hs,hs0⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hf
    (show (0 : ℝ) ∈ Icc (f 1) (f 0) from ⟨h1le,h0.le⟩)
  exact hne s hs hs0

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hg hData in
/-- Nonvanishing is obtained from the NORMALIZED positive congruence, including r=0. -/
theorem referenceFramedNormalizedJacobian_det_ne_zero_on_closedDoubleBall
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    (operatorMatrixMap (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)))).det ≠ 0 := by
  let A := operatorMatrixMap (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)))
  have hRoundtrip (M : Matrix (Fin 3) (Fin 3) ℝ) :
      operatorMatrixMap (matrixOperatorMap M) = M := by
    change matrixOperatorAlgEquiv.symm (matrixOperatorAlgEquiv M) = M
    exact matrixOperatorAlgEquiv.symm_apply_apply M
  have hMat : A.transpose * g (q • referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z))) * A =
      Real.exp (2*L*referenceRescaledDepth g L Φ (q,(y,r)) z) • H ((q,(y,r)),z) := by
    have hMetric := congrArg operatorMatrixMap
      (referenceFramedOriginalNormalizedMetric_eq g hg L y0 Φ B ε C ρ H a w hData
        q hq y hy r hr z hz)
    simpa only [referenceFramedOriginalNormalizedMetric,operatorMatrixMap_comp,
      operatorMatrixMap_adjoint,operatorMatrixMap_metricOperatorField,map_smul,hRoundtrip,
      Matrix.mul_assoc,A] using hMetric
  rcases hData.1 with ⟨_,_,_,_,_,_,_,hPos,_,_,_,_,_,_,_⟩
  have hRPos : (Real.exp (2*L*referenceRescaledDepth g L Φ (q,(y,r)) z) •
      H ((q,(y,r)),z)).PosDef := (hPos ((q,(y,r)),z)).smul (Real.exp_pos _)
  change A.det ≠ 0
  intro hZero
  have hDet := hRPos.det_pos
  rw [← hMat,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,hZero,mul_zero] at hDet
  exact (lt_irrefl (0 : ℝ)) hDet

include hg hData in
/-- The exact chosen normalized Jacobian has positive determinant throughout its original room. -/
theorem referenceFramedNormalizedJacobian_det_pos
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    0 < (operatorMatrixMap (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)))).det := by
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hJ := contDiff_referenceFramedNormalizedJacobian g hg L Φ hTheta
  have hNormal := hData.1.1
  have hFour : 4*ρ ≤ ε := hData.1.2.2.1
  rcases hNormal with ⟨hEndpoint,hε,_,_,_,_,hRoom,_⟩
  have hyB : (y,(0 : R3)) ∈ B := by
    simpa only [zero_smul] using
      (hRoom q hq y (hy.trans hFour) 0 (by simpa using hε.le) 0 (by simp)).1
  rcases hEndpoint with ⟨_,_,_,_,_,_,_,_,_,hFirst,_⟩
  have hZero : referenceFramedNormalizedJacobian g L Φ (q,((y,0),z)) =
      conformalReferenceGramFrameOperatorJoint g L (q,y) :=
    referenceFramedNormalizedJacobian_zero g L Φ q y z (hFirst q hq y hyB)
  let A : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun s =>
    operatorMatrixMap (referenceFramedNormalizedJacobian g L Φ (q,((y,s*r),z)))
  let T : ℝ → ReferenceEndpointVariables := fun s => (q,((y,s*r),z))
  have hT : ContDiff ℝ ∞ T :=
    contDiff_const.prodMk ((contDiff_const.prodMk
      (contDiff_id.mul contDiff_const)).prodMk contDiff_const)
  have hA : ContDiff ℝ ∞ A := operatorMatrixMap.contDiff.comp (hJ.comp hT)
  have h0 : 0 < (A 0).det := by
    change 0 < (operatorMatrixMap
      (referenceFramedNormalizedJacobian g L Φ (q,((y,0*r),z)))).det
    rw [zero_mul,hZero]
    exact det_operatorMatrixMap_frameOperator_metricGramFrame_pos _
      (conformalReferenceOperatorJoint_pos g hg L (q,y))
  have hne (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : (A s).det ≠ 0 := by
    apply referenceFramedNormalizedJacobian_det_ne_zero_on_closedDoubleBall
      g hg L y0 Φ B ε C ρ H a w hData q hq y hy (s*r) _ z hz
    calc
      |s*r| = s*|r| := by rw [abs_mul,abs_of_nonneg hs.1]
      _ ≤ 1*|r| := mul_le_mul_of_nonneg_right hs.2 (abs_nonneg r)
      _ ≤ 4*ρ := by simpa only [one_mul] using hr
  have h1 := pos_at_one_of_continuous_nonzero_unitInterval (fun s => (A s).det)
    (contDiff_matrixFamily_det A hA).continuous.continuousOn h0 hne
  simpa only [A,one_mul] using h1

include hg hData in
/-- Positive physical radius gives positive orientation for the SAME native physical endpoint. -/
theorem coordinateJacobianMatrix_referencePhysicalEndpoint_det_pos
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hrpos : 0 < r)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    0 < (coordinateJacobianMatrix
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))) z).det := by
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hDX : HasFDerivAt
      (fun x : R3 => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x)))
      (r • referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))) z :=
    hasFDerivAt_framedScaledEndpoint_slice (fun x => (Φ q x 1).1)
      (fun x => conformalReferenceGramFrameOperatorJoint g L (q,x))
      (hTheta.comp (contDiff_const.prodMk contDiff_id)) y z r
  rw [coordinateJacobianMatrix_eq_operatorMatrixMap,hDX.fderiv,map_smul,
    Matrix.det_smul,Fintype.card_fin]
  exact mul_pos (pow_pos hrpos 3)
    (referenceFramedNormalizedJacobian_det_pos g hg L y0 Φ B ε C ρ H a w hData
      q hq y hy r hr z hz)

end OAI.AnisotropicCalderon.ConnectionError
