import Calderon.MixedKernelConstruction.MixedKernelNativeAngularSkew
import Calderon.MixedKernelConstruction.MixedKernelPacketEndpointBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator NormalCoordinatesFrame
open scoped ContDiff InnerProductSpace Topology

section SpatialDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The literal spatial restriction of a full joint derivative. -/
def jointSpatialDerivative (F : ℝ × R3 → E) (p : ℝ × R3) : R3 →L[ℝ] E :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ R3)

theorem jointSpatialDerivative_eq_fderiv_slice (F : ℝ × R3 → E)
    (hF : ContDiff ℝ ∞ F) (lam : ℝ) (y : R3) :
    jointSpatialDerivative F (lam,y) = fderiv ℝ (fun Y => F (lam,Y)) y := by
  have h := (hF.differentiable (by simp) (lam,y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right lam y)
  exact h.fderiv.symm

theorem contDiff_jointSpatialDerivative (F : ℝ × R3 → E)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (jointSpatialDerivative F) :=
  (hF.fderiv_right (by simp)).clm_comp contDiff_const

end SpatialDerivative

/-- The actual slice Koszul connection, expressed by its genuine jointly smooth inputs. -/
def nativeReferenceConnectionJoint (g : MatrixField) (L : ℝ) (p : ℝ × R3) :
    R3 →L[ℝ] R3 →L[ℝ] R3 :=
  coordinateConnectionLinearMap (Ring.inverse (conformalReferenceOperatorJoint g L p))
    (jointSpatialDerivative (conformalReferenceOperatorJoint g L) p)

theorem nativeReferenceConnectionJoint_eq_actual (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (y : R3) :
    nativeReferenceConnectionJoint g L (lam,y) = coordinateConnectionField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L lam)))
      (metricOperatorField (conformalReferenceMatrix g L lam)) y := by
  unfold nativeReferenceConnectionJoint coordinateConnectionField
  rw [jointSpatialDerivative_eq_fderiv_slice _ (contDiff_conformalReferenceOperatorJoint g hg L)]
  rfl

/-- A direct genuine operator-norm bound for the actual parallel angular operator. -/
theorem norm_framedParallelAngularOperator_le
    (F : R3 → R3 →L[ℝ] R3) (Gamma : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (y X : R3) :
    ‖framedParallelAngularOperator F Gamma y X‖ ≤
      ‖ContinuousLinearMap.inverse (F y)‖*(‖fderiv ℝ F y‖+‖Gamma y‖*‖F y‖)*‖X‖ := by
  unfold framedParallelAngularOperator
  rw [norm_neg]
  have h1 := norm_add_le (fderiv ℝ F y X) ((Gamma y X).comp (F y))
  have h2 := ContinuousLinearMap.opNorm_comp_le (Gamma y X) (F y)
  have h3 := (fderiv ℝ F y).le_opNorm X
  have h4 := (Gamma y).le_opNorm X
  have hInner : ‖fderiv ℝ F y X+(Gamma y X).comp (F y)‖ ≤
      (‖fderiv ℝ F y‖+‖Gamma y‖*‖F y‖)*‖X‖ := by
    have hh := mul_le_mul_of_nonneg_right h4 (norm_nonneg (F y))
    nlinarith only [h1,h2,h3,hh]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    have hh := mul_le_mul_of_nonneg_left hInner (norm_nonneg (ContinuousLinearMap.inverse (F y)))
    nlinarith only [hh])

/-- Actual frame, reference connection and angular operators have one compact bound, before all packet parameters. -/
theorem exists_packet_reference_frame_connection_angular_bounds
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ y : R3, ‖y-P.y0‖ ≤ 4*P.rho →
      let F : R3 → R3 →L[ℝ] R3 := fun Y => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,Y)
      let Gamma := coordinateConnectionField
        (inverseMetricField (metricOperatorField (conformalReferenceMatrix S.g1 L lam)))
        (metricOperatorField (conformalReferenceMatrix S.g1 L lam))
      ‖F y‖ ≤ K ∧ ‖Gamma y‖ ≤ K ∧ ∀ i : Fin 3,
        ‖framedParallelAngularOperator F Gamma y (F y (coordinateVector i))‖ ≤ K := by
  classical
  let A : Set (ℝ × R3) := Icc (0 : ℝ) 1 ×ˢ closedBall P.y0 (4*P.rho)
  have hA : IsCompact A := isCompact_Icc.prod (isCompact_closedBall _ _)
  let FJ := conformalReferenceGramFrameOperatorJoint S.g1 L
  let QF := referenceGramFrameInverse S.g1 L
  let DF := jointSpatialDerivative FJ
  let QM : ℝ × R3 → R3 →L[ℝ] R3 := fun a => Ring.inverse (conformalReferenceOperatorJoint S.g1 L a)
  let DM := jointSpatialDerivative (conformalReferenceOperatorJoint S.g1 L)
  have hFJ := contDiff_conformalReferenceGramFrameOperatorJoint S.g1 S.g1_admissible L
  obtain ⟨cF,hF⟩ := hA.exists_bound_of_continuousOn (f := FJ) hFJ.continuous.continuousOn
  obtain ⟨cQ,hQ⟩ := hA.exists_bound_of_continuousOn (f := QF)
    (contDiff_referenceGramFrameInverse S.g1 S.g1_admissible L).continuous.continuousOn
  obtain ⟨cD,hD⟩ := hA.exists_bound_of_continuousOn (f := DF)
    (contDiff_jointSpatialDerivative FJ hFJ).continuous.continuousOn
  obtain ⟨cM,hM⟩ := hA.exists_bound_of_continuousOn (f := QM)
    (contDiff_conformalReferenceInverseJoint S.g1 S.g1_admissible L).continuous.continuousOn
  obtain ⟨cE,hE⟩ := hA.exists_bound_of_continuousOn (f := DM)
    (contDiff_jointSpatialDerivative _ (contDiff_conformalReferenceOperatorJoint S.g1 S.g1_admissible L)).continuous.continuousOn
  let B : ℝ := |cF|+|cQ|+|cD|+|cM|+|cE|+1
  have hB : 1 ≤ B := by dsimp [B];linarith [abs_nonneg cF,abs_nonneg cQ,abs_nonneg cD,abs_nonneg cM,abs_nonneg cE]
  have hB0 : 0 ≤ B := by linarith
  have hCF : cF ≤ B := by dsimp [B];linarith [le_abs_self cF,abs_nonneg cQ,abs_nonneg cD,abs_nonneg cM,abs_nonneg cE]
  have hCQ : cQ ≤ B := by dsimp [B];linarith [le_abs_self cQ,abs_nonneg cF,abs_nonneg cD,abs_nonneg cM,abs_nonneg cE]
  have hCD : cD ≤ B := by dsimp [B];linarith [le_abs_self cD,abs_nonneg cF,abs_nonneg cQ,abs_nonneg cM,abs_nonneg cE]
  have hCM : cM ≤ B := by dsimp [B];linarith [le_abs_self cM,abs_nonneg cF,abs_nonneg cQ,abs_nonneg cD,abs_nonneg cE]
  have hCE : cE ≤ B := by dsimp [B];linarith [le_abs_self cE,abs_nonneg cF,abs_nonneg cQ,abs_nonneg cD,abs_nonneg cM]
  let K : ℝ := B+2*B^2+B^3+2*B^5+1
  have hBK : B ≤ K := by dsimp [K];linarith [sq_nonneg B,pow_nonneg hB0 3,pow_nonneg hB0 5]
  have hGK : 2*B^2 ≤ K := by dsimp [K];linarith [pow_nonneg hB0 3,pow_nonneg hB0 5]
  have hOK : B^3+2*B^5 ≤ K := by dsimp [K];linarith [sq_nonneg B]
  refine ⟨K,hB.trans hBK,?_⟩
  intro lam hlam y hy F Gamma
  have ha : (lam,y) ∈ A := ⟨hlam,by simpa only [mem_closedBall,dist_eq_norm] using hy⟩
  have hFb : ‖F y‖ ≤ B := (hF (lam,y) ha).trans hCF
  have hQb : ‖ContinuousLinearMap.inverse (F y)‖ ≤ B := (hQ (lam,y) ha).trans hCQ
  have hDb : ‖fderiv ℝ F y‖ ≤ B := by
    have hh := (hD (lam,y) ha).trans hCD
    dsimp only [DF] at hh
    rw [jointSpatialDerivative_eq_fderiv_slice FJ hFJ lam y] at hh
    exact hh
  have hQMb : ‖QM (lam,y)‖ ≤ B := (hM (lam,y) ha).trans hCM
  have hDMb : ‖DM (lam,y)‖ ≤ B := (hE (lam,y) ha).trans hCE
  have hGb : ‖Gamma y‖ ≤ 2*B^2 := by
    dsimp only [Gamma]
    rw [← nativeReferenceConnectionJoint_eq_actual S.g1 S.g1_admissible L lam y]
    have hh := norm_coordinateConnectionLinearMap_le (QM (lam,y)) (DM (lam,y))
    have hprod := mul_le_mul hQMb hDMb (norm_nonneg _) hB0
    change ‖coordinateConnectionLinearMap (QM (lam,y)) (DM (lam,y))‖ ≤ 2*B^2
    nlinarith only [hh,hprod,sq_nonneg B]
  refine ⟨hFb.trans hBK,hGb.trans hGK,?_⟩
  intro i
  have hBasis : ‖coordinateVector i‖=1 := by simp [coordinateVector]
  have hX : ‖F y (coordinateVector i)‖ ≤ B := by
    have hh := (F y).le_opNorm (coordinateVector i)
    rw [hBasis,mul_one] at hh
    exact hh.trans hFb
  have hh := norm_framedParallelAngularOperator_le F Gamma y (F y (coordinateVector i))
  have hUpper : ‖ContinuousLinearMap.inverse (F y)‖*(‖fderiv ℝ F y‖+‖Gamma y‖*‖F y‖)*‖F y (coordinateVector i)‖ ≤
      B*(B+(2*B^2)*B)*B := by
    gcongr
  have hPoly : B*(B+(2*B^2)*B)*B=B^3+2*B^5 := by ring
  exact hh.trans (hUpper.trans (hPoly.le.trans hOK))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
