import Calderon.MixedKernelConstruction.MixedKernelNativeEnergyCovectors
import Calderon.MixedKernelConstruction.MixedKernelActualNormalizedOperatorDictionary
import Calderon.MetricFrameOperator
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator NormalCoordinatesFrame
open NormalizedPrincipalMetric
open scoped ContDiff Topology InnerProductSpace

/-- The SAME actual Gram frame pulls the original reference metric back to the identity. -/
theorem actual_reference_frame_pullback_metric
    (S : KnownSideSourceData) (L lam : ℝ) (y : R3) :
    let G := metricOperatorField (conformalReferenceMatrix S.g1 L lam) y
    let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
    F.adjoint.comp (G.comp F)=ContinuousLinearMap.id ℝ R3 := by
  intro G F
  change (frameOperator (metricGramFrame (conformalReferenceOperatorJoint S.g1 L (lam,y)))).adjoint.comp
    ((conformalReferenceOperatorJoint S.g1 L (lam,y)).comp
      (frameOperator (metricGramFrame (conformalReferenceOperatorJoint S.g1 L (lam,y)))))=_
  exact frameOperator_pullback_metric _ _ (NormalCoordinatesFrame.metricGramFrame_isMetricOrthonormalFrame _
    (conformalReferenceOperatorJoint_symmetric S.g1 S.g1_admissible L (lam,y))
    (conformalReferenceOperatorJoint_pos S.g1 S.g1_admissible L (lam,y)))

/-- Exact inverse identity, derived from a genuine frame and its genuine two-sided inverse. -/
theorem inverse_operator_eq_frame_comp_adjoint
    (G F Q : R3 →L[ℝ] R3) (hG : IsUnit G)
    (hFQ : ∀ U : R3, F (Q U)=U) (hQF : ∀ U : R3, Q (F U)=U)
    (hFrame : F.adjoint.comp (G.comp F)=ContinuousLinearMap.id ℝ R3) :
    Ring.inverse G=F.comp F.adjoint := by
  have hGdict : G=Q.adjoint.comp Q := by
    apply ContinuousLinearMap.ext
    intro U
    apply ext_inner_right ℝ
    intro V
    have hh := congrArg (fun A : R3 →L[ℝ] R3 => ⟪A (Q U),Q V⟫_ℝ) hFrame
    change ⟪F.adjoint (G (F (Q U))),Q V⟫_ℝ=⟪Q U,Q V⟫_ℝ at hh
    rw [ContinuousLinearMap.adjoint_inner_left,hFQ,hFQ] at hh
    change ⟪G U,V⟫_ℝ=⟪Q.adjoint (Q U),V⟫_ℝ
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact hh
  have hFQmap : F.comp Q=ContinuousLinearMap.id ℝ R3 := ContinuousLinearMap.ext hFQ
  have hAdj (U : R3) : Q.adjoint (F.adjoint U)=U := by
    have hh := congrArg (fun A : R3 →L[ℝ] R3 => A.adjoint U) hFQmap
    simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply] using hh
  have hRight (U : R3) : G (F (F.adjoint U))=U := by
    rw [hGdict]
    change Q.adjoint (Q (F (F.adjoint U)))=U
    rw [hQF,hAdj]
  apply ContinuousLinearMap.ext
  intro U
  have hLeft (W : R3) : Ring.inverse G (G W)=W := by
    have hh := congrArg (fun A : R3 →L[ℝ] R3 => A W) (Ring.inverse_mul_cancel G hG)
    simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] using hh
  calc
    Ring.inverse G U=Ring.inverse G (G (F (F.adjoint U))) := by rw [hRight]
    _ = F (F.adjoint U) := hLeft _

/-- The original reference inverse is the actual frame times its actual adjoint. -/
theorem actual_reference_inverse_eq_frame_comp_adjoint
    (S : KnownSideSourceData) (L lam : ℝ) (y : R3) :
    let G := metricOperatorField (conformalReferenceMatrix S.g1 L lam) y
    let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
    Ring.inverse G=F.comp F.adjoint := by
  intro G F
  let Q := referenceGramFrameInverse S.g1 L (lam,y)
  have hInv := referenceGramFrame_isInvertible S.g1 S.g1_admissible L (lam,y)
  have hFQ (U : R3) : F (Q U)=U := hInv.self_apply_inverse U
  have hQF (U : R3) : Q (F U)=U := hInv.inverse_apply_self U
  exact inverse_operator_eq_frame_comp_adjoint G F Q
    (isUnit_of_strictly_positive _ (conformalReferenceOperatorJoint_pos S.g1 S.g1_admissible L (lam,y)))
    hFQ hQF (actual_reference_frame_pullback_metric S L lam y)

/-- Genuine inverses remain genuine after the actual contravariant/covariant frame changes. -/
theorem frame_principal_covariant_inverse
    (A F Q : R3 →L[ℝ] R3) (hA : IsUnit A)
    (hFQ : ∀ U : R3, F (Q U)=U) (hQF : ∀ U : R3, Q (F U)=U) :
    let T := Q.comp (A.comp Q.adjoint)
    let R := F.adjoint.comp ((Ring.inverse A).comp F)
    T.comp R=ContinuousLinearMap.id ℝ R3 ∧ R.comp T=ContinuousLinearMap.id ℝ R3 := by
  intro T R
  have hAdj1 (U : R3) : Q.adjoint (F.adjoint U)=U := by
    have hh := congrArg (fun B : R3 →L[ℝ] R3 => B.adjoint U)
      (show F.comp Q=ContinuousLinearMap.id ℝ R3 from ContinuousLinearMap.ext hFQ)
    simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply] using hh
  have hAdj2 (U : R3) : F.adjoint (Q.adjoint U)=U := by
    have hh := congrArg (fun B : R3 →L[ℝ] R3 => B.adjoint U)
      (show Q.comp F=ContinuousLinearMap.id ℝ R3 from ContinuousLinearMap.ext hQF)
    simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply] using hh
  have hAM (U : R3) : A (Ring.inverse A U)=U := by
    have hh := congrArg (fun B : R3 →L[ℝ] R3 => B U) (Ring.mul_inverse_cancel A hA)
    simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] using hh
  have hMA (U : R3) : Ring.inverse A (A U)=U := by
    have hh := congrArg (fun B : R3 →L[ℝ] R3 => B U) (Ring.inverse_mul_cancel A hA)
    simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] using hh
  constructor
  · apply ContinuousLinearMap.ext
    intro U
    change Q (A (Q.adjoint (F.adjoint (Ring.inverse A (F U)))))=U
    rw [hAdj1,hAM,hQF]
  · apply ContinuousLinearMap.ext
    intro U
    change F.adjoint (Ring.inverse A (F (Q (A (Q.adjoint U)))))=U
    rw [hFQ,hMA,hAdj2]

/-- The frame error is EXACTLY the same principal tensor difference, before estimating it. -/
theorem frame_principal_sub_identity
    (A G F Q : R3 →L[ℝ] R3)
    (hGinv : Ring.inverse G=F.comp F.adjoint)
    (hFQ : ∀ U : R3, F (Q U)=U) (hQF : ∀ U : R3, Q (F U)=U) :
    Q.comp (A.comp Q.adjoint)-ContinuousLinearMap.id ℝ R3=
      Q.comp ((A-Ring.inverse G).comp Q.adjoint) := by
  have hAdj (U : R3) : F.adjoint (Q.adjoint U)=U := by
    have hh := congrArg (fun B : R3 →L[ℝ] R3 => B.adjoint U)
      (show Q.comp F=ContinuousLinearMap.id ℝ R3 from ContinuousLinearMap.ext hQF)
    simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply] using hh
  apply ContinuousLinearMap.ext
  intro U
  change Q (A (Q.adjoint U))-U=Q ((A-Ring.inverse G) (Q.adjoint U))
  rw [ContinuousLinearMap.sub_apply,map_sub,hGinv,ContinuousLinearMap.comp_apply,hQF,hAdj]

/-- Exact actual inverse pairs and original-H8 error, with constants before all small parameters. -/
theorem exists_actual_framed_principal_error_bound
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ (delta Rstar eps : ℝ) (p : ℕ), CurrentRadiusBootstrap S L lam delta Rstar eps p →
      ∀ y∈P.centers, y∈cylinder →
      let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
      let Q := referenceGramFrameInverse S.g1 L (lam,y)
      let A := metricOperatorField (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam) y
      let M := metricOperatorField (fun Y => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam Y)⁻¹) y
      let T := Q.comp (A.comp Q.adjoint)
      let R := F.adjoint.comp (M.comp F)
      T.comp R=ContinuousLinearMap.id ℝ R3 ∧ R.comp T=ContinuousLinearMap.id ℝ R3 ∧
        ‖T-ContinuousLinearMap.id ℝ R3‖ ≤ C*(eps*referenceRadius delta Rstar p L y) := by
  obtain ⟨B,hB,HB⟩ := exists_packet_frame_right_inverse_bound S L P
  obtain ⟨CH,hCH,HCH⟩ := exists_current_normalized_principal_operator_jet_bound
  refine ⟨B^2*CH,by positivity,?_⟩
  intro lam hlam delta Rstar eps p hBoot y hy hyC F Q A M T R
  have hyRoom : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy).1.le
  obtain ⟨hQ,hFQ⟩ := HB lam hlam y hyRoom
  have hInv := referenceGramFrame_isInvertible S.g1 S.g1_admissible L (lam,y)
  have hQF (U : R3) : Q (F U)=U := hInv.inverse_apply_self U
  have hM : M=Ring.inverse A := actual_covariant_second_operator_eq_ringInverse S L lam y
  have hPair := frame_principal_covariant_inverse A F Q (isUnit_normalized_principal_operator S L lam y) hFQ hQF
  change T.comp R=ContinuousLinearMap.id ℝ R3 ∧ R.comp T=ContinuousLinearMap.id ℝ R3 ∧ _
  have hPair' : T.comp R=ContinuousLinearMap.id ℝ R3 ∧ R.comp T=ContinuousLinearMap.id ℝ R3 := by
    simpa only [T,R,hM] using hPair
  refine ⟨hPair'.1,hPair'.2,?_⟩
  let G := metricOperatorField (conformalReferenceMatrix S.g1 L lam) y
  have hDiff : ‖A-Ring.inverse G‖ ≤ CH*(eps*referenceRadius delta Rstar p L y) := by
    rw [normalized_principal_operator_difference_eq S L lam y]
    exact (HCH S L lam delta Rstar eps p hBoot y hyC).1
  have hErr0 : 0 ≤ CH*(eps*referenceRadius delta Rstar p L y) := (norm_nonneg _).trans hDiff
  have hAdj : ‖Q.adjoint‖=‖Q‖ := ContinuousLinearMap.adjoint.norm_map Q
  change ‖Q.comp (A.comp Q.adjoint)-ContinuousLinearMap.id ℝ R3‖ ≤ _
  rw [frame_principal_sub_identity A G F Q (actual_reference_inverse_eq_frame_comp_adjoint S L lam y) hFQ hQF]
  calc
    ‖Q.comp ((A-Ring.inverse G).comp Q.adjoint)‖ ≤ ‖Q‖*‖(A-Ring.inverse G).comp Q.adjoint‖ :=
      Q.opNorm_comp_le _
    _ ≤ ‖Q‖*(‖A-Ring.inverse G‖*‖Q.adjoint‖) :=
      mul_le_mul_of_nonneg_left ((A-Ring.inverse G).opNorm_comp_le _) (norm_nonneg Q)
    _ ≤ B*((CH*(eps*referenceRadius delta Rstar p L y))*B) := by rw [hAdj];gcongr
    _ = (B^2*CH)*(eps*referenceRadius delta Rstar p L y) := by ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
