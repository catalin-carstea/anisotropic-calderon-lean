import MixedKernelNativePacketSmallness
import MixedKernelNativeFramedEnergyAbsorption
import MixedKernelNativeNormalizedFrameCriterion
import MixedKernelNativeEnergyReferenceLower
import MixedKernelNativeActualEnergyConnection
import MixedKernelNativeNormalMetricDictionary
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator NormalCoordinatesFrame
open ActualScalarPrincipalAdjoint ReferenceWeightedApproximation
open NormalizedPrincipalMetric
open scoped ContDiff Topology InnerProductSpace

/-- The actual packet energy meets the literal two-metric criterion with degree before epsilon and a delta-independent radius cap. -/
theorem exists_packet_actual_energy_strictness_parameters
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (c0 c : ℝ) (hc0 : 0<c0) (hc : 0<c) :
    ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p → ∃ eps0 rCap : ℝ,
      0<eps0 ∧ eps0 ≤ 1 ∧ 0<rCap ∧
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 → ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ delta Rstar : ℝ, 0<delta → delta ≤ 1 → 0<Rstar →
      CurrentRadiusBootstrap S L lam delta Rstar eps p → ∀ y ∈ cylinder∩P.centers,
      let rad := referenceRadius delta Rstar p L
      let beta := actualReferenceBeta S.g1 L lam delta Rstar p y
      rad y ≤ rCap → c0*(p : ℝ) ≤ beta →
      (∀ X : R3, RadiusProfile.coordinateHessian (fun Y => Real.log (rad Y))
        (fun U V => coordinateConnectionField
          (inverseMetricField (metricOperatorField (conformalReferenceMatrix S.g1 L lam)))
          (metricOperatorField (conformalReferenceMatrix S.g1 L lam)) y U V) y X X ≤ 
        -c*beta*⟪metricOperatorField (conformalReferenceMatrix S.g1 L lam) y X,X⟫_ℝ) →
      ∀ z : R3, ‖z‖=1 →
      let x := packetEndpoint S L P lam y (rad y) z
      ∀ rho : R3 × R3 → ℝ, ContDiffAt ℝ ∞ rho (x,y) →
      (∀ᶠ a : R3 × R3 in 𝓝 (y,z), rho (packetEndpoint S L P lam a.1 (rad y) a.2,a.1)=(⟪a.2,a.2⟫_ℝ-1)/2) →
      ProductHessianStrictAt (conformalReferenceMatrix S.g1 L lam)
        (fun Y => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam Y)⁻¹) x y
        (nativeEnergyPhase (rad y) rho rad) := by
  obtain ⟨D,hD,HD⟩ := exists_packet_actual_native_normal_inverse_error S L P
  obtain ⟨D2,hD2,HD2⟩ := exists_actual_framed_principal_error_bound S L P
  obtain ⟨D3,hD3,HD3⟩ := exists_packet_jacobi_synthesis_bound S L P
  obtain ⟨Cr,hCr,Hr⟩ := exists_packet_actual_energy_reference_lower_bound S L P
  obtain ⟨Cg,t,hCg,ht,Hg⟩ := exists_packet_actual_energy_connection_error S L P
  obtain ⟨pA,hpA,HA⟩ := exists_native_framed_energy_strictness_parameters c0 c (2*D) D2 D3 Cr Cg
    hc0 hc (by positivity) hD2.le hD3.le hCr.le hCg.le
  obtain ⟨N,rCap,hrCap,Hsmall⟩ := exists_native_packet_smallness_parameters c0 (D+1) D2 D3 P.rho t
    hc0 (by positivity) hD2 hD3 P.rho_positive ht
  refine ⟨max pA N,hpA.trans (Nat.le_max_left _ _),?_⟩
  intro p hp
  have hpA' : pA ≤ p := (Nat.le_max_left _ _).trans hp
  have hpN : N ≤ p := (Nat.le_max_right _ _).trans hp
  obtain ⟨epsA,hepsA,hepsA1,Hnum⟩ := HA p hpA'
  let eps0 := min epsA (1/8)
  have heps0 : 0<eps0 := lt_min hepsA (by norm_num)
  refine ⟨eps0,rCap,heps0,(min_le_left _ _).trans hepsA1,hrCap,?_⟩
  intro eps heps heps0' lam hlam delta Rstar hd hd1 hRs hBoot y hy rad beta hrBound hBeta hLog z hz x rho hRho hFamily
  let r := rad y
  have hr : 0<r := referenceRadius_pos delta Rstar p L y hd hRs
  have hepsA' : eps ≤ epsA := heps0'.trans (min_le_left _ _)
  have heps8 : eps ≤ 1/8 := heps0'.trans (min_le_right _ _)
  have heps1 : eps ≤ 1 := by linarith
  obtain ⟨hBeta1,hrMin,hSmall0,hEta1Plus,hEta2,hJacCap⟩ :=
    Hsmall p hpN eps heps heps1 beta r hBeta hr hrBound
  have hEta1 : (2*D)*r^2 ≤ 1/320 := by nlinarith only [hEta1Plus,sq_nonneg r]
  have hr1 : r ≤ 1 := hrMin.trans (min_le_left _ _)
  have hrRoom : r ≤ 4*P.rho := hrMin.trans (min_le_right _ _)
  have hRadiusBoot : r*beta^2 ≤ eps := hBoot.2 delta ⟨le_rfl,hd1⟩ y hy.1
  have hzRoom : z ∈ closedBall (0 : R3) 2 := by simp only [mem_closedBall,dist_zero_right,hz];norm_num
  have hyRoom : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy.2).1.le
  have hrAbs : |r| ≤ 4*P.rho := by rw [abs_of_pos hr];exact hrRoom
  let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z))
  let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
  let Q1 := ContinuousLinearMap.inverse J
  let Q2 := referenceGramFrameInverse S.g1 L (lam,y)
  let G := conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),z))
  let T1 := ContinuousLinearMap.inverse G
  let A := metricOperatorField (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam) y
  let M1 := metricOperatorField (conformalReferenceMatrix S.g1 L lam)
  let M2 := metricOperatorField (fun Y => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam Y)⁻¹)
  let T2 := Q2.comp (A.comp Q2.adjoint)
  let R2 := F.adjoint.comp ((M2 y).comp F)
  let Gamma1 := coordinateConnectionField (inverseMetricField M1) M1
  let Gamma2 := coordinateConnectionField (inverseMetricField M2) M2
  let V := frameOperator (fun i => referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i (lam,((y,r),z)))
  let b := profileFrameCovectorVector rad F y
  let e := r^2 • V.adjoint z
  let n := z+(b+e)
  let E := nativeEnergyPhase r rho rad
  have hInvJ := packet_normalizedJacobian_isInvertible S L P lam hlam y hy.2 r hrAbs z hzRoom
  have hInvF := referenceGramFrame_isInvertible S.g1 S.g1_admissible L (lam,y)
  have hInvG := (packet_nativeMetric_inverse_bound S L P lam hlam y hyRoom r hrAbs z hzRoom).1
  have hJQ (X : R3) : J (Q1 X)=X := hInvJ.self_apply_inverse X
  have hFQ (X : R3) : F (Q2 X)=X := hInvF.self_apply_inverse X
  have hGdict : G=J.adjoint.comp ((M1 x).comp J) := actual_native_normal_metric_eq_jacobian_pullback S L P lam y r z
  have hTR1 (X : R3) : T1 (J.adjoint (M1 x (J X)))=X := by
    have hh := congrArg (fun B : R3 →L[ℝ] R3 => B X) hGdict
    change G X=J.adjoint (M1 x (J X)) at hh
    rw [←hh]
    exact hInvG.inverse_apply_self X
  have hNear1 : ‖T1-ContinuousLinearMap.id ℝ R3‖ ≤ (2*D)*r^2 :=
    (HD lam hlam y hyRoom r hrAbs z hzRoom (by nlinarith only [hEta1])).2
  obtain ⟨hTR2map,_hRT2map,hNear2⟩ := HD2 lam hlam delta Rstar eps p hBoot y hy.2 hy.1
  have hNear2' : ‖T2-ContinuousLinearMap.id ℝ R3‖ ≤ D2*eps*r := by simpa only [mul_assoc] using hNear2
  have hTR2 (X : R3) : T2 (F.adjoint (M2 y (F X)))=X :=
    congrArg (fun B : R3 →L[ℝ] R3 => B X) hTR2map
  have hT2R2 (X : R3) : T2 (R2 X)=X := hTR2 X
  have hV : ‖V‖ ≤ D3 := HD3 lam hlam y hyRoom r hrAbs z hzRoom
  have hbNorm : ‖b‖=r*beta := norm_actual_radius_frame_covector_eq_radius_mul_beta S L lam delta Rstar p hd hRs y
  have hb8 : ‖b‖ ≤ 1/8 :=
    (norm_actual_radius_frame_covector_le_of_original_bootstrap S L lam delta Rstar p hd hRs y eps hBeta1 hRadiusBoot).trans heps8
  have heNorm : ‖e‖ ≤ D3*r^2 := by
    have hAdj : ‖V.adjoint‖=‖V‖ := ContinuousLinearMap.adjoint.norm_map V
    dsimp only [e]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
    have hh : ‖V.adjoint z‖ ≤ D3 := (V.adjoint.le_opNorm z).trans (by rw [hz,hAdj,mul_one];exact hV)
    nlinarith only [mul_le_mul_of_nonneg_left hh (sq_nonneg r)]
  have he8 : ‖e‖ ≤ 1/8 := heNorm.trans hJacCap
  have hzNe : z≠0 := norm_ne_zero_iff.mp (by rw [hz];norm_num)
  have hnNe : n≠0 := by
    intro h0
    have hh := norm_sub_norm_le z (-(b+e))
    have hbe := (norm_add_le b e).trans (add_le_add hb8 he8)
    rw [norm_neg,sub_neg_eq_add,hz,show z+(b+e)=n from rfl,h0,norm_zero] at hh
    linarith
  obtain ⟨hCov1,hCov2⟩ := packet_constant_radius_phase_covectors_of_identity S L P lam hlam r hr y hy.2 hrRoom z hzRoom rho hRho hFamily
  have hCovJ (eta : R3) : r*fderiv ℝ rho (x,y) (J eta,0)=⟪z,eta⟫_ℝ := by
    rw [hCov1 (J eta)]
    change r*(r⁻¹*⟪z,ContinuousLinearMap.inverse J (J eta)⟫_ℝ)=⟪z,eta⟫_ℝ
    rw [hInvJ.inverse_apply_self,←mul_assoc,mul_inv_cancel₀ hr.ne',one_mul]
  have hrSmooth : ContDiff ℝ ∞ rad := contDiff_referenceRadius_actual delta Rstar p L hd hRs
  obtain ⟨hE1,hE2⟩ := native_energy_phase_covectors rho rad x y z J F V
    (hRho.differentiableAt (by simp)) (hrSmooth.differentiable (by simp) y) hCovJ
    (by intro i;simpa only [V,frameOperator_coordinateVector] using hCov2 i)
  have hE2' (X : R3) : fderiv ℝ E (x,y) (0,F X)=(-r)*⟪n,X⟫_ℝ := by
    simpa only [E,n,e,add_assoc,neg_mul] using hE2 X
  have hPos1 : (conformalReferenceMatrix S.g1 L lam x).PosDef := by
    rw [←referenceMetric_eq_conformalReferenceMatrix S.g1 L lam]
    exact EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef S.g1 S.g1_admissible lam) x
  have hPos2 : ((referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam y)⁻¹).PosDef :=
    (normalizedPrincipalMatrix_posDef _ _
      (EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef S.g1 S.g1_admissible lam) y)
      (dilatedMetric_posDef S.g2 S.g2_admissible lam y)).inv
  let ell := fderiv ℝ E (x,y)
  let H := fun A B : R3 × R3 => fderiv ℝ (fderiv ℝ E) (x,y) A B-
    ell (Gamma1 x A.1 B.1,Gamma2 y A.2 B.2)
  let q1 := (⟪z,T1 z⟫_ℝ)⁻¹ • T1 z
  let q2 := (⟪n,T2 n⟫_ℝ)⁻¹ • T2 n
  apply productHessianStrictAt_of_normalized_frames
    (conformalReferenceMatrix S.g1 L lam)
    (fun Y : R3 => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam Y)⁻¹)
    x y E hPos1 hPos2 J F Q1 Q2 T1 T2 r hr.ne' z n hzNe hnNe hJQ hFQ hTR1 hTR2 hE1 hE2'
  change ∀ u w : R3, ⟪z,u⟫_ℝ=0 →
    ⟪J.adjoint (M1 x (J u)),u⟫_ℝ=(⟪z,T1 z⟫_ℝ)⁻¹ →
    ⟪n,w⟫_ℝ=0 → ⟪F.adjoint (M2 y (F w)),w⟫_ℝ=(⟪n,T2 n⟫_ℝ)⁻¹ →
    0<H (J q1,F q2) (J q1,F q2)+H (J u,F w) (J u,F w)
  intro u w huOrth huLength hwOrth hwLength
  have hGarg : G u=J.adjoint (M1 x (J u)) := congrArg (fun A : R3 →L[ℝ] R3 => A u) hGdict
  have hULength : ⟪u,G u⟫_ℝ=(⟪z,T1 z⟫_ℝ)⁻¹ := by
    calc
      _ = ⟪u,J.adjoint (M1 x (J u))⟫_ℝ := congrArg (fun W : R3 => ⟪u,W⟫_ℝ) hGarg
      _ = ⟪J.adjoint (M1 x (J u)),u⟫_ℝ := real_inner_comm _ _
      _ = _ := huLength
  have hWLength : ⟪w,R2 w⟫_ℝ=(⟪n,T2 n⟫_ℝ)⁻¹ := by
    calc
      _ = ⟪R2 w,w⟫_ℝ := real_inner_comm _ _
      _ = _ := hwLength
  have hSmall : eps*r ≤ t := hSmall0
  apply Hnum eps heps hepsA' beta r hBeta hr hr1 hEta1 hEta2 T1 G T2 R2 z b e u w
    hz hb8 he8 hbNorm.le heNorm hNear1 hNear2' hInvG.inverse_apply_self hT2R2 huOrth
    hULength hwOrth hWLength
    (fun U V => H (J U,F V) (J U,F V))
  intro U V
  have hRef := Hr lam hlam y hy.2 delta Rstar hd hRs p (le_min hr1 hrRoom) z hz rho
    (hRho.of_le (by simp)) hFamily c hLog U V
  have hConn := Hg lam hlam delta Rstar eps hd hd1 hRs heps heps1 p hBoot y hy
    (le_min hr1 hrRoom) hSmall hBeta1 z hz rho hRho hFamily (J U) V
  have hErr := (abs_le.mp hConn).1
  change _ ≤ H (J U,F V) (J U,F V)
  nlinarith only [hRef,hErr]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
