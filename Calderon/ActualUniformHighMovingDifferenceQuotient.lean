import Calderon.ActualNativeMovingLocalRemainderSigned
import Calderon.ActualReferenceRadialEndpointJointJets
import Calderon.ActualScaledHighFirstNativeRoomBounds
import Calderon.ActualRadiusScaledMovingAlgebra
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame

private lemma norm_regular_three_terms_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : V →L[ℝ] W) (A : V →L[ℝ] V) (J : V →L[ℝ] W) (c M : ℝ)
    (hM : 0 ≤ M) (hT : ‖T‖ ≤ M) (hA : ‖A‖ ≤ M) (hJ : ‖J‖ ≤ M) (hc : |c| ≤ M) :
    ‖T.comp A+J+c • T‖ ≤ 2*M^2+M := by
  have hTA : ‖T.comp A‖ ≤ M*M := (ContinuousLinearMap.opNorm_comp_le T A).trans
    (mul_le_mul hT hA (norm_nonneg _) hM)
  have hcT : ‖c • T‖ ≤ M*M := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hc hT (norm_nonneg _) hM
  calc
    _ ≤ ‖T.comp A+J‖+‖c • T‖ := norm_add_le _ _
    _ ≤ (‖T.comp A‖+‖J‖)+‖c • T‖ := by linarith only [norm_add_le (T.comp A) J]
    _ ≤ (M*M+M)+M*M := add_le_add (add_le_add hTA hJ) hcT
    _ = _ := by ring

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] harmonicSphereSubspace referenceHighAdjointMovingDifferenceQuotient
  referenceHighAdjointMovingActualJetNormalizedCorrection referenceHighAdjointRadialSecondRemainder
  referenceHighAdjointJacobiBoundaryCorrection referenceHighAdjointJacobiBoundaryCorrectionFamily
  sphereSobolevLinearCoordinateMulL referenceRadiusHorizontalLogDerivative

theorem exists_uniform_referenceHighAdjointMovingDifferenceQuotient_operator_bound
    (hreg : FixedDirichletRegularity) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧ ∃ U : ℝ, 1 ≤ U ∧
      ∀ q ∈ Icc (0:ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ →
      ∀ R : R3 → ℝ, ContDiff ℝ ∞ R → |R y| ≤ d → R y ≠ 0 → ‖fderiv ℝ R y‖ ≤ 1 →
      (∀ x : UnitSphere, (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible) →
      ∀ i : Fin 3, ‖referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i‖ ≤ U := by
  obtain ⟨d0,hd0,hd0ρ,hRoom⟩ := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  have hρ : 0 < ρ := hd0.trans_le hd0ρ
  have hAmbient := exists_reference_radial_endpoint_uniform_joint_jets
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  unfold radialEndpointUniformJointJetsTarget at hAmbient
  obtain ⟨dE,hdE,hdEρ,hdE1,hJets⟩ := hAmbient
  obtain ⟨hSmooth,CE,hCE,hBounds⟩ := hJets 0
  obtain ⟨G,hG,hGeom⟩ := exists_actual_room_referenceScaledHighFirst_coefficients_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  let A := 1+∑ i : Fin 3, ‖sphereSobolevLinearCoordinateMulL hF hO hD (3/2:ℝ) (EuclideanSpace.single i 1)‖
  have hA (i : Fin 3) : ‖sphereSobolevLinearCoordinateMulL hF hO hD (3/2:ℝ) (EuclideanSpace.single i 1)‖ ≤ A :=
    (Finset.single_le_sum (fun j _ => norm_nonneg (sphereSobolevLinearCoordinateMulL hF hO hD (3/2:ℝ) (EuclideanSpace.single j 1))) (Finset.mem_univ i)).trans
      (by dsimp [A]; linarith)
  let M := max CE (max G A)
  have hMC : CE ≤ M := le_max_left _ _
  have hMG : G ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hMA : A ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hM : 1 ≤ M := hG.trans hMG
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let d := min d0 (min dE 1)
  have hd : 0 < d := lt_min hd0 (lt_min hdE one_pos)
  have hdd0 : d ≤ d0 := min_le_left _ _
  have hddE : d ≤ dE := (min_le_right _ _).trans (min_le_left _ _)
  have hd1 : d ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨d,hd,hdd0.trans hd0ρ,hd1,2*M^2+M+1,by nlinarith [sq_nonneg M],?_⟩
  intro q hq y hy R hR hrBound hr hDR hInv i
  have hy4 : ‖y-y0‖ ≤ 4*ρ := hy.trans (by linarith)
  have hr4 : |R y| ≤ 4*ρ := hrBound.trans ((hdd0.trans hd0ρ).trans (by linarith))
  have hGeo := hGeom q hq y hy4 (R y) hr4 i
  have hSegment (t : ℝ) (ht : t ∈ uIcc (0:ℝ) (R y)) : (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
    have hab : |t| ≤ |R y| := by
      rcases le_total 0 (R y) with hp | hn
      · rw [uIcc_of_le hp] at ht
        rw [abs_of_nonneg ht.1,abs_of_nonneg hp]
        exact ht.2
      · rw [uIcc_of_ge hn] at ht
        rw [abs_of_nonpos ht.2,abs_of_nonpos hn]
        linarith [ht.1]
    exact hRoom ⟨hq,by simpa only [mem_closedBall,dist_eq_norm] using hy,
      abs_le.mp (hab.trans (hrBound.trans hdd0))⟩
  have hz : (q,(y,R y)) ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dE) dE) :=
    ⟨hq,by simpa only [mem_closedBall,dist_eq_norm] using hy,abs_le.mp (hrBound.trans hddE)⟩
  have hT : ‖referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y)‖ ≤ M := by
    have h := (hBounds 0 (by norm_num) (q,(y,R y)) hz).1.2
    rw [norm_iteratedFDeriv_zero] at h
    unfold referenceHighAdjointRadialSecondRemainder
    exact h.trans hMC
  have hV := hGeo.2.2.2.2.2
  have hScalar : |fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i))| ≤ M := by
    calc
      _ = ‖fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ R y‖*‖conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)‖ := (fderiv ℝ R y).le_opNorm _
      _ ≤ 1*G := mul_le_mul hDR hV (norm_nonneg _) (by norm_num)
      _ = G := one_mul _
      _ ≤ M := hMG
  have hSigned := referenceHighAdjointMovingDifferenceQuotient_eq_signed_correction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq y hy R hR i hr hInv hSegment
  have hJ := referenceHighAdjointJacobiBoundaryCorrectionFamily_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,R y)) i hInv
  have hLog := referenceRadiusHorizontalLogDerivative_mul_radius g L q R y i (hR.differentiable (by simp) y) hr
  have hCorrect := congrArg₂ (fun J c =>
    (referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y)).comp
      (sphereSobolevLinearCoordinateMulL hF hO hD (3/2:ℝ) (EuclideanSpace.single i 1)) +J+
    c • referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y)) hJ.symm hLog
  have hCorrect' : referenceHighAdjointMovingActualJetNormalizedCorrection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y (R y)
        (referenceRadiusHorizontalLogDerivative g L q R y i) i hInv =
      (referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y)).comp
        (sphereSobolevLinearCoordinateMulL hF hO hD (3/2:ℝ) (EuclideanSpace.single i 1)) +
      referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,R y)) i +
      fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)) •
        referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y) := by
    unfold referenceHighAdjointMovingActualJetNormalizedCorrection
    exact hCorrect
  have hExact := hSigned.trans hCorrect' 
  have hNorm := congrArg norm hExact
  have hBound := norm_regular_three_terms_le
    (referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y))
    (sphereSobolevLinearCoordinateMulL hF hO hD (3/2:ℝ) (EuclideanSpace.single i 1))
    (referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,R y)) i)
    (fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i))) M hM0 hT ((hA i).trans hMA) (hGeo.2.1.trans hMG) hScalar
  exact hNorm.le.trans (hBound.trans (by linarith))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
