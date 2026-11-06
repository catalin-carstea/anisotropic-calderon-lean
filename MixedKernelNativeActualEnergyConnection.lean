import MixedKernelNativeEnergyYBound
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator NormalCoordinatesFrame
open ActualScalarPrincipalAdjoint ReferenceWeightedApproximation
open NormalizedPrincipalMetric
open scoped ContDiff Topology InnerProductSpace

/-- The FULL actual energy Hessian changes by O(eps r squared) under the TRUE normalized second connection. -/
theorem exists_packet_actual_energy_connection_error
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ C t : ℝ, 0<C ∧ 0<t ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ delta Rstar eps : ℝ, 0<delta → delta ≤ 1 → 0<Rstar → 0 ≤ eps → eps ≤ 1 → ∀ p : ℕ,
      CurrentRadiusBootstrap S L lam delta Rstar eps p →
      ∀ y ∈ cylinder∩P.centers,
      let r := referenceRadius delta Rstar p L
      r y ≤ min 1 (4*P.rho) → eps*r y ≤ t →
      1 ≤ actualReferenceBeta S.g1 L lam delta Rstar p y →
      ∀ z : R3, ‖z‖=1 →
      let x := packetEndpoint S L P lam y (r y) z
      let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
      let G := metricOperatorField (conformalReferenceMatrix S.g1 L lam)
      let M := metricOperatorField (fun Y => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam Y)⁻¹)
      let Gamma := coordinateConnectionField (inverseMetricField G) G
      let Gamma2 := coordinateConnectionField (inverseMetricField M) M
      ∀ rho : R3 × R3 → ℝ, ContDiffAt ℝ ∞ rho (x,y) →
      (∀ᶠ a : R3 × R3 in 𝓝 (y,z), rho (packetEndpoint S L P lam a.1 (r y) a.2,a.1)=(⟪a.2,a.2⟫_ℝ-1)/2) →
      ∀ X V : R3,
      let E := nativeEnergyPhase (r y) rho r
      |(fderiv ℝ (fderiv ℝ E) (x,y) (X,F V) (X,F V)-
          fderiv ℝ E (x,y) (Gamma x X X,Gamma2 y (F V) (F V)))-
        (fderiv ℝ (fderiv ℝ E) (x,y) (X,F V) (X,F V)-
          fderiv ℝ E (x,y) (Gamma x X X,Gamma y (F V) (F V)))| ≤ C*eps*(r y)^2*‖V‖^2 := by
  obtain ⟨Cy,hCy,HY⟩ := exists_packet_actual_energy_y_covector_bound S L P
  obtain ⟨Cg,t,hCg,ht,HG⟩ := exists_actual_normalized_second_connection_error_bound S L
  let K : Set (ℝ × R3) := Icc (0 : ℝ) 1×ˢclosedBall P.y0 (4*P.rho)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨B0,HB⟩ := hK.exists_bound_of_continuousOn
    (contDiff_conformalReferenceGramFrameOperatorJoint S.g1 S.g1_admissible L).continuous.continuousOn
  let B := |B0|+1
  have hB : 0<B := by dsimp [B];positivity
  refine ⟨Cy*Cg*B^2,t,by positivity,ht,?_⟩
  intro lam hlam delta Rstar eps hd hd1 hRs heps heps1 p hBoot y hy r hrCap hSmall hb z hz x F G M Gamma Gamma2 rho hRho hFamily X V E
  have hrPos : 0<r y := referenceRadius_pos delta Rstar p L y hd hRs
  have hzRoom : z ∈ closedBall (0 : R3) 2 := by simp only [mem_closedBall,dist_zero_right,hz];norm_num
  obtain ⟨_hCov1,hCov2⟩ := packet_constant_radius_phase_covectors_of_identity S L P lam hlam (r y) hrPos y hy.2
    (hrCap.trans (min_le_right _ _)) z hzRoom rho hRho hFamily
  have hRadiusBoot := hBoot.2 delta ⟨le_rfl,hd1⟩ y hy.1
  let ell := fderiv ℝ E (x,y)
  let ellY := ell.comp (ContinuousLinearMap.inr ℝ R3 R3)
  have hEll : ‖ellY‖ ≤ Cy*r y := HY lam hlam y hy.2 delta Rstar eps p hd hRs heps1 z hz hrCap rho
    (hRho.differentiableAt (by simp)) hCov2 hb hRadiusBoot
  have hGamma : ‖Gamma2 y-Gamma y‖ ≤ Cg*eps*r y := by
    simpa only [mul_assoc] using HG lam hlam delta Rstar eps p hBoot y hy.1 hSmall
  have hFrame : ‖F‖ ≤ B := (HB (lam,y) ⟨hlam,by
    simpa only [mem_closedBall,dist_eq_norm] using (P.centers_room y hy.2).1.le⟩).trans
      ((le_abs_self B0).trans (by dsimp [B];linarith))
  have hFV : ‖F V‖ ≤ B*‖V‖ := (F.le_opNorm V).trans (mul_le_mul_of_nonneg_right hFrame (norm_nonneg V))
  have hErr := native_energy_y_hessian_connection_error_le ellY 0 (Gamma2 y) (Gamma y) (F V) (F V)
    Cy Cg eps (r y) hCy.le hCg.le heps hrPos.le hEll hGamma
  have hSplit (A D : R3) : ell (A,D)=ell (A,0)+ellY D := by
    have hh := ell.comp_inl_add_comp_inr (A,D)
    exact hh.symm
  change |(_-ell (Gamma x X X,Gamma2 y (F V) (F V)))-
    (_-ell (Gamma x X X,Gamma y (F V) (F V)))| ≤ _
  rw [hSplit (Gamma x X X) (Gamma2 y (F V) (F V)),
    hSplit (Gamma x X X) (Gamma y (F V) (F V))]
  have hEq (a b d h : ℝ) : (h-(a+b))-(h-(a+d))=(0-b)-(0-d) := by ring
  rw [hEq]
  calc
    _  ≤  (Cy*Cg)*eps*(r y)^2*‖F V‖*‖F V‖ := by simpa only [ContinuousLinearMap.zero_apply] using hErr
    _  ≤  (Cy*Cg)*eps*(r y)^2*(B*‖V‖)*(B*‖V‖) := by gcongr
    _ = (Cy*Cg*B^2)*eps*(r y)^2*‖V‖^2 := by ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
