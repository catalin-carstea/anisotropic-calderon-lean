import Calderon.ActualNativeKernelDatumUniformFirstJet
import Calderon.ActualUniformHighDensityOperator
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError SphereHarmonic
  ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint

/-- A common finite-jet budget gives the original high-density value and first derivative. -/
theorem exists_nativeMixedKernelHighDensity_uniform_firstJet_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) (Q : Set (ℝ × (R3 × ℝ))) (hQ : IsCompact Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Gext : R3×R3→ℝ) (hG : ContDiff ℝ ∞ Gext)
      (v : ℝ × (R3 × ℝ)), v ∈ Q → ∀ M : ℝ, 0 ≤ M →
      (∀ j ≤ 5, ∀ z ∈ closedBall (0:R3) 3,
        ‖iteratedFDeriv ℝ j Gext (packetEndpoint S L P v.1 v.2.1 v.2.2 z,v.2.1)‖ ≤ M) →
      ‖nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L P Gext hG v‖ ≤ C*M ∧
      ‖fderiv ℝ (nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L P Gext hG) v‖ ≤ C*M := by
  obtain ⟨A,hA,HA⟩ := exists_nativeMixedKernelPullbackHkDatum_uniform_firstJet_bound hcalc S L P 3 Q hQ
  obtain ⟨B,hB,HB⟩ := exists_uniform_nativeHighDensityOperator_profile_firstJet_bound
    hcalc hreg hF hO hD τ0 S L P Q hQ
  refine ⟨B*A,mul_pos hB hA,?_⟩
  intro Gext hG v hv M hM hJets
  let E := nativeMixedKernelPullbackHkDatum S L P Gext hG 3
  have hE : ContDiff ℝ ∞ E := contDiff_nativeMixedKernelPullbackHkDatum hcalc S L P Gext hG 3
  have hEn := HA Gext hG v hv M hM hJets
  have h := HB E v hv (hE.differentiable (by simp) v) (A*M) (mul_nonneg hA.le hM) hEn.1 hEn.2
  have hApply : (fun w => nativeHighDensityOperator hcalc hF hO hD τ0 S L P w (E w)) =
      nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L P Gext hG := by
    funext w
    exact nativeHighDensityOperator_apply hcalc hF hO hD τ0 S L P E w
  have hValue := congrFun hApply v
  rw [hValue,hApply] at h
  simpa only [mul_assoc] using h

/-- The constant is common to the original finite cover and the full closed parameter box. -/
theorem exists_nativeCover_mixedKernelHighDensity_uniform_firstJet_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : KnownSideSourceData) (L : ℝ)
    (cover : NativeNormalCover S L) (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : Fin cover.count,
      ∀ (Gext : R3×R3→ℝ) (hG : ContDiff ℝ ∞ Gext)
      (lambda : ℝ), lambda ∈ Icc (0:ℝ) cover.dilationCeiling →
      ∀ y ∈ cylinder, ∀ r ∈ Icc a b, ∀ M : ℝ, 0 ≤ M →
      (∀ j ≤ 5, ∀ z ∈ closedBall (0:R3) 3,
        ‖iteratedFDeriv ℝ j Gext (packetEndpoint S L (cover.packet i) lambda y r z,y)‖ ≤ M) →
      ‖nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Gext hG (lambda,(y,r))‖ ≤ C*M ∧
      ‖fderiv ℝ (nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Gext hG) (lambda,(y,r))‖ ≤ C*M := by
  let Q : Set (ℝ × (R3×ℝ)) := Icc (0:ℝ) cover.dilationCeiling ×ˢ (cylinder ×ˢ Icc a b)
  have hQ : IsCompact Q := isCompact_Icc.prod (Geometry.isCompact_cylinder.prod isCompact_Icc)
  choose C hC HC using fun i : Fin cover.count =>
    exists_nativeMixedKernelHighDensity_uniform_firstJet_bound hcalc hreg hF hO hD τ0 S L (cover.packet i) Q hQ
  obtain ⟨B,hB⟩ := (Set.finite_range C).bddAbove
  let D : ℝ := max B 1
  refine ⟨D,zero_lt_one.trans_le (le_max_right _ _),?_⟩
  intro i Gext hG lambda hlambda y hy r hr M hM hJets
  have h := HC i Gext hG (lambda,(y,r)) ⟨hlambda,hy,hr⟩ M hM hJets
  have hCi : C i ≤ D := (hB (Set.mem_range_self i)).trans (le_max_left _ _)
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_right hCi hM),h.2.trans (mul_le_mul_of_nonneg_right hCi hM)⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
