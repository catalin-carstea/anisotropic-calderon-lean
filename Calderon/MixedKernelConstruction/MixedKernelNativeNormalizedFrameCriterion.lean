import Calderon.MixedKernelConstruction.MixedKernelNormalizedMetricFrame
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open MetricOperator MetricVolume ConnectionError
open scoped InnerProductSpace

/-- Transfer the SAME actual joint Hessian positivity from both normalized frames to the literal native test. -/
theorem productHessianStrictAt_of_normalized_frames
    (g1 g2 : MatrixField) (x y : R3) (rho : R3 × R3 → ℝ)
    (hg1 : (g1 x).PosDef) (hg2 : (g2 y).PosDef)
    (J F Q1 Q2 T1 T2 : R3 →L[ℝ] R3) (r : ℝ) (hr : r≠0) (z n : R3)
    (hz : z≠0) (hn : n≠0)
    (hJQ : ∀ X : R3, J (Q1 X)=X) (hFQ : ∀ X : R3, F (Q2 X)=X)
    (hTR1 : ∀ X : R3, T1 (J.adjoint (matrixOperatorMap (g1 x) (J X)))=X)
    (hTR2 : ∀ X : R3, T2 (F.adjoint (matrixOperatorMap (g2 y) (F X)))=X)
    (hCov1 : ∀ X : R3, (fderiv ℝ rho (x,y)) (J X,0)=r*⟪z,X⟫_ℝ)
    (hCov2 : ∀ X : R3, (fderiv ℝ rho (x,y)) (0,F X)=-r*⟪n,X⟫_ℝ) :
    let ell := fderiv ℝ rho (x,y)
    let M1 := metricOperatorField g1 x
    let M2 := metricOperatorField g2 y
    let Gamma1 := coordinateConnectionField (inverseMetricField (metricOperatorField g1)) (metricOperatorField g1) x
    let Gamma2 := coordinateConnectionField (inverseMetricField (metricOperatorField g2)) (metricOperatorField g2) y
    let H := fun A B : R3 × R3 => fderiv ℝ (fderiv ℝ rho) (x,y) A B-ell (Gamma1 A.1 B.1,Gamma2 A.2 B.2)
    let q1 := (⟪z,T1 z⟫_ℝ)⁻¹ • T1 z
    let q2 := (⟪n,T2 n⟫_ℝ)⁻¹ • T2 n
    (∀ u w : R3, ⟪z,u⟫_ℝ=0 →
      ⟪J.adjoint (M1 (J u)),u⟫_ℝ=(⟪z,T1 z⟫_ℝ)⁻¹ →
      ⟪n,w⟫_ℝ=0 → ⟪F.adjoint (M2 (F w)),w⟫_ℝ=(⟪n,T2 n⟫_ℝ)⁻¹ →
      0<H (J q1,F q2) (J q1,F q2)+H (J u,F w) (J u,F w)) →
    ProductHessianStrictAt g1 g2 x y rho := by
  intro ell M1 M2 Gamma1 Gamma2 H q1 q2 hPositive
  let ell1 := ell.comp (ContinuousLinearMap.inl ℝ R3 R3)
  let ell2 := ell.comp (ContinuousLinearMap.inr ℝ R3 R3)
  have hCov1' (X : R3) : ell1 (J X)=r*⟪z,X⟫_ℝ := hCov1 X
  have hCov2' (X : R3) : ell2 (F X)=(-r)*⟪n,X⟫_ℝ := hCov2 X
  have hell1 : ell1≠0 := by
    intro h0
    have hh := hCov1' z
    rw [h0,ContinuousLinearMap.zero_apply,real_inner_self_eq_norm_sq] at hh
    exact (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)) ((mul_eq_zero.mp hh.symm).resolve_left hr)
  have hell2 : ell2≠0 := by
    intro h0
    have hh := hCov2' n
    rw [h0,ContinuousLinearMap.zero_apply,real_inner_self_eq_norm_sq] at hh
    exact (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)) ((mul_eq_zero.mp hh.symm).resolve_left (neg_ne_zero.mpr hr))
  let a1 := normalizedMetricCovector (g1 x) ell1
  let a2 := normalizedMetricCovector (g2 y) ell2
  obtain ⟨_,hq1,_⟩ := normalized_metric_covector_in_frame (g1 x) hg1 ell1 hell1 J Q1 T1 r hr z hJQ hTR1 hCov1'
  obtain ⟨_,hq2,_⟩ := normalized_metric_covector_in_frame (g2 y) hg2 ell2 hell2 F Q2 T2 (-r) (neg_ne_zero.mpr hr) n hFQ hTR2 hCov2'
  change r • Q1 a1=q1 at hq1
  change (-r) • Q2 a2=q2 at hq2
  have hJq : J q1=r • a1 := by rw [←hq1,map_smul,hJQ]
  have hFq : F q2=(-r) • a2 := by rw [←hq2,map_smul,hFQ]
  have hReal : (J q1,F q2)=r • (a1,-a2) := by rw [hJq,hFq];simp only [Prod.smul_mk,smul_neg,neg_smul]
  have hHom (c : ℝ) (A : R3 × R3) : H (c • A) (c • A)=c^2*H A A := by
    have hD : fderiv ℝ (fderiv ℝ rho) (x,y) (c • A) (c • A)=
        c*c*fderiv ℝ (fderiv ℝ rho) (x,y) A A := by
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul,mul_assoc]
    have hGamma : (Gamma1 (c • A).1 (c • A).1,Gamma2 (c • A).2 (c • A).2)=
        (c*c) • (Gamma1 A.1 A.1,Gamma2 A.2 A.2) := by
      simp only [Prod.smul_fst,Prod.smul_snd,map_smul,ContinuousLinearMap.smul_apply,smul_smul,Prod.smul_mk]
    dsimp only [H]
    rw [hD,hGamma,map_smul]
    simp only [smul_eq_mul]
    ring
  change ell1≠0 ∧ ell2≠0 ∧ ∀ v1 v2 : R3,
    ⟪M1 v1,a1⟫_ℝ=0 → ⟪M1 v1,v1⟫_ℝ=⟪M1 a1,a1⟫_ℝ →
    ⟪M2 v2,a2⟫_ℝ=0 → ⟪M2 v2,v2⟫_ℝ=⟪M2 a2,a2⟫_ℝ →
    0<H (a1,-a2) (a1,-a2)+H (v1,v2) (v1,v2)
  refine ⟨hell1,hell2,?_⟩
  intro v1 v2 ho1 hl1 ho2 hl2
  let u := r • Q1 v1
  let w := r • Q2 v2
  obtain ⟨hu,huLen⟩ := normalized_metric_characteristic_in_frame (g1 x) hg1 ell1 hell1 J Q1 T1 r hr z v1 hJQ hTR1 hCov1' ho1 hl1
  obtain ⟨hwNeg,hwNegLen⟩ := normalized_metric_characteristic_in_frame (g2 y) hg2 ell2 hell2 F Q2 T2 (-r) (neg_ne_zero.mpr hr) n v2 hFQ hTR2 hCov2' ho2 hl2
  change ⟪z,u⟫_ℝ=0 at hu
  change ⟪J.adjoint (M1 (J u)),u⟫_ℝ=(⟪z,T1 z⟫_ℝ)⁻¹ at huLen
  have hw : ⟪n,w⟫_ℝ=0 := by
    change ⟪n,(-r) • Q2 v2⟫_ℝ=0 at hwNeg
    simpa only [neg_smul,inner_neg_right,neg_eq_zero] using hwNeg
  have hwLen : ⟪F.adjoint (M2 (F w)),w⟫_ℝ=(⟪n,T2 n⟫_ℝ)⁻¹ := by
    change ⟪F.adjoint (M2 (F ((-r) • Q2 v2))),(-r) • Q2 v2⟫_ℝ=(⟪n,T2 n⟫_ℝ)⁻¹ at hwNegLen
    simpa only [neg_smul,map_neg,inner_neg_left,inner_neg_right,neg_neg] using hwNegLen
  have hImag : (J u,F w)=r • (v1,v2) := by
    dsimp only [u,w]
    rw [map_smul,map_smul,hJQ,hFQ]
    rfl
  have hPos := hPositive u w hu huLen hw hwLen
  rw [hReal,hImag,hHom,hHom] at hPos
  have hMul : 0<r^2*(H (a1,-a2) (a1,-a2)+H (v1,v2) (v1,v2)) := by nlinarith only [hPos]
  exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hr)).mp hMul

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
