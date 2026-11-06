import MixedKernelConformalProductCriterion
import Mathlib.Analysis.InnerProductSpace.Adjoint
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open MetricOperator MetricVolume ConnectionError
open scoped InnerProductSpace

/-- Derive the normalized frame vector from the original metric normal's actual duality. -/
theorem normalized_metric_covector_in_frame
    (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.PosDef)
    (ell : R3 →L[ℝ] ℝ) (hell : ell≠0) (F Q T : R3 →L[ℝ] R3) (c : ℝ) (hc : c≠0) (n : R3)
    (hFQ : ∀ W : R3, F (Q W)=W)
    (hTR : ∀ W : R3, T (F.adjoint (matrixOperatorMap G (F W)))=W)
    (hCov : ∀ eta : R3, ell (F eta)=c*⟪n,eta⟫_ℝ) :
    let a := normalizedMetricCovector G ell
    let K := ⟪matrixOperatorMap G a,a⟫_ℝ
    let q := c • Q a
    0 < ⟪n,T n⟫_ℝ ∧ q=(⟪n,T n⟫_ℝ)⁻¹ • T n ∧ c^2*K=(⟪n,T n⟫_ℝ)⁻¹ := by
  intro a K q
  obtain ⟨_hN,ha,hK,hDual⟩ := normalizedMetricCovector_data G hG ell hell
  change ell a=1 at ha
  change 0<K at hK
  change ∀ X : R3, ⟪matrixOperatorMap G a,X⟫_ℝ=K*ell X at hDual
  have hFq : F q=c • a := by dsimp only [q];rw [map_smul,hFQ]
  have hnq : ⟪n,q⟫_ℝ=1 := by
    have hh := hCov q
    rw [hFq,map_smul,smul_eq_mul,ha,mul_one] at hh
    exact (mul_left_cancel₀ hc) (by simpa only [mul_one] using hh.symm)
  let k := c^2*K
  have hk : 0<k := mul_pos (sq_pos_of_ne_zero hc) hK
  have hRq : F.adjoint (matrixOperatorMap G (F q))=k • n := by
    apply ext_inner_right ℝ
    intro eta
    rw [ContinuousLinearMap.adjoint_inner_left,hFq,map_smul,real_inner_smul_left,
      hDual,hCov,real_inner_smul_left]
    dsimp only [k]
    ring
  have hq : q=k • T n := by
    calc
      q=T (F.adjoint (matrixOperatorMap G (F q))) := (hTR q).symm
      _ = T (k • n) := congrArg T hRq
      _ = k • T n := map_smul T k n
  have hkN : k*⟪n,T n⟫_ℝ=1 := by
    rw [hq,real_inner_smul_right] at hnq
    exact hnq
  have hnT : 0<⟪n,T n⟫_ℝ := by nlinarith only [hkN,hk]
  have hkInv : k=(⟪n,T n⟫_ℝ)⁻¹ := by
    apply mul_left_cancel₀ hnT.ne'
    rw [mul_inv_cancel₀ hnT.ne']
    nlinarith only [hkN]
  exact ⟨hnT,by rw [hq,hkInv],hkInv⟩

/-- Derive the original imaginary constraints in the SAME frame, with the literal metric normal. -/
theorem normalized_metric_characteristic_in_frame
    (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.PosDef)
    (ell : R3 →L[ℝ] ℝ) (hell : ell≠0) (F Q T : R3 →L[ℝ] R3) (c : ℝ) (hc : c≠0) (n v : R3)
    (hFQ : ∀ W : R3, F (Q W)=W)
    (hTR : ∀ W : R3, T (F.adjoint (matrixOperatorMap G (F W)))=W)
    (hCov : ∀ eta : R3, ell (F eta)=c*⟪n,eta⟫_ℝ)
    (hOrth : ⟪matrixOperatorMap G v,normalizedMetricCovector G ell⟫_ℝ=0)
    (hLength : ⟪matrixOperatorMap G v,v⟫_ℝ=
      ⟪matrixOperatorMap G (normalizedMetricCovector G ell),normalizedMetricCovector G ell⟫_ℝ) :
    let u := c • Q v
    ⟪n,u⟫_ℝ=0 ∧ ⟪F.adjoint (matrixOperatorMap G (F u)),u⟫_ℝ=(⟪n,T n⟫_ℝ)⁻¹ := by
  intro u
  let a := normalizedMetricCovector G ell
  let K := ⟪matrixOperatorMap G a,a⟫_ℝ
  obtain ⟨_hN,_ha,hK,hDual⟩ := normalizedMetricCovector_data G hG ell hell
  change 0<K at hK
  change ∀ X : R3, ⟪matrixOperatorMap G a,X⟫_ℝ=K*ell X at hDual
  have hSym (U V : R3) : ⟪matrixOperatorMap G U,V⟫_ℝ=⟪matrixOperatorMap G V,U⟫_ℝ := by
    have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hG.isHermitian
    exact (hs U V).trans (real_inner_comm _ _)
  have hv : ell v=0 := by
    have hh := hDual v
    rw [← hSym v a,hOrth] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hK.ne'
  have hFu : F u=c • v := by dsimp only [u];rw [map_smul,hFQ]
  have hnU : ⟪n,u⟫_ℝ=0 := by
    have hh := hCov u
    rw [hFu,map_smul,smul_eq_mul,hv,mul_zero] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hc
  obtain ⟨_hpos,_hq,hk⟩ := normalized_metric_covector_in_frame G hG ell hell F Q T c hc n hFQ hTR hCov
  refine ⟨hnU,?_⟩
  rw [ContinuousLinearMap.adjoint_inner_left,hFu,map_smul,real_inner_smul_left,real_inner_smul_right,hLength]
  change c*(c*K)=(⟪n,T n⟫_ℝ)⁻¹
  nlinarith only [hk]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
