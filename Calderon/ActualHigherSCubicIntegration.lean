import Calderon.ActualHigherSScalarCommutatorForm

/-! Weighted diagonal cubic integration, with density and coefficient derivatives.
This is an auxiliary identity, with no actual atom specialization or quantitative estimate. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSCubicIntegration
open PrincipalCommutator ActualScalarPrincipalAdjoint PerturbedDensityAdjoint
  ActualHigherSScalarCommutatorForm ActualScalarPrincipalSelfFormBound
  ActualHigherSScalarCommutatorCoefficients
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Weighted diagonal integration exposes the skew cubic form without a high
angular norm of the derivative; all four integrabilities are derived. -/
theorem weighted_diagonal_pairing_eq_skew_sub_derivatives
    (Q : R3 → E →L[ℝ] E →L[ℝ] ℝ) (mu : R3 → ℝ) (U : R3 → E)
    (K : Set R3) (hK : IsCompact K) (hmu : ContDiff ℝ ∞ mu)
    (hU : ContDiff ℝ ∞ U) (h0 : ∀ x ∉ K, U x = 0)
    (hQ : ∀ x ∈ K, ContDiffAt ℝ ∞ Q x) (X : R3) :
    Integrable (fun x => mu x*Q x (directionalFDeriv X U x) (U x)) ∧
    Integrable (fun x => mu x*Q x (U x) (directionalFDeriv X U x)) ∧
    Integrable (fun x => directionalFDeriv X mu x*Q x (U x) (U x)) ∧
    Integrable (fun x => mu x*directionalFDeriv X Q x (U x) (U x)) ∧
    2*(∫ x, mu x*Q x (directionalFDeriv X U x) (U x)) =
      (∫ x, mu x*(Q x (directionalFDeriv X U x) (U x)-
        Q x (U x) (directionalFDeriv X U x)))-
      (∫ x, directionalFDeriv X mu x*Q x (U x) (U x))-
      (∫ x, mu x*directionalFDeriv X Q x (U x) (U x)) := by
  let P : E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).flip
  let A : R3 → ℝ := fun x => mu x*Q x (directionalFDeriv X U x) (U x)
  let B : R3 → ℝ := fun x => mu x*Q x (U x) (directionalFDeriv X U x)
  let C : R3 → ℝ := fun x => directionalFDeriv X mu x*Q x (U x) (U x)
  let D : R3 → ℝ := fun x => mu x*directionalFDeriv X Q x (U x) (U x)
  have hdu := contDiff_directionalFDeriv X U hU
  have hdu0 : ∀ x ∉ K, directionalFDeriv X U x = 0 :=
    fun x hx => directional_eq_zero_off U K hK.isClosed h0 X x hx
  have hAi : Integrable A := by
    have h := integrable_weighted_supported_operator_pair P mu U (directionalFDeriv X U) Q
      K hK hmu.continuous hU.continuous hdu hdu0 hQ
    simpa only [P, ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply] using h
  have hBi : Integrable B := by
    have h := integrable_weighted_supported_operator_pair P mu (directionalFDeriv X U) U Q
      K hK hmu.continuous hdu.continuous hU h0 hQ
    simpa only [P, ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply] using h
  have hCi : Integrable C := by
    have h := integrable_weighted_supported_operator_pair P (directionalFDeriv X mu) U U Q
      K hK (contDiff_directionalFDeriv X mu hmu).continuous hU.continuous hU h0 hQ
    simpa only [P, ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply] using h
  have hDi : Integrable D := by
    have h := integrable_weighted_supported_operator_pair P mu U U (directionalFDeriv X Q)
      K hK hmu.continuous hU.continuous hU h0
      (fun x hx => contDiffAt_directional Q x X (hQ x hx))
    simpa only [P, ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply] using h
  let z : R3 → E →L[ℝ] ℝ := fun x => Q x (U x)
  let f : R3 → E := fun x => mu x • U x
  have hz : ContDiff ℝ ∞ z :=
    contDiff_supported_operator_apply U Q K hK.isClosed hU h0 hQ
  have hzc : HasCompactSupport z := compact_supported_operator_apply U Q K hK h0
  have hf : ContDiff ℝ ∞ f := hmu.smul hU
  have hfi : Integrable (fun x => P (directionalFDeriv X f x) (z x)) :=
    compact_bilinear_integrable P _ _ (contDiff_directionalFDeriv X f hf).continuous hz.continuous hzc
  have hzi : Integrable (fun x => P (f x) (directionalFDeriv X z x)) :=
    compact_bilinear_integrable P _ _ hf.continuous (contDiff_directionalFDeriv X z hz).continuous
      (hzc.fderiv_apply (𝕜 := ℝ) X)
  have hbase : Integrable (fun x => P (f x) (z x)) :=
    compact_bilinear_integrable P _ _ hf.continuous hz.continuous hzc
  have hg := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := P) (v := X) hfi hzi hbase
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hz.differentiable (by simp) x)
  have hzD (x : R3) : directionalFDeriv X z x =
      directionalFDeriv X Q x (U x)+Q x (directionalFDeriv X U x) :=
    directional_operator_apply_supported U Q K hK.isClosed hU h0 hQ X x
  have hfD (x : R3) : directionalFDeriv X f x =
      directionalFDeriv X mu x • U x+mu x • directionalFDeriv X U x :=
    directional_smul_at mu U x X hmu.contDiffAt hU.contDiffAt
  have hleft : (fun x => P (f x) (directionalFDeriv X z x)) = fun x => D x+A x := by
    funext x
    change (directionalFDeriv X z x) (f x) = D x+A x
    rw [hzD x]
    simp only [f,D,A,ContinuousLinearMap.add_apply,map_smul,smul_eq_mul]
    ring
  have hright : (fun x => P (directionalFDeriv X f x) (z x)) = fun x => C x+B x := by
    funext x
    change z x (directionalFDeriv X f x) = C x+B x
    rw [hfD x]
    simp only [z,C,B,map_add,map_smul,smul_eq_mul]
  change (∫ x, P (f x) (directionalFDeriv X z x)) =
    -(∫ x, P (directionalFDeriv X f x) (z x)) at hg
  rw [hleft,hright,integral_add hDi hAi,integral_add hCi hBi] at hg
  refine ⟨hAi,hBi,hCi,hDi,?_⟩
  have hskew : (fun x => mu x*(Q x (directionalFDeriv X U x) (U x)-
      Q x (U x) (directionalFDeriv X U x))) = fun x => A x-B x := by
    funext x
    dsimp only [A,B]
    ring
  rw [hskew,integral_sub hAi hBi]
  change 2*(∫ x, A x) = ((∫ x, A x)-(∫ x, B x))-(∫ x, C x)-(∫ x, D x)
  linarith only [hg]
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSCubicIntegration
