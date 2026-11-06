import Calderon.ConformalConnection
import Calderon.ProfileChain
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI.AnisotropicCalderon.ConformalDepth
open OAI.AnisotropicCalderon.ConnectionError
open OAI.AnisotropicCalderon.RadiusProfile
open scoped Topology

noncomputable def depthPrimitive (L s₀ s : ℝ) : ℝ :=
  (Real.exp (-2*L*s₀) - Real.exp (-2*L*s))/(2*L)

theorem hasDerivAt_depthPrimitive (L s₀ s : ℝ) (hL : L ≠ 0) :
    HasDerivAt (depthPrimitive L s₀) (Real.exp (-2*L*s)) s := by
  have he := ((hasDerivAt_id' s).const_mul (-2*L)).exp
  have h := ((hasDerivAt_const s (Real.exp (-2*L*s₀))).sub he).div_const (2*L)
  convert! h using 1 <;> field_simp [hL] <;> ring

theorem depthPrimitive_eq_integral (L s₀ s : ℝ) (hL : L ≠ 0) :
    depthPrimitive L s₀ s = ∫ u in s₀..s, Real.exp (-2*L*u) := by
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (-2*L*u))
      MeasureTheory.volume s₀ s := by
    exact (show Continuous (fun u : ℝ => Real.exp (-2*L*u)) by fun_prop).intervalIntegrable s₀ s
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_depthPrimitive L s₀ u hL) hint
  simpa only [depthPrimitive, sub_self, zero_div, sub_zero] using h.symm

theorem depthPrimitive_zero_neg (L s₀ : ℝ) (hL : 0 < L) (hs₀ : 0 < s₀) :
    depthPrimitive L s₀ 0 < 0 := by
  have he : Real.exp (-2*L*s₀) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith)
  unfold depthPrimitive
  simp only [mul_zero, Real.exp_zero]
  exact div_neg_of_neg_of_pos (sub_neg.mpr he) (by positivity)

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def depthFunction (L s₀ : ℝ) (t : E → ℝ) (x : E) : ℝ :=
  depthPrimitive L s₀ (t x)

noncomputable def depthDifferential (L : ℝ) (t : E → ℝ) (x : E) : E →L[ℝ] ℝ :=
  Real.exp (-2*L*t x) • fderiv ℝ t x

noncomputable def depthSecondDifferential (L : ℝ) (t : E → ℝ) (x : E)
    (T : E →L[ℝ] ℝ) (H : E →L[ℝ] (E →L[ℝ] ℝ)) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  Real.exp (-2*L*t x) • H + ((-2*L*Real.exp (-2*L*t x)) • T).smulRight T

theorem hasFDerivAt_depthFunction (L s₀ : ℝ) (t : E → ℝ) (x : E)
    (T : E →L[ℝ] ℝ) (hL : L ≠ 0) (ht : HasFDerivAt t T x) :
    HasFDerivAt (depthFunction L s₀ t) (Real.exp (-2*L*t x) • T) x := by
  exact (hasDerivAt_depthPrimitive L s₀ (t x) hL).comp_hasFDerivAt x ht

theorem fderiv_depthFunction (L s₀ : ℝ) (t : E → ℝ) (x : E)
    (hL : L ≠ 0) (ht : DifferentiableAt ℝ t x) :
    fderiv ℝ (depthFunction L s₀ t) x = depthDifferential L t x :=
  (hasFDerivAt_depthFunction L s₀ t x (fderiv ℝ t x) hL ht.hasFDerivAt).fderiv

theorem hasFDerivAt_depthDifferential (L : ℝ) (t : E → ℝ) (x : E)
    (T : E →L[ℝ] ℝ) (H : E →L[ℝ] (E →L[ℝ] ℝ))
    (ht : HasFDerivAt t T x) (hH : HasFDerivAt (fderiv ℝ t) H x) :
    HasFDerivAt (depthDifferential L t) (depthSecondDifferential L t x T H) x := by
  have ha := (ht.const_smul (-2*L)).exp
  have h := ha.smul hH
  rw [ht.fderiv] at h
  convert! h using 1 <;>
    simp only [depthDifferential, depthSecondDifferential, Pi.smul_apply,
      smul_eq_mul, smul_smul]
  congr 1
  ring

theorem hasFDerivAt_fderiv_depthFunction (L s₀ : ℝ) (t : E → ℝ) (x : E)
    (T : E →L[ℝ] ℝ) (H : E →L[ℝ] (E →L[ℝ] ℝ)) (hL : L ≠ 0)
    (ht : HasFDerivAt t T x) (hH : HasFDerivAt (fderiv ℝ t) H x)
    (hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ t y) :
    HasFDerivAt (fderiv ℝ (depthFunction L s₀ t))
      (depthSecondDifferential L t x T H) x := by
  apply (hasFDerivAt_depthDifferential L t x T H ht hH).congr_of_eventuallyEq
  filter_upwards [hnear] with y hy
  exact fderiv_depthFunction L s₀ t y hL hy

end Normed

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem coordinateHessian_depthFunction (L s₀ : ℝ) (t : E → ℝ) (x : E)
    (Q M : E →L[ℝ] E) (D : E →L[ℝ] (E →L[ℝ] E))
    (T : E →L[ℝ] ℝ) (H : E →L[ℝ] (E →L[ℝ] ℝ)) (hL : L ≠ 0)
    (ht : HasFDerivAt t T x) (hH : HasFDerivAt (fderiv ℝ t) H x)
    (hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ t y)
    (hQM : ∀ z, Q (M z) = z) (hMQ : ∀ z, M (Q z) = z)
    (hsym : ∀ X Y, inner ℝ (M X) Y = inner ℝ (M Y) X) (X Y : E) :
    coordinateHessian (depthFunction L s₀ t)
      (coordinateConnection ((Real.exp (-2*L*t x))⁻¹ • Q)
        (conformalMetricDerivative (Real.exp (-2*L*t x)) L M D T)) x X Y =
      Real.exp (-2*L*t x) *
        (coordinateHessian t (coordinateConnection Q D) x X Y -
          L*(T (metricGradient Q T))*inner ℝ (M X) Y) := by
  have hfirst := (hasFDerivAt_depthFunction L s₀ t x T hL ht).fderiv
  have hsecond := (hasFDerivAt_fderiv_depthFunction L s₀ t x T H hL ht hH hnear).fderiv
  have hΓ := coordinateConnection_conformal (Real.exp (-2*L*t x)) L Q M D T
    (Real.exp_ne_zero _) hQM hMQ hsym X Y
  unfold coordinateHessian
  rw [hfirst, hsecond, ht.fderiv, hH.fderiv, hΓ]
  simp only [depthSecondDifferential, conformalConnection, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_sub, map_add, map_smul, smul_eq_mul]
  ring

theorem conformal_depth_hessian_le (a L C c m A g q : ℝ)
    (ha : 0 ≤ a) (hL : 0 ≤ L) (hg : 0 ≤ g) (hA : A ≤ C*g)
    (hq : m ≤ q) (hchoice : C-L*m ≤ -c) :
    a*(A-L*q*g) ≤ -c*(a*g) := by
  have hm := mul_le_mul_of_nonneg_left hq hL
  have hmg := mul_le_mul_of_nonneg_right hm hg
  have hfirst : A-L*q*g ≤ (C-L*m)*g := by nlinarith
  have hsecond := mul_le_mul_of_nonneg_right hchoice hg
  have h := mul_le_mul_of_nonneg_left (hfirst.trans hsecond) ha
  convert h using 1 <;> ring

theorem exists_conformal_depth_parameter (C c m : ℝ)
    (hC : 0 ≤ C) (hc : 0 < c) (hm : 0 < m) :
    ∃ L : ℝ, 0 < L ∧ C-L*m = -c := by
  refine ⟨(C+c)/m, div_pos (by linarith) hm, ?_⟩
  field_simp
  ring

end Hilbert
#print axioms depthPrimitive_eq_integral
#print axioms hasFDerivAt_fderiv_depthFunction
#print axioms coordinateHessian_depthFunction
#print axioms conformal_depth_hessian_le
end OAI.AnisotropicCalderon.ConformalDepth
