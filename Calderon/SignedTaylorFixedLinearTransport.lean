import Calderon.SignedOperatorTaylorRemainder

/-! Necessary actual signed integral transport through fixed continuous linear maps. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

lemma secondTaylorRemainder_fixed_linear_map
    (F : ℝ → V) (L : V →L[ℝ] W) (r : ℝ)
    (hF : ∀ a ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ F (a*r)) :
    L (secondTaylorRemainder F r) = secondTaylorRemainder (fun x => L (F x)) r := by
  have hSecond (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
      deriv (deriv (fun x => L (F x))) (a*r) = L (deriv (deriv F) (a*r)) := by
    have hFa := hF a ha
    have hD : ContDiffAt ℝ ∞ (deriv F) (a*r) := hFa.derivWithin (by simp)
    have hNear : ∀ᶠ x in 𝓝 (a*r), DifferentiableAt ℝ F x := by
      filter_upwards [(hFa.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).eventually (by simp)] with x hx
      exact hx.differentiableAt (by norm_num)
    have hFirst : (deriv (fun x => L (F x))) =ᶠ[𝓝 (a*r)] (fun x => L (deriv F x)) := by
      filter_upwards [hNear] with x hx
      exact (L.hasFDerivAt.comp_hasDerivAt x hx.hasDerivAt).deriv
    exact hFirst.deriv_eq.trans
      (L.hasFDerivAt.comp_hasDerivAt (a*r) (hD.differentiableAt (by simp)).hasDerivAt).deriv
  have hContinuous : ContinuousOn (fun a : ℝ => (1-a) • deriv (deriv F) (a*r))
      (Icc (0 : ℝ) 1) := by
    intro a ha
    have hD : ContDiffAt ℝ ∞ (deriv F) (a*r) := (hF a ha).derivWithin (by simp)
    have hDD : ContDiffAt ℝ ∞ (deriv (deriv F)) (a*r) := hD.derivWithin (by simp)
    have hCurve : ContinuousAt (fun b : ℝ => b*r) a := continuousAt_id.mul_const r
    have hComp : ContinuousAt (fun b : ℝ => deriv (deriv F) (b*r)) a :=
      ContinuousAt.comp' (f := fun b : ℝ => b*r) (g := deriv (deriv F)) (x := a)
        hDD.continuousAt hCurve
    exact ((continuousAt_const.sub continuousAt_id).smul hComp).continuousWithinAt
  have hIntegrable : IntervalIntegrable
      (fun a : ℝ => (1-a) • deriv (deriv F) (a*r)) volume 0 1 :=
    ContinuousOn.intervalIntegrable
      (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hContinuous)
  change L (∫ a : ℝ in (0 : ℝ)..1, (1-a) • deriv (deriv F) (a*r)) =
    ∫ a : ℝ in (0 : ℝ)..1, (1-a) • deriv (deriv (fun x => L (F x))) (a*r)
  rw [← L.intervalIntegral_comp_comm hIntegrable]
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ha
  exact (L.map_smul (1-a) _).trans
    (congrArg (fun z : W => (1-a) • z) (hSecond a ha).symm)

lemma secondTaylorRemainder_eq_of_locallyEq_on_segment
    (F G : ℝ → V) (r : ℝ)
    (hEq : ∀ a ∈ Icc (0 : ℝ) 1, F =ᶠ[𝓝 (a*r)] G) :
    secondTaylorRemainder F r = secondTaylorRemainder G r := by
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ha
  exact congrArg (fun z : V => (1-a) • z) ((hEq a ha).deriv.deriv_eq)

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.secondTaylorRemainder_fixed_linear_map
#print axioms OAI.AnisotropicCalderon.ConnectionError.secondTaylorRemainder_eq_of_locallyEq_on_segment
