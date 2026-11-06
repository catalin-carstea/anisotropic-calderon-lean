import Calderon.LocalRadialDerivative
import Mathlib.Analysis.Calculus.ContDiff.Basic
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
/-! Full upfront: EXPANSION-v001.json. Exact local radial curve jets,
connecting selected Taylor derivatives to full-joint actual operator jets. -/
variable {Q P V : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma deriv_joint_radialSlice_eq_jet_one
    (F : Q × (P × ℝ) → V) (q : Q) (y : P) (r : ℝ)
    (hF : DifferentiableAt ℝ F (q,(y,r))) :
    deriv (fun t : ℝ => F (q,(y,t))) r =
      iteratedFDeriv ℝ 1 F (q,(y,r)) (fun _ => (0,(0,1))) := by
  have hc : HasDerivAt (fun t : ℝ => (q,(y,t))) (0,(0,1)) r :=
    (hasDerivAt_const r q).prodMk ((hasDerivAt_const r y).prodMk (hasDerivAt_id r))
  have hd := (hF.hasFDerivAt.comp_hasDerivAt r hc).deriv
  simpa only [Function.comp_def,iteratedFDeriv_one_apply] using hd

lemma deriv_deriv_joint_radialSlice_eq_jet_two
    (F : Q × (P × ℝ) → V) (q : Q) (y : P) (r : ℝ)
    (hF : ContDiffAt ℝ ∞ F (q,(y,r))) :
    deriv (deriv (fun t : ℝ => F (q,(y,t)))) r =
      iteratedFDeriv ℝ 2 F (q,(y,r)) (fun _ => (0,(0,1))) := by
  let e : Q × (P × ℝ) := (0,(0,1))
  have hNearby : ∀ᶠ p in 𝓝 (q,(y,r)), DifferentiableAt ℝ F p := by
    filter_upwards [(hF.of_le (show (1:ℕ∞ω) ≤ (∞:ℕ∞ω) by simp)).eventually (by simp)] with p hp
    exact hp.differentiableAt (by norm_num)
  have hNearSlice := (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt.eventually hNearby
  have hEq : deriv (fun t : ℝ => F (q,(y,t))) =ᶠ[𝓝 r]
      (fun t : ℝ => fderiv ℝ F (q,(y,t)) e) := by
    filter_upwards [hNearSlice] with t ht
    simpa only [iteratedFDeriv_one_apply] using deriv_joint_radialSlice_eq_jet_one F q y t ht
  have hc : HasDerivAt (fun t : ℝ => (q,(y,t))) e r :=
    (hasDerivAt_const r q).prodMk ((hasDerivAt_const r y).prodMk (hasDerivAt_id r))
  have hFDsmooth : ContDiffAt ℝ ∞ (fderiv ℝ F) (q,(y,r)) := hF.fderiv_right (by simp)
  have hFD : DifferentiableAt ℝ (fderiv ℝ F) (q,(y,r)) :=
    hFDsmooth.differentiableAt (by simp)
  have hD := hFD.hasFDerivAt.comp_hasDerivAt r hc
  have hEval := ((ContinuousLinearMap.apply ℝ V e).hasFDerivAt.comp_hasDerivAt r hD).deriv
  rw [hEq.deriv_eq]
  simpa only [Function.comp_def,ContinuousLinearMap.apply_apply,iteratedFDeriv_two_apply] using hEval

lemma radialFirstDerivative_jointSlice_eq_jet_one
    (F : Q × (P × ℝ) → V) (q : Q) (y : P) (r : ℝ)
    (hF : DifferentiableAt ℝ F (q,(y,r))) :
    radialFirstDerivative (fun p : P × ℝ => F (q,p)) (y,r) =
      iteratedFDeriv ℝ 1 F (q,(y,r)) (fun _ => (0,(0,1))) := by
  have hCurve : DifferentiableAt ℝ (fun p : P × ℝ => (q,p)) (y,r) := by fun_prop
  have hS : DifferentiableAt ℝ (fun p : P × ℝ => F (q,p)) (y,r) :=
    hF.comp (y,r) hCurve
  exact (deriv_radialSlice_of_differentiableAt (fun p : P × ℝ => F (q,p)) y r hS).symm.trans
    (deriv_joint_radialSlice_eq_jet_one F q y r hF)

#print axioms OAI.AnisotropicCalderon.ConnectionError.deriv_joint_radialSlice_eq_jet_one
#print axioms OAI.AnisotropicCalderon.ConnectionError.deriv_deriv_joint_radialSlice_eq_jet_two
#print axioms OAI.AnisotropicCalderon.ConnectionError.radialFirstDerivative_jointSlice_eq_jet_one
end OAI.AnisotropicCalderon.ConnectionError
