import Calderon.JointRadialSliceJetTransport
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError

lemma contDiffOn_deriv_joint_radialSlice
    {Q P V : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : Q × (P × ℝ) → V) (Ω : Set (Q × (P × ℝ)))
    (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ ∞ F Ω) :
    ContDiffOn ℝ ∞
      (fun z : Q × (P × ℝ) => deriv (fun t : ℝ => F (z.1,(z.2.1,t))) z.2.2) Ω := by
  have hFD : ContDiffOn ℝ ∞ (fderiv ℝ F) Ω :=
    hF.fderiv_of_isOpen hΩ (by simp)
  have hEval : ContDiffOn ℝ ∞
      (fun z : Q × (P × ℝ) => fderiv ℝ F z (0,(0,1))) Ω :=
    hFD.clm_apply contDiffOn_const
  apply hEval.congr
  intro z hz
  simpa only [iteratedFDeriv_one_apply] using
    deriv_joint_radialSlice_eq_jet_one F z.1 z.2.1 z.2.2
      ((hF.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp))

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiffOn_deriv_joint_radialSlice
