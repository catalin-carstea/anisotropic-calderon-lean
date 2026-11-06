import Calderon.DenseOperatorSignedTaylorCompletion
import Calderon.DenseOperatorHighJetTransport
import Calderon.JointRadialSliceJetTransport
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DenseOperatorTaylorGraph
open ConnectionError DenseOperatorTaylorCompletion DenseOperatorJetTransport
/-! Exact canonical and signed radial graph transport. -/
variable {Q P E G V : Type*}
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

lemma extendOfNorm_eq_of_dense_operator_graph
    (I : E →L[ℝ] G) (hd : DenseRange I) (T : E →L[ℝ] V) (S : G →L[ℝ] V)
    (hGraph : ∀ u, S (I u) = T u) :
    T.toLinearMap.extendOfNorm I.toLinearMap = S := by
  have hBound (u : E) : ‖T u‖ ≤ ‖S‖*‖I u‖ :=
    (congrArg norm (hGraph u)).symm.trans_le (S.le_opNorm (I u))
  apply dense_operator_extension_unique I hd
  intro u
  exact (DenseRealLinearExtension.extendOfNorm_apply_dense T.toLinearMap I.toLinearMap
    hd ‖S‖ hBound u).trans (hGraph u).symm

lemma deriv_operator_radial_high_graph
    (Ω : Set (Q × (P × ℝ))) (hΩ : IsOpen Ω)
    (I : E →L[ℝ] G) (S : Q × (P × ℝ) → G →L[ℝ] V)
    (T : Q × (P × ℝ) → E →L[ℝ] V)
    (hIdentity : ∀ p ∈ Ω, (S p).comp I = T p)
    (q : Q) (y : P) (r : ℝ) (hp : (q,(y,r)) ∈ Ω)
    (hS : ContDiffAt ℝ ∞ S (q,(y,r))) (hT : ContDiffAt ℝ ∞ T (q,(y,r))) :
    (deriv (fun t : ℝ => S (q,(y,t))) r).comp I =
      deriv (fun t : ℝ => T (q,(y,t))) r := by
  let PreI : (G →L[ℝ] V) →L[ℝ] (E →L[ℝ] V) :=
    (ContinuousLinearMap.compL ℝ E G V).flip I
  have hJet := iteratedFDeriv_operator_high_graph Ω hΩ (q,(y,r)) hp I S T hS hT
    hIdentity 1 (fun _ => (0,(0,1)))
  have hLeft := deriv_joint_radialSlice_eq_jet_one S q y r (hS.differentiableAt (by simp))
  have hRight := deriv_joint_radialSlice_eq_jet_one T q y r (hT.differentiableAt (by simp))
  exact (congrArg PreI hLeft).trans (hJet.trans hRight.symm)

lemma secondTaylorRemainder_operator_radial_high_graph
    (Ω : Set (Q × (P × ℝ))) (hΩ : IsOpen Ω)
    (I : E →L[ℝ] G) (S : Q × (P × ℝ) → G →L[ℝ] V)
    (T : Q × (P × ℝ) → E →L[ℝ] V)
    (hIdentity : ∀ p ∈ Ω, (S p).comp I = T p)
    (hS : ∀ p ∈ Ω, ContDiffAt ℝ ∞ S p)
    (hT : ∀ p ∈ Ω, ContDiffAt ℝ ∞ T p)
    (q : Q) (y : P) (r : ℝ)
    (hSegment : ∀ t ∈ Icc (0:ℝ) 1, (q,(y,t*r)) ∈ Ω) :
    (secondTaylorRemainder (fun t : ℝ => S (q,(y,t))) r).comp I =
      secondTaylorRemainder (fun t : ℝ => T (q,(y,t))) r := by
  let PreI : (G →L[ℝ] V) →L[ℝ] (E →L[ℝ] V) :=
    (ContinuousLinearMap.compL ℝ E G V).flip I
  let s : ℝ → G →L[ℝ] V := fun t => S (q,(y,t))
  let tRaw : ℝ → E →L[ℝ] V := fun t => T (q,(y,t))
  have hSecond (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) :
      PreI (deriv (deriv s) (a*r)) = deriv (deriv tRaw) (a*r) := by
    have hp := hSegment a ha
    have hJet := iteratedFDeriv_operator_high_graph Ω hΩ (q,(y,a*r)) hp I S T
      (hS _ hp) (hT _ hp) hIdentity 2 (fun _ => (0,(0,1)))
    have hLeft := deriv_deriv_joint_radialSlice_eq_jet_two S q y (a*r) (hS _ hp)
    have hRight := deriv_deriv_joint_radialSlice_eq_jet_two T q y (a*r) (hT _ hp)
    exact (congrArg PreI hLeft).trans (hJet.trans hRight.symm)
  have hSlice (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ s (a*r) :=
    (hS _ (hSegment a ha)).comp (a*r)
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hContinuous : ContinuousOn (fun a : ℝ => (1-a) • deriv (deriv s) (a*r))
      (Icc (0:ℝ) 1) := by
    intro a ha
    have hD : ContDiffAt ℝ ∞ (deriv s) (a*r) := (hSlice a ha).derivWithin (by simp)
    have hDD : ContDiffAt ℝ ∞ (deriv (deriv s)) (a*r) := hD.derivWithin (by simp)
    have hCurve : ContinuousAt (fun b : ℝ => b*r) a := continuousAt_id.mul_const r
    have hDDCurve : ContinuousAt (fun b : ℝ => deriv (deriv s) (b*r)) a :=
      ContinuousAt.comp' (f := fun b : ℝ => b*r) (g := deriv (deriv s)) (x := a)
        hDD.continuousAt hCurve
    exact ((continuousAt_const.sub continuousAt_id).smul hDDCurve).continuousWithinAt
  have hIntegrable : IntervalIntegrable
      (fun a : ℝ => (1-a) • deriv (deriv s) (a*r)) volume 0 1 :=
    ContinuousOn.intervalIntegrable
      (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hContinuous)
  change PreI (∫ a : ℝ in (0:ℝ)..1, (1-a) • deriv (deriv s) (a*r)) =
    ∫ a : ℝ in (0:ℝ)..1, (1-a) • deriv (deriv tRaw) (a*r)
  rw [← PreI.intervalIntegral_comp_comm hIntegrable]
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ha
  exact (PreI.map_smul (1-a) _).trans
    (congrArg (fun z : E →L[ℝ] V => (1-a) • z) (hSecond a ha))

#print axioms OAI.AnisotropicCalderon.DenseOperatorTaylorGraph.extendOfNorm_eq_of_dense_operator_graph
#print axioms OAI.AnisotropicCalderon.DenseOperatorTaylorGraph.deriv_operator_radial_high_graph
#print axioms OAI.AnisotropicCalderon.DenseOperatorTaylorGraph.secondTaylorRemainder_operator_radial_high_graph
end OAI.AnisotropicCalderon.DenseOperatorTaylorGraph
