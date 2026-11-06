import Calderon.DenseRealLinearExtension
import Calderon.SignedOperatorTaylorRemainder
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DenseOperatorTaylorCompletion
open ConnectionError
/-! Generic dense input completion seams; their bounds are hypotheses supplied by the
caller. -/
variable {E G V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

lemma exists_dense_operator_extension_of_input_bound
    (I : E →L[ℝ] G) (hd : DenseRange I) (T : E →L[ℝ] V)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ u, ‖T u‖ ≤ M*‖I u‖) :
    ∃ S : G →L[ℝ] V, ‖S‖ ≤ M ∧ ∀ u, S (I u) = T u := by
  let S : G →L[ℝ] V := T.toLinearMap.extendOfNorm I.toLinearMap
  have hGraph (u : E) : S (I u) = T u :=
    DenseRealLinearExtension.extendOfNorm_apply_dense T.toLinearMap I.toLinearMap hd M hb u
  have hNorm (u : G) : ‖S u‖ ≤ M*‖u‖ :=
    DenseRealLinearExtension.norm_extendOfNorm_apply_dense T.toLinearMap I.toLinearMap hd M hb u
  exact ⟨S,S.opNorm_le_bound hM hNorm,hGraph⟩

lemma dense_operator_extension_unique
    (I : E →L[ℝ] G) (hd : DenseRange I) (S T : G →L[ℝ] V)
    (h : ∀ u, S (I u) = T (I u)) : S = T := by
  have hFunction : (S : G → V) = (T : G → V) :=
    hd.equalizer S.continuous T.continuous (funext h)
  ext u
  exact congr_fun hFunction u

lemma dense_operator_extension_taylor_identity
    (I : E →L[ℝ] G) (hd : DenseRange I)
    (T T0 D R : E →L[ℝ] V) (S S0 A B : G →L[ℝ] V) (r : ℝ)
    (hS : ∀ u, S (I u) = T u) (hS0 : ∀ u, S0 (I u) = T0 u)
    (hA : ∀ u, A (I u) = D u) (hB : ∀ u, B (I u) = R u)
    (hTaylor : T = T0 + r • D + r^2 • R) :
    S = S0 + r • A + r^2 • B := by
  apply dense_operator_extension_unique I hd
  intro u
  calc
    S (I u) = T u := hS u
    _ = T0 u + r • D u + r^2 • R u := by
      exact (congrArg (fun J : E →L[ℝ] V => J u) hTaylor).trans (by rfl)
    _ = (S0 + r • A + r^2 • B) (I u) := by
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,hS0,hA,hB]

lemma norm_input_secondTaylorRemainder_le
    (I : E →L[ℝ] G) (F : ℝ → E →L[ℝ] V) (r M : ℝ)
    (hF : ∀ t ∈ Icc (0:ℝ) 1, ContDiffAt ℝ ∞ F (t*r))
    (hDD : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, ‖(deriv (deriv F) (t*r)) u‖ ≤ M*‖I u‖)
    (u : E) : ‖(secondTaylorRemainder F r) u‖ ≤ (M/2)*‖I u‖ := by
  let ev : (E →L[ℝ] V) →L[ℝ] V := ContinuousLinearMap.apply ℝ V u
  have hContinuous : ContinuousOn (fun t : ℝ => (1-t) • deriv (deriv F) (t*r)) (Icc (0:ℝ) 1) := by
    intro t ht
    have hD : ContDiffAt ℝ ∞ (deriv F) (t*r) := (hF t ht).derivWithin (by simp)
    have hDDiff : ContDiffAt ℝ ∞ (deriv (deriv F)) (t*r) := hD.derivWithin (by simp)
    have hCurve : ContinuousAt (fun s : ℝ => s*r) t := continuousAt_id.mul_const r
    have hDDCurve : ContinuousAt (fun s : ℝ => deriv (deriv F) (s*r)) t :=
      ContinuousAt.comp' (f := fun s : ℝ => s*r) (g := deriv (deriv F)) (x := t) hDDiff.continuousAt hCurve
    have hWeight : ContinuousAt (fun s : ℝ => 1-s) t := continuousAt_const.sub continuousAt_id
    exact (hWeight.smul hDDCurve).continuousWithinAt
  have hIntegrable : IntervalIntegrable (fun t : ℝ => (1-t) • deriv (deriv F) (t*r)) volume 0 1 :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hContinuous)
  have hMap := ev.intervalIntegral_comp_comm hIntegrable
  have hEstimate : ‖∫ t : ℝ in (0:ℝ)..1, ev ((1-t) • deriv (deriv F) (t*r))‖ ≤
      ∫ t : ℝ in (0:ℝ)..1, (1-t)*(M*‖I u‖) := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · filter_upwards [] with t ht
      rw [ev.map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht.2)]
      exact mul_le_mul_of_nonneg_left (hDD t ⟨ht.1.le,ht.2⟩ u) (sub_nonneg.mpr ht.2)
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hInt : (∫ t : ℝ in (0:ℝ)..1, (1-t)*(M*‖I u‖)) = (M/2)*‖I u‖ := by
    rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_sub
      (f := fun _ : ℝ => (1:ℝ)) (g := fun t : ℝ => t)
      intervalIntegrable_const (Continuous.intervalIntegrable continuous_id _ _),integral_one,integral_id]
    ring
  change ‖ev (∫ t : ℝ in (0:ℝ)..1, (1-t) • deriv (deriv F) (t*r))‖ ≤ _
  exact (congrArg norm hMap).symm.trans_le (hEstimate.trans_eq hInt)

#print axioms OAI.AnisotropicCalderon.DenseOperatorTaylorCompletion.exists_dense_operator_extension_of_input_bound
#print axioms OAI.AnisotropicCalderon.DenseOperatorTaylorCompletion.dense_operator_extension_unique
#print axioms OAI.AnisotropicCalderon.DenseOperatorTaylorCompletion.dense_operator_extension_taylor_identity
#print axioms OAI.AnisotropicCalderon.DenseOperatorTaylorCompletion.norm_input_secondTaylorRemainder_le
end OAI.AnisotropicCalderon.DenseOperatorTaylorCompletion
