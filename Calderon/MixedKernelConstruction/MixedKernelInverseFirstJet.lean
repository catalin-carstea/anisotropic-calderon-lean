import Calderon.MixedKernelConstruction.MixedKernelInversePerturbation
import Mathlib.Analysis.Calculus.FDeriv.Mul
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError MetricOperator
open scoped ContDiff Topology

private instance actualOperator_scalarTower : IsScalarTower ℝ (R3 →L[ℝ] R3) (R3 →L[ℝ] R3) where
  smul_assoc a P Q := by
    apply ContinuousLinearMap.ext
    intro V
    rfl

private instance actualOperator_smulComm : SMulCommClass ℝ (R3 →L[ℝ] R3) (R3 →L[ℝ] R3) where
  smul_comm a P Q := by
    apply ContinuousLinearMap.ext
    intro V
    change a • P (Q V)=P (a • Q V)
    rw [map_smul]

/-- Differentiate the genuine inverse in the actual operator ring. -/
theorem fderiv_actual_operator_inverse_apply
    (P : R3 → R3 →L[ℝ] R3) (x U : R3)
    (hP : DifferentiableAt ℝ P x) (hUnit : IsUnit (P x)) :
    fderiv ℝ (fun Y => Ring.inverse (P Y)) x U =
      -(Ring.inverse (P x) * fderiv ℝ P x U * Ring.inverse (P x)) := by
  obtain ⟨u,hu⟩ := hUnit
  have hInv : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (R3 →L[ℝ] R3)
        (Ring.inverse (P x)) (Ring.inverse (P x))) (P x) := by
    rw [← hu,Ring.inverse_unit]
    exact hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have hChain := (hInv.comp x hP.hasFDerivAt).fderiv
  simp only [Function.comp_def] at hChain
  rw [hChain]
  rfl

/-- Ordered telescope for two inverse derivatives; no commutation is used. -/
theorem inverse_first_jet_telescope
    (M M0 D D0 : R3 →L[ℝ] R3) :
    M*D*M-M0*D0*M0 =
      (M-M0)*D*M+M0*(D-D0)*M+M0*D0*(M-M0) := by
  apply ContinuousLinearMap.ext
  intro U
  change M (D (M U))-M0 (D0 (M0 U))=
    (M-M0) (D (M U))+M0 ((D-D0) (M U))+M0 (D0 ((M-M0) U))
  simp only [ContinuousLinearMap.sub_apply,map_sub]
  abel

/-- Genuine inverse first derivatives retain a uniform quantitative perturbation bound. -/
theorem inverse_first_jet_perturbation_bounds
    (P P0 : R3 → R3 →L[ℝ] R3) (x : R3)
    (hP : DifferentiableAt ℝ P x) (hP0 : DifferentiableAt ℝ P0 x)
    (hUnit : IsUnit (P x)) (hUnit0 : IsUnit (P0 x)) (K d : ℝ)
    (hK : 0 ≤ K) (hInv0 : ‖Ring.inverse (P0 x)‖ ≤ K)
    (hD0 : ‖fderiv ℝ P0 x‖ ≤ K)
    (hValue : ‖P x-P0 x‖ ≤ d)
    (hJet : ‖fderiv ℝ P x-fderiv ℝ P0 x‖ ≤ d)
    (hd : d ≤ 1) (hSmall : K*d ≤ 1/2) :
    ‖fderiv ℝ (fun Y => Ring.inverse (P Y)) x‖ ≤ 4*K^2*(K+1) ∧
    ‖fderiv ℝ (fun Y => Ring.inverse (P Y)) x-
      fderiv ℝ (fun Y => Ring.inverse (P0 Y)) x‖ ≤ (6*K^4+4*K^3+2*K^2)*d := by
  let M := Ring.inverse (P x)
  let M0 := Ring.inverse (P0 x)
  let D := fderiv ℝ P x
  let D0 := fderiv ℝ P0 x
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hValue
  obtain ⟨hM,hDiff⟩ := ring_inverse_perturbation_bounds (P x) (P0 x) hUnit hUnit0 K d hK hInv0 hValue hSmall
  have hD : ‖D‖ ≤ K+1 := by
    have ht := norm_add_le (D-D0) D0
    have he : D-D0+D0=D := sub_add_cancel D D0
    rw [he] at ht
    exact ht.trans (by linarith only [hJet,hD0,hd])
  have hDM (U : R3) : ‖D U‖ ≤ (K+1)*‖U‖ :=
    (D.le_opNorm U).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg U))
  have hD0U (U : R3) : ‖D0 U‖ ≤ K*‖U‖ :=
    (D0.le_opNorm U).trans (mul_le_mul_of_nonneg_right hD0 (norm_nonneg U))
  have hDeltaU (U : R3) : ‖D U-D0 U‖ ≤ d*‖U‖ :=
    ((D-D0).le_opNorm U).trans (mul_le_mul_of_nonneg_right hJet (norm_nonneg U))
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro U
    rw [fderiv_actual_operator_inverse_apply P x U hP hUnit,norm_neg]
    calc
      ‖M*D U*M‖ ≤ ‖M‖*‖D U‖*‖M‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg M))
      _ ≤ (2*K)*((K+1)*‖U‖)*(2*K) := by gcongr;exact hDM U
      _ = (4*K^2*(K+1))*‖U‖ := by ring
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro U
    simp only [ContinuousLinearMap.sub_apply]
    rw [fderiv_actual_operator_inverse_apply P x U hP hUnit,
      fderiv_actual_operator_inverse_apply P0 x U hP0 hUnit0]
    change ‖-(M*D U*M)- -(M0*D0 U*M0)‖ ≤ _
    have heq : -(M*D U*M)- -(M0*D0 U*M0) = -(M*D U*M-M0*D0 U*M0) := by abel
    rw [heq,norm_neg]
    rw [inverse_first_jet_telescope]
    have h1 : ‖(M-M0)*D U*M‖ ≤ (4*K^3*(K+1)*d)*‖U‖ := by
      calc
        ‖(M-M0)*D U*M‖ ≤ ‖M-M0‖*‖D U‖*‖M‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg M))
        _ ≤ (2*K^2*d)*((K+1)*‖U‖)*(2*K) := by gcongr;exact hDM U
        _ = (4*K^3*(K+1)*d)*‖U‖ := by ring
    have h2 : ‖M0*(D U-D0 U)*M‖ ≤ (2*K^2*d)*‖U‖ := by
      calc
        ‖M0*(D U-D0 U)*M‖ ≤ ‖M0‖*‖D U-D0 U‖*‖M‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg M))
        _ ≤ K*(d*‖U‖)*(2*K) := by gcongr;exact hDeltaU U
        _ = (2*K^2*d)*‖U‖ := by ring
    have h3 : ‖M0*D0 U*(M-M0)‖ ≤ (2*K^4*d)*‖U‖ := by
      calc
        ‖M0*D0 U*(M-M0)‖ ≤ ‖M0‖*‖D0 U‖*‖M-M0‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg (M-M0)))
        _ ≤ K*(K*‖U‖)*(2*K^2*d) := by gcongr;exact hD0U U
        _ = (2*K^4*d)*‖U‖ := by ring
    calc
      ‖(M-M0)*D U*M+M0*(D U-D0 U)*M+M0*D0 U*(M-M0)‖ ≤
          ‖(M-M0)*D U*M‖+‖M0*(D U-D0 U)*M‖+‖M0*D0 U*(M-M0)‖ :=
        (norm_add_le ((M-M0)*D U*M+M0*(D U-D0 U)*M) (M0*D0 U*(M-M0))).trans
          (add_le_add (norm_add_le ((M-M0)*D U*M) (M0*(D U-D0 U)*M)) le_rfl)
      _ ≤ (4*K^3*(K+1)*d)*‖U‖+(2*K^2*d)*‖U‖+(2*K^4*d)*‖U‖ := add_le_add (add_le_add h1 h2) h3
      _ = ((6*K^4+4*K^3+2*K^2)*d)*‖U‖ := by ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
