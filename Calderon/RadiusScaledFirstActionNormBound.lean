import Calderon.ActualHorizontalSobolevConnection
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

private lemma norm_four_terms_le {V : Type*} [SeminormedAddCommGroup V]
    (a b c d : V) : ‖a+b+c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
  have h1 := norm_add_le a b
  have h2 := norm_add_le (a+b) c
  have h3 := norm_add_le (a+b+c) d
  linarith only [h1,h2,h3]

theorem norm_radiusScaled_first_action_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (I Q J A Omega : V →L[ℝ] W) (Du : R3 →L[ℝ] V) (DR : R3 →L[ℝ] ℝ)
    (r : ℝ) (u : V) (e v : R3) (M : ℝ)
    (hM : 1 ≤ M) (hr : |r| ≤ M) (hu : ‖u‖ ≤ M) (hDu : ‖Du‖ ≤ M)
    (hDR : ‖DR‖ ≤ 1) (hQ : ‖Q‖ ≤ M) (hJ : ‖J‖ ≤ M) (hA : ‖A‖ ≤ M)
    (hOmega : ‖Omega‖ ≤ M) (he : ‖e‖ ≤ M) (hv : ‖v‖ ≤ M) :
    ‖r • (I (Du e)+Omega u) + Q u + r^2 • J u + DR v • A u‖ ≤
      M*(‖I‖*M*M+M*M)+M*M+M^2*M*M+M*M*M := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hDe : ‖Du e‖ ≤ M*M :=
    (Du.le_opNorm e).trans (mul_le_mul hDu he (norm_nonneg e) hM0)
  have hI : ‖I (Du e)‖ ≤ ‖I‖*(M*M) :=
    (I.le_opNorm _).trans (mul_le_mul_of_nonneg_left hDe (norm_nonneg I))
  have hO : ‖Omega u‖ ≤ M*M :=
    (Omega.le_opNorm u).trans (mul_le_mul hOmega hu (norm_nonneg u) hM0)
  have hH : ‖I (Du e)+Omega u‖ ≤ ‖I‖*M*M+M*M := by
    exact (norm_add_le _ _).trans (by simpa only [mul_assoc] using add_le_add hI hO)
  have hHorizontal : ‖r • (I (Du e)+Omega u)‖ ≤ M*(‖I‖*M*M+M*M) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hr hH (norm_nonneg _) hM0
  have hCoordinate : ‖Q u‖ ≤ M*M :=
    (Q.le_opNorm u).trans (mul_le_mul hQ hu (norm_nonneg u) hM0)
  have hJacobi : ‖r^2 • J u‖ ≤ M^2*M*M := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
    have hr2 : r^2 ≤ M^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg r) hr 2
    have hJu := (J.le_opNorm u).trans (mul_le_mul hJ hu (norm_nonneg u) hM0)
    exact (mul_le_mul hr2 hJu (norm_nonneg _) (sq_nonneg M)).trans_eq (mul_assoc _ _ _).symm
  have hDRv : |DR v| ≤ M := by
    simpa only [Real.norm_eq_abs,one_mul] using
      (DR.le_opNorm v).trans (mul_le_mul hDR hv (norm_nonneg v) zero_le_one)
  have hRadial : ‖DR v • A u‖ ≤ M*M*M := by
    rw [norm_smul,Real.norm_eq_abs]
    have hAu := (A.le_opNorm u).trans (mul_le_mul hA hu (norm_nonneg u) hM0)
    exact (mul_le_mul hDRv hAu (norm_nonneg _) hM0).trans_eq (mul_assoc _ _ _).symm
  exact (norm_four_terms_le _ _ _ _).trans
    (add_le_add (add_le_add (add_le_add hHorizontal hCoordinate) hJacobi) hRadial)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
