import Calderon.SphereSobolevFiniteDegreeDualForm
import Calderon.SphereSobolevFinitePhysicalHalfDualPackets
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
/-! The finite dual-pair bound, factored out of the pointwise theorem. -/
attribute [local irreducible] sphereSobolevSingleL sphereSobolevCoefficientL sphereSobolevInclusionL

lemma finite_half_dual_degree_pair_bound_of_decoded_form_bound
    (T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (K : ∀ m n : ℕ, harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m)
    (hCoefficients : ∀ m n : ℕ, ∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (T (sphereSobolevSingleL (3/2:ℝ) n z)) = ((m:ℝ)-(n:ℝ)) • K m n z)
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ ncut : ℕ, ∀ u v : ∀ l, harmonicSphereSubspace l,
      |∑ m ∈ Finset.range ncut, ∑ n ∈ Finset.range ncut, ((m:ℝ)-(n:ℝ))*⟪K m n (u n),v m⟫_ℝ| ≤
        M*Real.sqrt (∑ l ∈ Finset.range ncut, (1+(l:ℝ))*‖u l‖^2)*Real.sqrt (∑ l ∈ Finset.range ncut, (1+(l:ℝ))*‖v l‖^2)) :
    ∀ u ∈ sphereSobolevFiniteSupport (3/2:ℝ),
      ∀ v ∈ sphereSobolevFiniteSupport (1/2:ℝ), |sphereSobolevDualPairing (1/2:ℝ) v (T u)| ≤ M*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u‖*‖v‖ := by
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_FINITE_ENTER"; out.flush
  intro u hu v hv
  obtain ⟨nu,hnu⟩ := hu
  obtain ⟨nv,hnv⟩ := hv
  let ncut := max nu nv
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_SUPPORTS_OBTAINED"; out.flush
  have hU (k : ℕ) (hk : ncut ≤ k) : sphereSobolevCoefficientL (3/2:ℝ) k u = 0 := hnu k ((le_max_left nu nv).trans hk)
  have hV (k : ℕ) (hk : ncut ≤ k) : sphereSobolevCoefficientL (1/2:ℝ) k v = 0 := hnv k ((le_max_right nu nv).trans hk)
  have hI (k : ℕ) (hk : ncut ≤ k) : sphereSobolevCoefficientL (1/2:ℝ) k (I u) = 0 :=
    (sphereSobolevCoefficientL_inclusion (3/2:ℝ) (1/2:ℝ) (by norm_num) u k).trans (hU k hk)
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_INCLUSION_SUPPORT_READY"; out.flush
  have hNormU := sqrt_half_finite_decoded_eq_norm ncut (I u) hI
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_HALF_INPUT_NORM_READY"; out.flush
  have hInputNorm : Real.sqrt (∑ k ∈ Finset.range ncut, (1+(k:ℝ))*‖sphereSobolevCoefficientL (3/2:ℝ) k u‖^2) = ‖I u‖ := by
    simpa only [I,sphereSobolevCoefficientL_inclusion] using hNormU
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_DECODED_INPUT_BUDGET_READY"; out.flush
  have hTestNorm := sqrt_half_finite_decoded_eq_norm ncut v hV
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_TEST_NORM_READY"; out.flush
  have hDegree := hBound ncut (fun n => sphereSobolevCoefficientL (3/2:ℝ) n u) (fun m => sphereSobolevCoefficientL (1/2:ℝ) m v)
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_DEGREE_BOUND_READY"; out.flush
  rw [hInputNorm,hTestNorm] at hDegree
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_BOUND_NORMS_TRANSPORTED"; out.flush
  exact (congrArg abs (sphereSobolev_finite_half_dual_degree_form_of_coefficients T K hCoefficients ncut u v hU hV)).trans_le hDegree

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.finite_half_dual_degree_pair_bound_of_decoded_form_bound
end OAI.AnisotropicCalderon.SphereHarmonic
