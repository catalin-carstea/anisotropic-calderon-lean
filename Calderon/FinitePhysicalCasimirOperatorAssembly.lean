import Calderon.FinitePhysicalHarmonicPacketInclusion
import Calderon.PhysicalAdjointOperatorPairingPointDiagnostic

set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.RotationCasimirEstimate
open SphereHarmonic SmoothSphereRotationProjection
attribute [local irreducible] sphereSobolevSingleL sphereSobolevCoefficientL
  sphereSobolevZeroEquiv sphereSobolevInclusionL

lemma finite_physical_casimir_pairing_le_of_adjoint_operator_bounds
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (P Q : Fin 3 × Fin 3 → (SphereSobolev 1 →L[ℝ] SphereSobolev 0))
    (M0 Mstar : ℝ) (hM0 : 0 ≤ M0) (hMstar : 0 ≤ Mstar)
    (hP : ∀ ij, ‖P ij‖ ≤ M0) (hQ : ∀ ij, ‖Q ij‖ ≤ Mstar)
    (hDual : ∀ ij, ∀ f h : SphereSobolev 1,
      ⟪(sphereSobolevZeroEquiv hO hD).symm (P ij f),
        (sphereSobolevZeroEquiv hO hD).symm
          (sphereSobolevInclusionL 1 0 (by norm_num) h)⟫_ℝ =
      ⟪(sphereSobolevZeroEquiv hO hD).symm
          (sphereSobolevInclusionL 1 0 (by norm_num) f),
        (sphereSobolevZeroEquiv hO hD).symm (Q ij h)⟫_ℝ)
    (n m : ℕ) (u v : ∀ k, harmonicSphereSubspace k) :
    |(1/2:ℝ) * (∑ ij : Fin 3 × Fin 3, (
      ⟪(sphereSobolevZeroEquiv hO hD).symm
          (P ij (∑ k ∈ Finset.range n, sphereSobolevSingleL 1 k (u k))),
        (∑ k ∈ Finset.range m, (harmonicSphereRotation k ij.1 ij.2 (v k) : SphereL2))⟫_ℝ -
      ⟪(sphereSobolevZeroEquiv hO hD).symm
          (P ij (∑ k ∈ Finset.range n,
            sphereSobolevSingleL 1 k (harmonicSphereRotation k ij.1 ij.2 (u k)))),
        (∑ k ∈ Finset.range m, (v k : SphereL2))⟫_ℝ))| ≤
    3*Real.sqrt 2*(M0+Mstar) *
      Real.sqrt (∑ k ∈ Finset.range n, (1+(k:ℝ)*((k:ℝ)+1))*‖u k‖^2) *
      Real.sqrt (∑ k ∈ Finset.range m, (1+(k:ℝ)*((k:ℝ)+1))*‖v k‖^2) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "FINITE_OPERATOR_SECOND_ENTER"
    out.flush
  let Pu : SphereSobolev 1 := ∑ k ∈ Finset.range n, sphereSobolevSingleL 1 k (u k)
  let Pv : SphereSobolev 1 := ∑ k ∈ Finset.range m, sphereSobolevSingleL 1 k (v k)
  let Eu : ℝ := ∑ k ∈ Finset.range n, (1+(k:ℝ)*((k:ℝ)+1))*‖u k‖^2
  let Ev : ℝ := ∑ k ∈ Finset.range m, (1+(k:ℝ)*((k:ℝ)+1))*‖v k‖^2
  let U : ℝ := Real.sqrt Eu
  let V : ℝ := Real.sqrt Ev
  let A (ij : Fin 3 × Fin 3) : SphereL2 := (sphereSobolevZeroEquiv hO hD).symm (P ij Pu)
  let B (ij : Fin 3 × Fin 3) : SphereL2 := (sphereSobolevZeroEquiv hO hD).symm (Q ij Pv)
  let ru (ij : Fin 3 × Fin 3) : SphereL2 :=
    ∑ k ∈ Finset.range n, (harmonicSphereRotation k ij.1 ij.2 (u k) : SphereL2)
  let rv (ij : Fin 3 × Fin 3) : SphereL2 :=
    ∑ k ∈ Finset.range m, (harmonicSphereRotation k ij.1 ij.2 (v k) : SphereL2)
  have hEu : 0 ≤ Eu := by
    apply Finset.sum_nonneg
    intro k _
    positivity
  have hEv : 0 ≤ Ev := by
    apply Finset.sum_nonneg
    intro k _
    positivity
  have hU2 : U^2 = Eu := Real.sq_sqrt hEu
  have hV2 : V^2 = Ev := Real.sq_sqrt hEv
  have hSqrt2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hNorm (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (M : ℝ)
      (hM : 0 ≤ M) (hT : ‖T‖ ≤ M) (r : ℕ) (f : ∀ k, harmonicSphereSubspace k) :
      ‖(sphereSobolevZeroEquiv hO hD).symm
        (T (∑ k ∈ Finset.range r, sphereSobolevSingleL 1 k (f k)))‖ ≤
      2*M*Real.sqrt (∑ k ∈ Finset.range r, (1+(k:ℝ)*((k:ℝ)+1))*‖f k‖^2) := by
    calc
      _ = ‖T (∑ k ∈ Finset.range r, sphereSobolevSingleL 1 k (f k))‖ :=
        (sphereSobolevZeroEquiv hO hD).symm.norm_map _
      _ ≤ ‖T‖*‖∑ k ∈ Finset.range r, sphereSobolevSingleL 1 k (f k)‖ := T.le_opNorm _
      _ ≤ M*‖∑ k ∈ Finset.range r, sphereSobolevSingleL 1 k (f k)‖ :=
        mul_le_mul_of_nonneg_right hT (norm_nonneg _)
      _ ≤ M*(Real.sqrt 2*Real.sqrt
          (∑ k ∈ Finset.range r, (1+(k:ℝ)*((k:ℝ)+1))*‖f k‖^2)) :=
        mul_le_mul_of_nonneg_left
          (norm_finite_harmonic_packet_le_sqrt_two_casimir_energy r f) hM
      _ = Real.sqrt 2*(M*Real.sqrt
          (∑ k ∈ Finset.range r, (1+(k:ℝ)*((k:ℝ)+1))*‖f k‖^2)) := by ring
      _ ≤ 2*(M*Real.sqrt
          (∑ k ∈ Finset.range r, (1+(k:ℝ)*((k:ℝ)+1))*‖f k‖^2)) :=
        mul_le_mul_of_nonneg_right hSqrt2 (by positivity)
      _ = _ := by ring
  have hA : ∀ ij, ‖A ij‖ ≤ 2*M0*U := fun ij => hNorm (P ij) M0 hM0 (hP ij) n u
  have hB : ∀ ij, ‖B ij‖ ≤ 2*Mstar*V := fun ij => hNorm (Q ij) Mstar hMstar (hQ ij) m v
  have hRuEnergy : (∑ ij : Fin 3 × Fin 3, ‖ru ij‖^2) ≤ 2*Eu := by
    simpa only [ru, Eu, Fintype.sum_prod_type] using
      sum_norm_sq_finite_harmonic_rotation_packet_le_casimir_energy hO hD n u
  have hRvEnergy : (∑ ij : Fin 3 × Fin 3, ‖rv ij‖^2) ≤ 2*Ev := by
    simpa only [rv, Ev, Fintype.sum_prod_type] using
      sum_norm_sq_finite_harmonic_rotation_packet_le_casimir_energy hO hD m v
  have hru : (∑ ij : Fin 3 × Fin 3, ‖ru ij‖^2) ≤ 2*U^2 :=
    hRuEnergy.trans_eq (congrArg (fun r : ℝ => 2*r) hU2.symm)
  have hrv : (∑ ij : Fin 3 × Fin 3, ‖rv ij‖^2) ≤ 2*V^2 :=
    hRvEnergy.trans_eq (congrArg (fun r : ℝ => 2*r) hV2.symm)
  have hSecond (ij : Fin 3 × Fin 3) :
      ⟪(sphereSobolevZeroEquiv hO hD).symm
          (P ij (∑ k ∈ Finset.range n,
            sphereSobolevSingleL 1 k (harmonicSphereRotation k ij.1 ij.2 (u k)))),
        (∑ k ∈ Finset.range m, (v k : SphereL2))⟫_ℝ = ⟪ru ij,B ij⟫_ℝ := by
    let PR : SphereSobolev 1 := ∑ k ∈ Finset.range n,
      sphereSobolevSingleL 1 k (harmonicSphereRotation k ij.1 ij.2 (u k))
    have h := physical_adjoint_operator_pairing_apply_diagnostic hO hD P Q hDual ij PR Pv
    run_tac do
      let out ← IO.getStdout
      out.putStrLn "FINITE_OPERATOR_ADJOINT_POINT_APPLIED"
      out.flush
    rw [zeroEquiv_symm_inclusion_one_zero_finite_packet,
      zeroEquiv_symm_inclusion_one_zero_finite_packet] at h
    run_tac do
      let out ← IO.getStdout
      out.putStrLn "FINITE_OPERATOR_PHYSICAL_GRAPHS_TRANSPORTED"
      out.flush
    exact h
  have hForm : (1/2:ℝ) * (∑ ij : Fin 3 × Fin 3, (
      ⟪(sphereSobolevZeroEquiv hO hD).symm
          (P ij (∑ k ∈ Finset.range n, sphereSobolevSingleL 1 k (u k))),
        (∑ k ∈ Finset.range m, (harmonicSphereRotation k ij.1 ij.2 (v k) : SphereL2))⟫_ℝ -
      ⟪(sphereSobolevZeroEquiv hO hD).symm
          (P ij (∑ k ∈ Finset.range n,
            sphereSobolevSingleL 1 k (harmonicSphereRotation k ij.1 ij.2 (u k)))),
        (∑ k ∈ Finset.range m, (v k : SphereL2))⟫_ℝ)) =
      (1/2:ℝ) * (∑ ij : Fin 3 × Fin 3, (⟪A ij,rv ij⟫_ℝ - ⟪ru ij,B ij⟫_ℝ)) := by
    apply congrArg (fun r : ℝ => (1/2:ℝ)*r)
    apply Finset.sum_congr rfl
    intro ij _
    exact congrArg (fun r : ℝ => ⟪A ij,rv ij⟫_ℝ-r) (hSecond ij)
  exact (congrArg abs hForm).trans_le
    (abs_half_sum_nine_inner_sub_inner_le A B ru rv M0 Mstar U V hM0 hMstar
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hA hB hru hrv)

#print axioms OAI.AnisotropicCalderon.RotationCasimirEstimate.finite_physical_casimir_pairing_le_of_adjoint_operator_bounds
end OAI.AnisotropicCalderon.RotationCasimirEstimate
