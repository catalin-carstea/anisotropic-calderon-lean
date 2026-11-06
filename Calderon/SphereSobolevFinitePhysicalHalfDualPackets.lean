import Calderon.SphereSobolevPairing
import Calderon.ActualFiniteSobolevCasimirEnergyBridge
set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph
/-! Literal physical dual coefficients,
actual weighted packets and half norm, complete unrestricted outputs. -/
lemma sphereSobolevDualPairing_single_left_physical
    (s : ℝ) (k : ℕ) (z : harmonicSphereSubspace k) (f : SphereSobolev (-s)) :
    sphereSobolevDualPairing s (sphereSobolevSingleL s k z) f =
      ⟪sphereSobolevCoefficientL (-s) k f,z⟫_ℝ := by
  change ⟪besselWeight s k • lp.single (E := fun j => harmonicSphereSubspace j) 2 k z,f⟫_ℝ =
    ⟪besselWeight (-(-s)) k • f k,z⟫_ℝ
  rw [neg_neg]
  calc
    _ = ⟪f,besselWeight s k • lp.single (E := fun j => harmonicSphereSubspace j) 2 k z⟫_ℝ := real_inner_comm _ _
    _ = besselWeight s k * ⟪f,lp.single (E := fun j => harmonicSphereSubspace j) 2 k z⟫_ℝ :=
      real_inner_smul_right _ _ _
    _ = besselWeight s k * ⟪f k,z⟫_ℝ :=
      congrArg (fun r : ℝ => besselWeight s k*r) (lp.inner_single_right (𝕜 := ℝ) k z f)
    _ = _ := (real_inner_smul_left (f k) z (besselWeight s k)).symm

lemma sphereSobolevDualPairing_finite_left_physical
    (s : ℝ) (S : Finset ℕ) (z : ∀ k, harmonicSphereSubspace k) (f : SphereSobolev (-s)) :
    sphereSobolevDualPairing s (∑ k ∈ S, sphereSobolevSingleL s k (z k)) f =
      ∑ k ∈ S, ⟪sphereSobolevCoefficientL (-s) k f,z k⟫_ℝ := by
  change ⟪∑ k ∈ S, sphereSobolevSingleL s k (z k),f⟫_ℝ = _
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro k _
  exact sphereSobolevDualPairing_single_left_physical s k (z k) f

lemma sphereSobolev_eq_physical_packet_of_finiteSupport
    (s : ℝ) (ncut : ℕ) (u : SphereSobolev s)
    (hu : ∀ k, ncut ≤ k → sphereSobolevCoefficientL s k u = 0) :
    u = ∑ k ∈ Finset.range ncut, sphereSobolevSingleL s k (sphereSobolevCoefficientL s k u) := by
  change u = sphereSobolevPartialSum s ncut u
  apply sphereSobolev_ext s
  intro k
  rw [sphereSobolevCoefficientL_partialSum]
  by_cases hk : k < ncut
  · rw [if_pos hk]
  · rw [if_neg hk]
    exact hu k (Nat.le_of_not_lt hk)

lemma sqrt_half_finite_decoded_eq_norm
    (ncut : ℕ) (u : SphereSobolev (1/2:ℝ))
    (hu : ∀ k, ncut ≤ k → sphereSobolevCoefficientL (1/2:ℝ) k u = 0) :
    Real.sqrt (∑ k ∈ Finset.range ncut, (1+(k:ℝ))*‖sphereSobolevCoefficientL (1/2:ℝ) k u‖^2) = ‖u‖ := by
  have hNorm := norm_sq_sphereSobolev_finite_decoded (1/2:ℝ) ncut u hu
  simp only [besselWeight_half_square] at hNorm
  rw [← hNorm,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg u)]
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_single_left_physical
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_finite_left_physical
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolev_eq_physical_packet_of_finiteSupport
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sqrt_half_finite_decoded_eq_norm
end OAI.AnisotropicCalderon.SphereHarmonic
