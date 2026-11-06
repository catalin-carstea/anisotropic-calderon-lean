import Calderon.SphereSobolevPairing
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph

def sphereSobolevDualRieszL (s : ℝ) :
    StrongDual ℝ (SphereSobolev s) →L[ℝ] SphereSobolev (-s) :=
  (InnerProductSpace.toDual ℝ (SphereSobolev s)).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma sphereSobolevDualPairing_dualRiesz (s : ℝ)
    (ell : StrongDual ℝ (SphereSobolev s)) (u : SphereSobolev s) :
    sphereSobolevDualPairing s u (sphereSobolevDualRieszL s ell) = ell u := by
  change ⟪u,(InnerProductSpace.toDual ℝ (SphereSobolev s)).symm ell⟫_ℝ = _
  exact (real_inner_comm _ _).trans InnerProductSpace.toDual_symm_apply

lemma sphereSobolevCoefficientL_dualRiesz_inner (s : ℝ)
    (ell : StrongDual ℝ (SphereSobolev s)) (k : ℕ) (z : harmonicSphereSubspace k) :
    ⟪sphereSobolevCoefficientL (-s) k (sphereSobolevDualRieszL s ell),z⟫_ℝ =
      ell (sphereSobolevSingleL s k z) := by
  let r : SphereSobolev (-s) := sphereSobolevDualRieszL s ell
  have hsingle : ⟪r,sphereSobolevSingleL s k z⟫_ℝ =
      ⟪sphereSobolevCoefficientL (-s) k r,z⟫_ℝ := by
    change ⟪r,besselWeight s k • lp.single
      (E := fun j : ℕ => harmonicSphereSubspace j) 2 k z⟫_ℝ =
      ⟪besselWeight (-(-s)) k • r k,z⟫_ℝ
    rw [neg_neg]
    calc
      _ = besselWeight s k * ⟪r,lp.single
          (E := fun j : ℕ => harmonicSphereSubspace j) 2 k z⟫_ℝ :=
        real_inner_smul_right _ _ _
      _ = besselWeight s k * ⟪r k,z⟫_ℝ :=
        congrArg (fun t : ℝ => besselWeight s k * t) (lp.inner_single_right (𝕜 := ℝ) k z r)
      _ = _ := (real_inner_smul_left (r k) z (besselWeight s k)).symm
  exact hsingle.symm.trans InnerProductSpace.toDual_symm_apply

lemma norm_sphereSobolevDualRieszL_apply (s : ℝ)
    (ell : StrongDual ℝ (SphereSobolev s)) : ‖sphereSobolevDualRieszL s ell‖ = ‖ell‖ :=
  (InnerProductSpace.toDual ℝ (SphereSobolev s)).symm.norm_map ell

end OAI.AnisotropicCalderon.SphereHarmonic
