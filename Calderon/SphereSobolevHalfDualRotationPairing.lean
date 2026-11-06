import Calderon.SphereSobolevOrderOneRotation
import Calderon.SphereSobolevPairing
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotationProjection

lemma real_inner_inverseDegree_harmonicSphereRotation_skew (k : ℕ) (i j : Fin 3)
    (a b : harmonicSphereSubspace k) :
    ⟪(1+(k:ℝ))⁻¹ • harmonicSphereRotation k i j a,b⟫_ℝ =
      -⟪a,(1+(k:ℝ))⁻¹ • harmonicSphereRotation k i j b⟫_ℝ := by
  let c : ℝ := (1+(k:ℝ))⁻¹
  have hL : ⟪c • harmonicSphereRotation k i j a,b⟫_ℝ = c * ⟪harmonicSphereRotation k i j a,b⟫_ℝ :=
    real_inner_smul_left (F := harmonicSphereSubspace k) (harmonicSphereRotation k i j a) b c
  have hR : ⟪a,c • harmonicSphereRotation k i j b⟫_ℝ = c * ⟪a,harmonicSphereRotation k i j b⟫_ℝ :=
    real_inner_smul_right (F := harmonicSphereSubspace k) a (harmonicSphereRotation k i j b) c
  exact hL.trans ((congrArg (fun r : ℝ => c*r) (inner_harmonicSphereRotation_skew k i j a b)).trans
    ((mul_neg c ⟪a,harmonicSphereRotation k i j b⟫_ℝ).trans (congrArg (fun r : ℝ => -r) hR.symm)))

lemma sphereSobolevDualPairing_half_rotation_skew (i j : Fin 3)
    (u v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (-(1/2:ℝ)) (sphereSobolevRotationL (1/2:ℝ) i j u) v =
      -sphereSobolevDualPairing (1/2:ℝ) u (sphereSobolevRotationL (1/2:ℝ) i j v) := by
  change ⟪sphereSobolevRotationL (1/2:ℝ) i j u,v⟫_ℝ =
    -⟪u,sphereSobolevRotationL (1/2:ℝ) i j v⟫_ℝ
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum,← tsum_neg]
  apply tsum_congr
  intro k
  change ⟪(1+(k:ℝ))⁻¹ • harmonicSphereRotation k i j (u k),v k⟫_ℝ =
    -⟪u k,(1+(k:ℝ))⁻¹ • harmonicSphereRotation k i j (v k)⟫_ℝ
  exact real_inner_inverseDegree_harmonicSphereRotation_skew k i j (u k) (v k)

end OAI.AnisotropicCalderon.SphereHarmonic
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_half_rotation_skew

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.real_inner_inverseDegree_harmonicSphereRotation_skew
