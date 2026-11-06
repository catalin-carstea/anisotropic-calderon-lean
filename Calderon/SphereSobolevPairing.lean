import Calderon.SphereSobolevCompletion

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph


theorem inner_sphereSobolev (s : ℝ) (u v : SphereSobolev s) :
    ⟪u, v⟫_ℝ = ∑' k : ℕ, besselWeight s k ^ 2 *
      ⟪sphereSobolevCoefficientL s k u, sphereSobolevCoefficientL s k v⟫_ℝ := by
  have hscale (k : ℕ) (r t : ℝ) (a b : harmonicSphereSubspace k) :
      ⟪r • a, t • b⟫_ℝ = (r * t) * ⟪a, b⟫_ℝ := by
    calc
      ⟪r • a, t • b⟫_ℝ = r * ⟪a, t • b⟫_ℝ :=
        real_inner_smul_left (F := harmonicSphereSubspace k) a (t • b) r
      _ = r * (t * ⟪a, b⟫_ℝ) :=
        congrArg (fun z : ℝ => r * z)
          (real_inner_smul_right (F := harmonicSphereSubspace k) a b t)
      _ = (r * t) * ⟪a, b⟫_ℝ := (mul_assoc r t ⟪a, b⟫_ℝ).symm
  have hcoordinate (k : ℕ) :
      ⟪u k, v k⟫_ℝ = besselWeight s k ^ 2 *
        ⟪sphereSobolevCoefficientL s k u, sphereSobolevCoefficientL s k v⟫_ℝ := by
    have hu : besselWeight s k • sphereSobolevCoefficientL s k u = u k :=
      sphereSobolevCoefficientL_reconstruct s k u
    have hv : besselWeight s k • sphereSobolevCoefficientL s k v = v k :=
      sphereSobolevCoefficientL_reconstruct s k v
    calc
      ⟪u k, v k⟫_ℝ =
          ⟪besselWeight s k • sphereSobolevCoefficientL s k u,
            besselWeight s k • sphereSobolevCoefficientL s k v⟫_ℝ :=
        congrArg₂ (fun (a b : harmonicSphereSubspace k) => ⟪a, b⟫_ℝ) hu.symm hv.symm
      _ = besselWeight s k ^ 2 *
          ⟪sphereSobolevCoefficientL s k u, sphereSobolevCoefficientL s k v⟫_ℝ := by
        simpa only [pow_two] using hscale k (besselWeight s k) (besselWeight s k)
          (sphereSobolevCoefficientL s k u) (sphereSobolevCoefficientL s k v)
  calc
    ⟪u, v⟫_ℝ = ∑' k : ℕ, ⟪u k, v k⟫_ℝ := lp.inner_eq_tsum (𝕜 := ℝ) u v
    _ = ∑' k : ℕ, besselWeight s k ^ 2 *
        ⟪sphereSobolevCoefficientL s k u, sphereSobolevCoefficientL s k v⟫_ℝ :=
      tsum_congr hcoordinate

def sphereSobolevDualPairing (s : ℝ) (u : SphereSobolev s)
    (v : SphereSobolev (-s)) : ℝ := ⟪u, v⟫_ℝ

theorem sphereSobolevDualPairing_eq_tsum (s : ℝ) (u : SphereSobolev s)
    (v : SphereSobolev (-s)) :
    sphereSobolevDualPairing s u v = ∑' k : ℕ,
      ⟪sphereSobolevCoefficientL s k u, sphereSobolevCoefficientL (-s) k v⟫_ℝ := by
  have hscale (k : ℕ) (r t : ℝ) (a b : harmonicSphereSubspace k) :
      ⟪r • a, t • b⟫_ℝ = (r * t) * ⟪a, b⟫_ℝ := by
    calc
      ⟪r • a, t • b⟫_ℝ = r * ⟪a, t • b⟫_ℝ :=
        real_inner_smul_left (F := harmonicSphereSubspace k) a (t • b) r
      _ = r * (t * ⟪a, b⟫_ℝ) :=
        congrArg (fun z : ℝ => r * z)
          (real_inner_smul_right (F := harmonicSphereSubspace k) a b t)
      _ = (r * t) * ⟪a, b⟫_ℝ := (mul_assoc r t ⟪a, b⟫_ℝ).symm
  have hweight (k : ℕ) : besselWeight (-s) k * besselWeight s k = 1 := by
    simpa only [besselWeight, neg_add_cancel, Real.rpow_zero] using
      (Real.rpow_add (by positivity : 0 < 1 + (k : ℝ)) (-s) s).symm
  have hdecode (k : ℕ) (a b : harmonicSphereSubspace k) :
      ⟪besselWeight (-s) k • a, besselWeight s k • b⟫_ℝ = ⟪a, b⟫_ℝ := by
    calc
      _ = (besselWeight (-s) k * besselWeight s k) * ⟪a, b⟫_ℝ :=
        hscale k (besselWeight (-s) k) (besselWeight s k) a b
      _ = ⟪a, b⟫_ℝ := by rw [hweight k, one_mul]
  have hcoordinate (k : ℕ) :
      ⟪u k, v k⟫_ℝ =
        ⟪sphereSobolevCoefficientL s k u, sphereSobolevCoefficientL (-s) k v⟫_ℝ := by
    have hu : sphereSobolevCoefficientL s k u = besselWeight (-s) k • u k := rfl
    have hv0 : sphereSobolevCoefficientL (-s) k v = besselWeight (-(-s)) k • v k := rfl
    have hv : sphereSobolevCoefficientL (-s) k v = besselWeight s k • v k := by
      simpa only [neg_neg] using hv0
    exact ((congrArg₂ (fun (a b : harmonicSphereSubspace k) => ⟪a, b⟫_ℝ) hu hv).trans
      (hdecode k (u k) (v k))).symm
  calc
    sphereSobolevDualPairing s u v = ∑' k : ℕ, ⟪u k, v k⟫_ℝ :=
      lp.inner_eq_tsum (𝕜 := ℝ) u v
    _ = ∑' k : ℕ,
        ⟪sphereSobolevCoefficientL s k u, sphereSobolevCoefficientL (-s) k v⟫_ℝ :=
      tsum_congr hcoordinate

theorem abs_sphereSobolevDualPairing_le (s : ℝ) (u : SphereSobolev s)
    (v : SphereSobolev (-s)) :
    |sphereSobolevDualPairing s u v| ≤ ‖u‖ * ‖v‖ := by
  exact abs_real_inner_le_norm u v

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.inner_sphereSobolev

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_eq_tsum

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.abs_sphereSobolevDualPairing_le
