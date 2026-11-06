import Calderon.SphereSobolevCoefficientOrderZero
import Calderon.SphereSobolevMidpointFiniteCoefficients
import Calderon.SphereSobolevOrderOneRotation

set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph SmoothSphereRotationProjection SmoothSphereRotationBounds

/-! Existing finite decoded lp2 cutoff, actual H1-to-H0 rotations and probability-L2 decoding; selected Casimir shift is 1+k(k+1). -/

lemma norm_sq_sphereSobolev_finite_decoded
    (s : ℝ) (n : ℕ) (u : SphereSobolev s)
    (hu : ∀ k : ℕ, n ≤ k → sphereSobolevCoefficientL s k u = 0) :
    ‖u‖^2 = ∑ k ∈ Finset.range n,
      besselWeight s k^2 * ‖sphereSobolevCoefficientL s k u‖^2 := by
  have hPacket := sphereSobolev_eq_sum_lp_single_of_finiteSupport s u n hu
    (Finset.range n) (fun _ h => h)
  have hNorm := lp.norm_sum_single (E := fun k : ℕ => harmonicSphereSubspace k)
    (p := (2:ℝ≥0∞)) (by norm_num) (fun k => u k) (Finset.range n)
  rw [← hPacket] at hNorm
  have hRaw : ‖u‖^2 = ∑ k ∈ Finset.range n, ‖u k‖^2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hNorm
  calc
    _ = ∑ k ∈ Finset.range n, ‖u k‖^2 := hRaw
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← sphereSobolevCoefficientL_reconstruct s k u, norm_smul,
        Real.norm_eq_abs, abs_of_pos (besselWeight_pos s k), mul_pow]

lemma norm_sphereSobolev_one_le_sqrt_two_casimir_energy
    (n : ℕ) (u : SphereSobolev 1)
    (hu : ∀ k : ℕ, n ≤ k → sphereSobolevCoefficientL 1 k u = 0) :
    ‖u‖ ≤ Real.sqrt 2 * Real.sqrt (∑ k ∈ Finset.range n,
      (1+(k:ℝ)*((k:ℝ)+1)) * ‖sphereSobolevCoefficientL 1 k u‖^2) := by
  have hEnergy : 0 ≤ ∑ k ∈ Finset.range n,
      (1+(k:ℝ)*((k:ℝ)+1)) * ‖sphereSobolevCoefficientL 1 k u‖^2 := by
    apply Finset.sum_nonneg
    intro k _
    positivity
  have hSq : ‖u‖^2 ≤ 2 * (∑ k ∈ Finset.range n,
      (1+(k:ℝ)*((k:ℝ)+1)) * ‖sphereSobolevCoefficientL 1 k u‖^2) := by
    rw [norm_sq_sphereSobolev_finite_decoded 1 n u hu, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have hWeight : (1+(k:ℝ))^2 ≤ 2*(1+(k:ℝ)*((k:ℝ)+1)) := by
      nlinarith [sq_nonneg (k:ℝ)]
    have h := mul_le_mul_of_nonneg_right hWeight
      (sq_nonneg ‖sphereSobolevCoefficientL 1 k u‖)
    simpa only [besselWeight, Real.rpow_one, mul_assoc] using h
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sq_sqrt hEnergy]
  exact hSq

lemma sum_norm_sq_sphereSobolevRotationL_one_finite
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (n : ℕ) (u : SphereSobolev 1)
    (hu : ∀ k : ℕ, n ≤ k → sphereSobolevCoefficientL 1 k u = 0) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      ‖(sphereSobolevZeroEquiv hO hD).symm (sphereSobolevRotationL 1 i j u)‖^2) =
    2 * (∑ k ∈ Finset.range n,
      (k:ℝ)*((k:ℝ)+1) * ‖sphereSobolevCoefficientL 1 k u‖^2) := by
  have hCoeff (i j : Fin 3) (k : ℕ) :
      sphereSobolevCoefficientL 0 k (sphereSobolevRotationL 1 i j u) =
        harmonicSphereRotation k i j (sphereSobolevCoefficientL 1 k u) := by
    exact (sphereSobolevCoefficientL_one_sub_one k (sphereSobolevRotationL 1 i j u)).symm.trans
      (sphereSobolevCoefficientL_rotation (1:ℝ) i j k u)
  have hFinite (i j : Fin 3) : ∀ k : ℕ, n ≤ k →
      sphereSobolevCoefficientL 0 k (sphereSobolevRotationL 1 i j u) = 0 := by
    intro k hk
    rw [hCoeff, hu k hk, map_zero]
  have hNorm (i j : Fin 3) :
      ‖(sphereSobolevZeroEquiv hO hD).symm (sphereSobolevRotationL 1 i j u)‖^2 =
      ∑ k ∈ Finset.range n,
        ‖harmonicSphereRotation k i j (sphereSobolevCoefficientL 1 k u)‖^2 := by
    calc
      _ = ‖sphereSobolevRotationL 1 i j u‖^2 :=
        congrArg (fun r : ℝ => r^2)
          ((sphereSobolevZeroEquiv hO hD).symm.norm_map (sphereSobolevRotationL 1 i j u))
      _ = _ := by
        simpa only [hCoeff, besselWeight_zero_order, one_pow, one_mul] using
          norm_sq_sphereSobolev_finite_decoded 0 n (sphereSobolevRotationL 1 i j u) (hFinite i j)
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k ∈ Finset.range n,
        ‖harmonicSphereRotation k i j (sphereSobolevCoefficientL 1 k u)‖^2 :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hNorm i j))
    _ = ∑ i : Fin 3, ∑ k ∈ Finset.range n, ∑ j : Fin 3,
        ‖harmonicSphereRotation k i j (sphereSobolevCoefficientL 1 k u)‖^2 :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ k ∈ Finset.range n, ∑ i : Fin 3, ∑ j : Fin 3,
        ‖harmonicSphereRotation k i j (sphereSobolevCoefficientL 1 k u)‖^2 := Finset.sum_comm
    _ = ∑ k ∈ Finset.range n,
        (2*(k:ℝ)*((k:ℝ)+1))*‖sphereSobolevCoefficientL 1 k u‖^2 :=
      Finset.sum_congr rfl (fun k _ =>
        sum_harmonicSphereRotation_norm_sq k (sphereSobolevCoefficientL 1 k u))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

lemma sum_norm_sq_sphereSobolevRotationL_one_le_casimir_energy
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (n : ℕ) (u : SphereSobolev 1)
    (hu : ∀ k : ℕ, n ≤ k → sphereSobolevCoefficientL 1 k u = 0) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      ‖(sphereSobolevZeroEquiv hO hD).symm (sphereSobolevRotationL 1 i j u)‖^2) ≤
    2 * (∑ k ∈ Finset.range n,
      (1+(k:ℝ)*((k:ℝ)+1)) * ‖sphereSobolevCoefficientL 1 k u‖^2) := by
  rw [sum_norm_sq_sphereSobolevRotationL_one_finite hO hD n u hu]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right
    (by linarith : (k:ℝ)*((k:ℝ)+1) ≤ 1+(k:ℝ)*((k:ℝ)+1))
    (sq_nonneg ‖sphereSobolevCoefficientL 1 k u‖)

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sq_sphereSobolev_finite_decoded
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolev_one_le_sqrt_two_casimir_energy
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sum_norm_sq_sphereSobolevRotationL_one_finite
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sum_norm_sq_sphereSobolevRotationL_one_le_casimir_energy

end OAI.AnisotropicCalderon.SphereHarmonic
