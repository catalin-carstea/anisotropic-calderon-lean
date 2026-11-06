import Calderon.ActualFiniteSobolevCasimirEnergyBridge
import Calderon.SharpRadialHarmonicCoefficientCore

set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotationProjection

/-! Full upfront: EXPANSION-v001.json. Existing physical Single1 finite packet,
probability-L2 R1 graph, and checked selected shifted Casimir energy specialization. -/

lemma sphereSobolevCoefficientL_one_finite_packet
    (s : Finset ℕ) (u : ∀ k, harmonicSphereSubspace k) (l : ℕ) :
    sphereSobolevCoefficientL 1 l (∑ k ∈ s, sphereSobolevSingleL 1 k (u k)) =
      if l ∈ s then u l else 0 := by
  rw [map_sum]
  by_cases hl : l ∈ s
  · rw [if_pos hl]
    calc
      _ = sphereSobolevCoefficientL 1 l (sphereSobolevSingleL 1 l (u l)) := by
        apply Finset.sum_eq_single l
        · intro k _ hkl
          exact sphereSobolevCoefficientL_single_ne 1 k l hkl.symm (u k)
        · intro h
          exact (h hl).elim
      _ = _ := sphereSobolevCoefficientL_single_self 1 l (u l)
  · rw [if_neg hl]
    apply Finset.sum_eq_zero
    intro k hk
    have hlk : l ≠ k := by
      intro h
      subst k
      exact hl hk
    exact sphereSobolevCoefficientL_single_ne 1 k l hlk (u k)

lemma zeroEquiv_symm_sphereSobolevRotationL_one_single
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevRotationL 1 i j (sphereSobolevSingleL 1 k u)) =
      (harmonicSphereRotation k i j u : SphereL2) := by
  apply (sphereSobolevZeroEquiv hO hD).injective
  rw [LinearIsometryEquiv.apply_symm_apply, sphereSobolevZeroEquiv_harmonic_subtype]
  apply sphereSobolev_ext 0
  intro l
  have hDecode : sphereSobolevCoefficientL 0 l
      (sphereSobolevRotationL 1 i j (sphereSobolevSingleL 1 k u)) =
      harmonicSphereRotation l i j (sphereSobolevCoefficientL 1 l (sphereSobolevSingleL 1 k u)) :=
    (sphereSobolevCoefficientL_one_sub_one l
      (sphereSobolevRotationL 1 i j (sphereSobolevSingleL 1 k u))).symm.trans
        (sphereSobolevCoefficientL_rotation 1 i j l (sphereSobolevSingleL 1 k u))
  rw [hDecode]
  by_cases hl : l = k
  · subst l
    rw [sphereSobolevCoefficientL_single_self, sphereSobolevCoefficientL_single_self]
  · rw [sphereSobolevCoefficientL_single_ne 1 k l hl,
      sphereSobolevCoefficientL_single_ne 0 k l hl, map_zero]

lemma zeroEquiv_symm_sphereSobolevRotationL_one_finite_packet
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) (s : Finset ℕ) (u : ∀ k, harmonicSphereSubspace k) :
    (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevRotationL 1 i j (∑ k ∈ s, sphereSobolevSingleL 1 k (u k))) =
      ∑ k ∈ s, (harmonicSphereRotation k i j (u k) : SphereL2) := by
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl (fun k _ =>
    zeroEquiv_symm_sphereSobolevRotationL_one_single hO hD i j k (u k))

lemma norm_finite_harmonic_packet_le_sqrt_two_casimir_energy
    (n : ℕ) (u : ∀ k, harmonicSphereSubspace k) :
    ‖∑ k ∈ Finset.range n, sphereSobolevSingleL 1 k (u k)‖ ≤
      Real.sqrt 2 * Real.sqrt (∑ k ∈ Finset.range n,
        (1+(k:ℝ)*((k:ℝ)+1)) * ‖u k‖^2) := by
  let P : SphereSobolev 1 := ∑ k ∈ Finset.range n, sphereSobolevSingleL 1 k (u k)
  have hFinite : ∀ k : ℕ, n ≤ k → sphereSobolevCoefficientL 1 k P = 0 := by
    intro k hk
    rw [sphereSobolevCoefficientL_one_finite_packet]
    exact if_neg (fun h => (not_lt.mpr hk) (Finset.mem_range.mp h))
  have hEnergy : (∑ k ∈ Finset.range n,
      (1+(k:ℝ)*((k:ℝ)+1)) * ‖sphereSobolevCoefficientL 1 k P‖^2) =
      ∑ k ∈ Finset.range n, (1+(k:ℝ)*((k:ℝ)+1)) * ‖u k‖^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [sphereSobolevCoefficientL_one_finite_packet, if_pos hk]
  exact (norm_sphereSobolev_one_le_sqrt_two_casimir_energy n P hFinite).trans_eq
    (congrArg (fun r : ℝ => Real.sqrt 2*Real.sqrt r) hEnergy)

lemma sum_norm_sq_finite_harmonic_rotation_packet_le_casimir_energy
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (n : ℕ) (u : ∀ k, harmonicSphereSubspace k) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      ‖∑ k ∈ Finset.range n, (harmonicSphereRotation k i j (u k) : SphereL2)‖^2) ≤
      2 * (∑ k ∈ Finset.range n, (1+(k:ℝ)*((k:ℝ)+1))*‖u k‖^2) := by
  let P : SphereSobolev 1 := ∑ k ∈ Finset.range n, sphereSobolevSingleL 1 k (u k)
  have hFinite : ∀ k : ℕ, n ≤ k → sphereSobolevCoefficientL 1 k P = 0 := by
    intro k hk
    rw [sphereSobolevCoefficientL_one_finite_packet]
    exact if_neg (fun h => (not_lt.mpr hk) (Finset.mem_range.mp h))
  have hEnergy : (∑ k ∈ Finset.range n,
      (1+(k:ℝ)*((k:ℝ)+1)) * ‖sphereSobolevCoefficientL 1 k P‖^2) =
      ∑ k ∈ Finset.range n, (1+(k:ℝ)*((k:ℝ)+1)) * ‖u k‖^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [sphereSobolevCoefficientL_one_finite_packet, if_pos hk]
  have hLeft : (∑ i : Fin 3, ∑ j : Fin 3,
      ‖(sphereSobolevZeroEquiv hO hD).symm (sphereSobolevRotationL 1 i j P)‖^2) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ‖∑ k ∈ Finset.range n, (harmonicSphereRotation k i j (u k) : SphereL2)‖^2 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun f : SphereL2 => ‖f‖^2)
      (zeroEquiv_symm_sphereSobolevRotationL_one_finite_packet hO hD i j (Finset.range n) u)
  exact hLeft.symm.trans_le
    ((sum_norm_sq_sphereSobolevRotationL_one_le_casimir_energy hO hD n P hFinite).trans_eq
      (congrArg (fun r : ℝ => 2*r) hEnergy))

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevCoefficientL_one_finite_packet
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.zeroEquiv_symm_sphereSobolevRotationL_one_single
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.zeroEquiv_symm_sphereSobolevRotationL_one_finite_packet
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_finite_harmonic_packet_le_sqrt_two_casimir_energy
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sum_norm_sq_finite_harmonic_rotation_packet_le_casimir_energy

end OAI.AnisotropicCalderon.SphereHarmonic
