import Calderon.HarmonicCoordinateCompatibility
import Calderon.SpherePositiveDensity

set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereDerivativeAdjoint
open SphereHarmonic AngularPolynomial HarmonicCoordinateCompatibility

def sphereDerivativeAdjoint (k : ℕ) (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ := C (2*(k:ℝ)+3) * coordinateHarmonicRaising k i p

lemma sphereDerivativeAdjoint_eq_raisingComponent (k : ℕ) (hk : 1 ≤ k)
    (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    sphereDerivativeAdjoint k i p = raisingComponent k i p := by
  rw [sphereDerivativeAdjoint,coordinateHarmonicRaising_eq_harmonicRaising k hk,
    raisingComponent,sphereRaising]
  congr 2
  rw [Nat.cast_sub hk]
  simp only [Nat.cast_one,Fintype.card_fin,Nat.cast_ofNat]
  ring

lemma sphereDerivativeAdjoint_zero_C (i : Fin 3) (r : ℝ) :
    sphereDerivativeAdjoint 0 i (C r) = C 3 * (X i * C r) := by
  simp [sphereDerivativeAdjoint,coordinateHarmonicRaising]

lemma eq_C_of_harmonicHomogeneous_zero (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous 0) : p = C (p.coeff 0) :=
  totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous (Fin 3)).2 hp.1)

theorem sphereDerivativeAdjoint_harmonicHomogeneous (k : ℕ) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    sphereDerivativeAdjoint k i p ∈ harmonicHomogeneous (k+1) := by
  cases k with
  | zero =>
    rw [eq_C_of_harmonicHomogeneous_zero p hp,sphereDerivativeAdjoint_zero_C]
    refine ⟨?_,?_⟩
    · simpa using ((isHomogeneous_X (R := ℝ) i).mul
        (isHomogeneous_C (Fin 3) (p.coeff 0))).C_mul 3
    · rw [laplacian_C_mul,laplacian_X_mul]
      simp [laplacian]
  | succ k =>
    rw [sphereDerivativeAdjoint_eq_raisingComponent (k+1) (by omega)]
    exact raisingComponent_harmonicHomogeneous (k+1) (by omega) i p hp

theorem sphereDerivativeAdjoint_inner_adjoint (hF : SphereFischerInner) (k : ℕ)
    (i : Fin 3) (p h : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) (hh : h ∈ harmonicHomogeneous (k+1)) :
    ⟪polynomialSphereL2 (sphereDerivativeAdjoint k i p),polynomialSphereL2 h⟫_ℝ =
      ⟪polynomialSphereL2 p,polynomialSphereL2 (pderiv i h)⟫_ℝ := by
  cases k with
  | zero =>
    rw [hF 1 _ h (sphereDerivativeAdjoint_harmonicHomogeneous 0 i p hp) hh,
      hF 0 p _ hp (pderiv_harmonicHomogeneous_succ 0 i h hh)]
    rw [eq_C_of_harmonicHomogeneous_zero p hp,sphereDerivativeAdjoint_zero_C]
    simp only [normalizedFischerInner,fischerInner_C_mul_left,fischerInner_X_mul_left,
      Fintype.card_fin,sphereNormalization_succ,sphereNormalization_zero,Nat.cast_zero,
      Nat.cast_ofNat,mul_zero,add_zero,mul_one,div_one]
    ring
  | succ k =>
    rw [sphereDerivativeAdjoint_eq_raisingComponent (k+1) (by omega)]
    exact raisingComponent_inner_adjoint hF (k+1) (by omega) i p h hp hh

lemma sum_double_sphereDerivativeAdjoint_pair_eq_zero (hF : SphereFischerInner) (k : ℕ)
    (p h : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k)
    (hh : h ∈ harmonicHomogeneous (k+2)) :
    (∑ i : Fin 3, ⟪polynomialSphereL2
      (sphereDerivativeAdjoint (k+1) i (sphereDerivativeAdjoint k i p)),
      polynomialSphereL2 h⟫_ℝ) = 0 := by
  have hh' : h ∈ harmonicHomogeneous ((k+1)+1) := by simpa [Nat.add_assoc] using hh
  simp_rw [sphereDerivativeAdjoint_inner_adjoint hF (k+1) _ _ h
    (sphereDerivativeAdjoint_harmonicHomogeneous k _ p hp) hh']
  simp_rw [sphereDerivativeAdjoint_inner_adjoint hF k _ p _ hp
    (pderiv_harmonicHomogeneous_succ (k+1) _ h hh')]
  rw [← inner_sum,← map_sum]
  change ⟪polynomialSphereL2 p,polynomialSphereL2 (laplacian h)⟫_ℝ = 0
  rw [hh.2,map_zero,inner_zero_right]

theorem sum_double_sphereDerivativeAdjoint_eq_zero (hF : SphereFischerInner) (k : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    (∑ i : Fin 3, sphereDerivativeAdjoint (k+1) i (sphereDerivativeAdjoint k i p)) = 0 := by
  let s := ∑ i : Fin 3, sphereDerivativeAdjoint (k+1) i (sphereDerivativeAdjoint k i p)
  have hs : s ∈ harmonicHomogeneous (k+2) := by
    apply (harmonicHomogeneous (k+2)).sum_mem
    intro i hi
    simpa [Nat.add_assoc] using sphereDerivativeAdjoint_harmonicHomogeneous (k+1) i _
      (sphereDerivativeAdjoint_harmonicHomogeneous k i p hp)
  have hn : ‖polynomialSphereL2 s‖^2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    change ⟪polynomialSphereL2 (∑ i : Fin 3, sphereDerivativeAdjoint (k+1) i
      (sphereDerivativeAdjoint k i p)),polynomialSphereL2 s⟫_ℝ = 0
    rw [map_sum,sum_inner]
    simpa only [s,map_sum] using sum_double_sphereDerivativeAdjoint_pair_eq_zero hF k p s hp hs
  exact (polynomialSphereL2_eq_zero_iff hF (k+2) s hs).mp
    (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

lemma sphereDerivativeAdjoint_C_mul (k : ℕ) (i : Fin 3) (r : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) :
    sphereDerivativeAdjoint k i (C r*p) = C r*sphereDerivativeAdjoint k i p := by
  simp only [sphereDerivativeAdjoint,coordinateHarmonicRaising,pderiv_C_mul]
  ring

lemma sphereDerivativeAdjoint_add (k : ℕ) (i : Fin 3) (p q : MvPolynomial (Fin 3) ℝ) :
    sphereDerivativeAdjoint k i (p+q) = sphereDerivativeAdjoint k i p +
      sphereDerivativeAdjoint k i q := by
  simp only [sphereDerivativeAdjoint,coordinateHarmonicRaising,map_add]
  ring

lemma sphereDerivativeAdjoint_zero (k : ℕ) (i : Fin 3) :
    sphereDerivativeAdjoint k i 0 = 0 := by
  simp [sphereDerivativeAdjoint,coordinateHarmonicRaising]

lemma sphereDerivativeAdjoint_constant_one (i : Fin 3) :
    sphereDerivativeAdjoint 0 i (C 1) = C 3*X i := by
  simpa only [map_one,mul_one] using sphereDerivativeAdjoint_zero_C i 1

lemma sphereDerivativeAdjoint_degree_commutator (k : ℕ) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    polynomialSphereL2 (C ((k+1:ℕ):ℝ)*sphereDerivativeAdjoint k i p) -
      polynomialSphereL2 (sphereDerivativeAdjoint k i (C (k:ℝ)*p)) =
        polynomialSphereL2 (sphereDerivativeAdjoint k i p) := by
  rw [sphereDerivativeAdjoint_C_mul,← map_sub]
  congr 1
  simp only [Nat.cast_add,Nat.cast_one,map_add,map_one]
  ring

end OAI.AnisotropicCalderon.SphereDerivativeAdjoint
