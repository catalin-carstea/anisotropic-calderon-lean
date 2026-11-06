import Calderon.SphereHarmonicBridge

noncomputable section
open MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

def sphereRaising (k : ℕ) (q : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  C ((Fintype.card (Fin 3) : ℝ) + 2 * (k + 1)) * harmonicRaising k q

lemma pderiv_harmonicHomogeneous (k : ℕ) (i : Fin 3)
    (h : MvPolynomial (Fin 3) ℝ) (hh : h ∈ harmonicHomogeneous (k + 2)) :
    pderiv i h ∈ harmonicHomogeneous (k + 1) := by
  refine ⟨?_, ?_⟩
  · simpa only [show k + 2 - 1 = k + 1 by omega] using hh.1.pderiv (i := i)
  · rw [laplacian_pderiv, hh.2, map_zero]

lemma polynomialDivergence_harmonicHomogeneous (k : ℕ)
    (q : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hq : ∀ i, q i ∈ harmonicHomogeneous (k + 1)) :
    polynomialDivergence q ∈ harmonicHomogeneous k := by
  refine ⟨?_, laplacian_polynomialDivergence q (fun i => (hq i).2)⟩
  simpa only [Nat.add_sub_cancel] using
    polynomialDivergence_isHomogeneous q (fun i => (hq i).1)

lemma sphereRaising_harmonicHomogeneous (k : ℕ)
    (q : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hq : ∀ i, q i ∈ harmonicHomogeneous (k + 1)) :
    sphereRaising k q ∈ harmonicHomogeneous (k + 2) := by
  have hhom := harmonicRaising_isHomogeneous (k := k + 1) (by omega)
    q (fun i => (hq i).1)
  have hΔ := laplacian_harmonicRaising (k := k + 1) q
    (fun i => (hq i).1) (fun i => (hq i).2)
    (by simpa only [Nat.add_sub_cancel] using
      ne_of_gt (radiusSq_laplacian_coefficient_pos (σ := Fin 3) k))
  refine ⟨?_, ?_⟩
  · simpa only [sphereRaising, Nat.add_sub_cancel, Nat.add_assoc] using
      hhom.C_mul ((Fintype.card (Fin 3) : ℝ) + 2 * (k + 1))
  · change laplacian (C _ * harmonicRaising k q) = 0
    rw [laplacian_C_mul]
    simpa only [Nat.add_sub_cancel, mul_zero] using congrArg (fun p => C
      ((Fintype.card (Fin 3) : ℝ) + 2 * (k + 1)) * p) hΔ

lemma sphereRaising_inner_adjoint (hF : SphereFischerInner) (k : ℕ)
    (q : Fin 3 → MvPolynomial (Fin 3) ℝ) (h : MvPolynomial (Fin 3) ℝ)
    (hq : ∀ i, q i ∈ harmonicHomogeneous (k + 1))
    (hh : h ∈ harmonicHomogeneous (k + 2)) :
    ⟪polynomialSphereL2 (sphereRaising k q), polynomialSphereL2 h⟫_ℝ =
      ∑ i : Fin 3, ⟪polynomialSphereL2 (q i), polynomialSphereL2 (pderiv i h)⟫_ℝ := by
  rw [hF (k + 2) _ h (sphereRaising_harmonicHomogeneous k q hq) hh]
  simp_rw [hF (k + 1) _ _ (hq _) (pderiv_harmonicHomogeneous k _ h hh)]
  exact normalizedFischer_raising_adjoint k q h hh.2

lemma polynomialDivergence_sphere_norm_bound (hF : SphereFischerInner) (k : ℕ)
    (q : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hq : ∀ i, q i ∈ harmonicHomogeneous (k + 1)) :
    ‖polynomialSphereL2 (polynomialDivergence q)‖ ^ 2 ≤
      (((k : ℝ) + 3) * (3 + 2 * k)) *
        ∑ i : Fin 3, ‖polynomialSphereL2 (q i)‖ ^ 2 := by
  rw [polynomialSphereL2_norm_sq hF k _ (polynomialDivergence_harmonicHomogeneous k q hq)]
  simp_rw [polynomialSphereL2_norm_sq hF (k + 1) _ (hq _)]
  simpa using normalizedFischer_divergence_bound k q (fun i => (hq i).1)

lemma sphereRaising_norm_bound (hF : SphereFischerInner) (k : ℕ)
    (q : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hq : ∀ i, q i ∈ harmonicHomogeneous (k + 1)) :
    ‖polynomialSphereL2 (sphereRaising k q)‖ ^ 2 ≤
      ((3 + 2 * ((k : ℝ) + 1)) * ((k : ℝ) + 2)) *
        ∑ i : Fin 3, ‖polynomialSphereL2 (q i)‖ ^ 2 := by
  rw [polynomialSphereL2_norm_sq hF (k + 2) _ (sphereRaising_harmonicHomogeneous k q hq)]
  simp_rw [polynomialSphereL2_norm_sq hF (k + 1) _ (hq _)]
  simpa [sphereRaising] using normalizedFischer_harmonicRaising_bound k q
    (fun i => (hq i).1) (fun i => (hq i).2)

lemma sphere_fock_difference (hF : SphereFischerInner) (k : ℕ)
    (qp qm : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hqp : ∀ i, qp i ∈ harmonicHomogeneous (k + 1))
    (hqm : ∀ i, qm i ∈ harmonicHomogeneous (k + 1)) :
    ‖polynomialSphereL2 (sphereRaising k qp)‖ ^ 2 -
      ‖polynomialSphereL2 (polynomialDivergence qm)‖ ^ 2 =
      (((3 : ℝ) + 2 * (k + 1)) *
        ((∑ i : Fin 3, fischerInner (qp i) (qp i)) +
          (∑ i : Fin 3, ∑ j : Fin 3, fischerInner (pderiv j (qp i)) (pderiv i (qp j))) -
          (4 / (4 * (k : ℝ) + 2 * 3)) *
            fischerInner (polynomialDivergence qp) (polynomialDivergence qp)) -
        ((3 : ℝ) + 2 * k) *
          fischerInner (polynomialDivergence qm) (polynomialDivergence qm)) /
        sphereNormalization 3 (k + 1) := by
  rw [polynomialSphereL2_norm_sq hF (k + 2) _ (sphereRaising_harmonicHomogeneous k qp hqp),
    polynomialSphereL2_norm_sq hF k _ (polynomialDivergence_harmonicHomogeneous k qm hqm)]
  simpa [sphereRaising] using normalizedFischer_fock_difference k qp qm
    (fun i => (hqp i).1) (fun i => (hqp i).2)

end OAI.AnisotropicCalderon.SphereHarmonic
