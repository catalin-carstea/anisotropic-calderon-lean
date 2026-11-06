import Calderon.SphereAngularCore

noncomputable section
open MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

def raisingComponent (m : ℕ) (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ := sphereRaising (m - 1) (Pi.single i p)

lemma pderiv_harmonicHomogeneous_succ (m : ℕ) (i : Fin 3)
    (h : MvPolynomial (Fin 3) ℝ) (hh : h ∈ harmonicHomogeneous (m + 1)) :
    pderiv i h ∈ harmonicHomogeneous m := by
  refine ⟨?_, ?_⟩
  · simpa only [Nat.add_sub_cancel] using hh.1.pderiv (i := i)
  · rw [laplacian_pderiv, hh.2, map_zero]

lemma single_harmonicHomogeneous (m : ℕ) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous m) (j : Fin 3) :
    (Pi.single i p : Fin 3 → MvPolynomial (Fin 3) ℝ) j ∈ harmonicHomogeneous m := by
  classical
  by_cases hji : j = i
  · subst j; simpa using hp
  · simpa [Pi.single_apply, hji] using (harmonicHomogeneous m).zero_mem

lemma raisingComponent_harmonicHomogeneous (m : ℕ) (hm : 1 ≤ m) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous m) :
    raisingComponent m i p ∈ harmonicHomogeneous (m + 1) := by
  have h := sphereRaising_harmonicHomogeneous (m - 1) (Pi.single i p)
    (fun j => by simpa only [Nat.sub_add_cancel hm] using single_harmonicHomogeneous m i p hp j)
  simpa only [raisingComponent, show m - 1 + 2 = m + 1 by omega] using h

lemma raisingComponent_inner_adjoint (hF : SphereFischerInner) (m : ℕ) (hm : 1 ≤ m)
    (i : Fin 3) (p h : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous m) (hh : h ∈ harmonicHomogeneous (m + 1)) :
    ⟪polynomialSphereL2 (raisingComponent m i p), polynomialSphereL2 h⟫_ℝ =
      ⟪polynomialSphereL2 p, polynomialSphereL2 (pderiv i h)⟫_ℝ := by
  have hadj := sphereRaising_inner_adjoint hF (m - 1) (Pi.single i p) h
    (fun j => by simpa only [Nat.sub_add_cancel hm] using single_harmonicHomogeneous m i p hp j)
    (by simpa only [show m - 1 + 2 = m + 1 by omega] using hh)
  change ⟪polynomialSphereL2 (sphereRaising (m - 1) (Pi.single i p)), polynomialSphereL2 h⟫_ℝ = _
  rw [hadj]
  classical
  calc
    _ = ∑ j : Fin 3, if j = i then
        ⟪polynomialSphereL2 p, polynomialSphereL2 (pderiv i h)⟫_ℝ else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j = i
      · subst j; simp
      · simp [Pi.single_apply, hji]
    _ = _ := by simp

lemma sum_double_raising_pair_eq_zero (hF : SphereFischerInner) (m : ℕ) (hm : 1 ≤ m)
    (p h : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous m)
    (hh : h ∈ harmonicHomogeneous (m + 2)) :
    (∑ i : Fin 3, ⟪polynomialSphereL2 (raisingComponent (m + 1) i (raisingComponent m i p)),
      polynomialSphereL2 h⟫_ℝ) = 0 := by
  have hh' : h ∈ harmonicHomogeneous ((m + 1) + 1) := by simpa only [Nat.add_assoc] using hh
  simp_rw [raisingComponent_inner_adjoint hF (m + 1) (by omega) _ _ h
    (raisingComponent_harmonicHomogeneous m hm _ p hp) hh']
  simp_rw [raisingComponent_inner_adjoint hF m hm _ p _ hp
    (pderiv_harmonicHomogeneous_succ (m + 1) _ h hh')]
  rw [← inner_sum, ← map_sum]
  change ⟪polynomialSphereL2 p, polynomialSphereL2 (laplacian h)⟫_ℝ = 0
  rw [hh.2, map_zero, inner_zero_right]

lemma sum_double_raising_eq_zero (hF : SphereFischerInner) (m : ℕ) (hm : 1 ≤ m)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous m) :
    (∑ i : Fin 3, raisingComponent (m + 1) i (raisingComponent m i p)) = 0 := by
  let s := ∑ i : Fin 3, raisingComponent (m + 1) i (raisingComponent m i p)
  have hs : s ∈ harmonicHomogeneous (m + 2) := by
    apply (harmonicHomogeneous (m + 2)).sum_mem
    intro i hi
    simpa only [Nat.add_assoc] using raisingComponent_harmonicHomogeneous (m + 1)
      (by omega) i _ (raisingComponent_harmonicHomogeneous m hm i p hp)
  have hz : ‖polynomialSphereL2 s‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    change ⟪polynomialSphereL2 (∑ i : Fin 3, raisingComponent (m + 1) i
      (raisingComponent m i p)), polynomialSphereL2 s⟫_ℝ = 0
    rw [map_sum, sum_inner]
    simpa only [s, map_sum] using sum_double_raising_pair_eq_zero hF m hm p s hp hs
  have htrace : polynomialSphereL2 s = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact (polynomialSphereL2_eq_zero_iff hF (m + 2) s hs).mp htrace

lemma raisingComponent_C_mul (m : ℕ) (i : Fin 3) (c : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) :
    raisingComponent m i (C c * p) = C c * raisingComponent m i p := by
  classical
  have hsingle : (Pi.single i (C c * p) : Fin 3 → MvPolynomial (Fin 3) ℝ) =
      fun j => C c * (Pi.single i p : Fin 3 → MvPolynomial (Fin 3) ℝ) j := by
    funext j
    simp only [Pi.single_apply]
    split_ifs <;> simp
  unfold raisingComponent
  rw [hsingle]
  simp only [sphereRaising, harmonicRaising, polynomialRaising,
    polynomialDivergence, pderiv_mul, pderiv_C, zero_mul, zero_add]
  simp_rw [mul_left_comm (X _) (C c)]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

lemma raisingComponent_degree_commutator (m : ℕ) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    polynomialSphereL2 (C ((m + 1 : ℕ) : ℝ) * raisingComponent m i p) -
      polynomialSphereL2 (raisingComponent m i (C (m : ℝ) * p)) =
        polynomialSphereL2 (raisingComponent m i p) := by
  rw [raisingComponent_C_mul, ← map_sub]
  congr 1
  simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
  ring

end OAI.AnisotropicCalderon.SphereHarmonic
