import Calderon.SphereHarmonicBridge

/-! Harmonic decomposition of polynomials (helper for task 02). -/

noncomputable section
open MvPolynomial
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

/-- The polynomial `x₁² + x₂² + x₃²`. -/
def normSqPoly : MvPolynomial (Fin 3) ℝ := ∑ i, X i ^ 2

lemma normSqPoly_isHomogeneous : normSqPoly.IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i 2

lemma pderiv_normSqPoly (i : Fin 3) : pderiv i normSqPoly = 2 * X i := by
  fin_cases i <;> simp [normSqPoly, Fin.sum_univ_three, pderiv_X]

lemma laplacian_mul (f g : MvPolynomial (Fin 3) ℝ) :
    laplacian (f * g) = laplacian f * g + 2 * ∑ i, pderiv i f * pderiv i g + f * laplacian g := by
  simp only [laplacian, Fin.sum_univ_three, pderiv_mul, map_add]; ring

lemma laplacian_normSqPoly : laplacian normSqPoly = 6 := by
  have h2 : ∀ i : Fin 3, pderiv i (2 : MvPolynomial (Fin 3) ℝ) = 0 := fun i => by
    rw [show (2 : MvPolynomial (Fin 3) ℝ) = C 2 from (map_ofNat C 2).symm, pderiv_C]
  simp only [laplacian, pderiv_normSqPoly, pderiv_mul, Fin.sum_univ_three, pderiv_X_self]
  simp only [h2, zero_mul, zero_add]
  norm_num

lemma laplacian_normSqPoly_mul {f : MvPolynomial (Fin 3) ℝ} {d : ℕ} (hf : f.IsHomogeneous d) :
    laplacian (normSqPoly * f) = normSqPoly * laplacian f + C (6 + 4 * (d : ℝ)) * f := by
  have e := hf.sum_X_mul_pderiv
  have h2 : ∑ i, pderiv i normSqPoly * pderiv i f = 2 * (d • f) := by
    rw [← e, Finset.mul_sum]; simp only [pderiv_normSqPoly]; congr 1; ext1 i; ring
  rw [laplacian_mul, laplacian_normSqPoly, h2]
  simp only [nsmul_eq_mul, map_add, map_mul, map_natCast, map_ofNat]
  ring

lemma laplacian_normSqPoly_pow_mul {h : MvPolynomial (Fin 3) ℝ} {m : ℕ}
    (hh : h ∈ harmonicHomogeneous m) (s : ℕ) :
    laplacian (normSqPoly ^ (s + 1) * h) =
      C (2 * ((s : ℝ) + 1) * (2 * s + 2 * m + 3)) * (normSqPoly ^ s * h) := by
  induction s with
  | zero =>
    rw [pow_one, laplacian_normSqPoly_mul hh.1, hh.2]
    have : (C (2 * ((0 : ℕ) + 1) * (2 * (0 : ℕ) + 2 * m + 3) : ℝ) : MvPolynomial (Fin 3) ℝ) =
        C (6 + 4 * (m : ℝ)) := by
      congr 1; push_cast; ring
    rw [this]; ring
  | succ s ih =>
    have hd : (normSqPoly ^ (s + 1) * h).IsHomogeneous (2 * (s + 1) + m) :=
      (normSqPoly_isHomogeneous.pow _).mul hh.1
    rw [pow_succ', mul_assoc, laplacian_normSqPoly_mul hd, ih]
    have : (C (2 * (((s + 1 : ℕ) : ℝ) + 1) * (2 * ((s + 1 : ℕ) : ℝ) + 2 * m + 3)) :
        MvPolynomial (Fin 3) ℝ) =
        C (2 * ((s : ℝ) + 1) * (2 * s + 2 * m + 3)) +
          C (6 + 4 * (((2 * (s + 1) + m : ℕ)) : ℝ)) := by
      rw [← C_add]; congr 1; push_cast; ring
    rw [this, pow_succ']; ring

/-- The Laplacian as a linear map. -/
def laplacianLinear : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ where
  toFun := laplacian
  map_add' p q := by simp [laplacian, Finset.sum_add_distrib]
  map_smul' c p := by simp [laplacian, Finset.smul_sum]

/-- Span of `‖x‖^{2j} h` with `h` harmonic homogeneous of degree `m`, `2j + m = k`. -/
def harmonicDecompSpan (k : ℕ) : Submodule ℝ (MvPolynomial (Fin 3) ℝ) :=
  Submodule.span ℝ {p | ∃ j m : ℕ, 2 * j + m = k ∧ ∃ h ∈ harmonicHomogeneous m,
    p = normSqPoly ^ j * h}

lemma harmonicDecompSpan_le (k : ℕ) :
    harmonicDecompSpan k ≤ homogeneousSubmodule (Fin 3) ℝ k := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, m, rfl, h, hh, rfl⟩
  exact (normSqPoly_isHomogeneous.pow j).mul hh.1

lemma harmonicHomogeneous_le_decompSpan (k : ℕ) :
    harmonicHomogeneous k ≤ harmonicDecompSpan k := fun h hh =>
  Submodule.subset_span ⟨0, k, by ring, h, hh, by simp⟩

lemma harmonicDecompSpan_le_map (k : ℕ) :
    harmonicDecompSpan k ≤ (harmonicDecompSpan (k + 2)).map laplacianLinear := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, m, rfl, h, hh, rfl⟩
  set c : ℝ := 2 * ((j : ℝ) + 1) * (2 * j + 2 * m + 3)
  have hc : c ≠ 0 := by positivity
  refine ⟨c⁻¹ • (normSqPoly ^ (j + 1) * h), Submodule.smul_mem _ _
    (Submodule.subset_span ⟨j + 1, m, by ring, h, hh, rfl⟩), ?_⟩
  rw [map_smul]
  change c⁻¹ • laplacian _ = _
  rw [laplacian_normSqPoly_pow_mul hh, smul_eq_C_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc,
    C_1, one_mul]

lemma pderiv_eq_zero_of_isHomogeneous_zero {q : MvPolynomial (Fin 3) ℝ} (hq : q.IsHomogeneous 0)
    (i : Fin 3) : pderiv i q = 0 := by
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hq
  rw [hq, pderiv_C]

lemma laplacian_isHomogeneous {p : MvPolynomial (Fin 3) ℝ} {k : ℕ} (hp : p.IsHomogeneous (k + 2)) :
    (laplacian p).IsHomogeneous k :=
  IsHomogeneous.sum _ _ _ fun _ _ => (hp.pderiv.pderiv : IsHomogeneous _ (k + 2 - 1 - 1))

/-- Harmonic decomposition (ABR Theorem 5.7): every homogeneous polynomial of degree `k`
is a sum of terms `‖x‖^{2j} h` with `h` harmonic homogeneous of degree `k - 2j`. -/
theorem homogeneous_mem_harmonicDecompSpan {p : MvPolynomial (Fin 3) ℝ} {k : ℕ}
    (hp : p.IsHomogeneous k) : p ∈ harmonicDecompSpan k := by
  induction k using Nat.strong_induction_on generalizing p with
  | _ k ih =>
  match k, ih, hp with
  | 0, _, hp =>
    refine harmonicHomogeneous_le_decompSpan 0 ⟨hp, ?_⟩
    simp [laplacian, pderiv_eq_zero_of_isHomogeneous_zero hp]
  | 1, _, hp =>
    refine harmonicHomogeneous_le_decompSpan 1 ⟨hp, ?_⟩
    simp [laplacian, pderiv_eq_zero_of_isHomogeneous_zero (hp.pderiv : IsHomogeneous _ (1 - 1))]
  | k + 2, ih, hp =>
    obtain ⟨q, hq, hΔ⟩ := harmonicDecompSpan_le_map k (ih k (by omega) (laplacian_isHomogeneous hp))
    have hpq : p - q ∈ harmonicHomogeneous (k + 2) := by
      refine ⟨hp.sub (harmonicDecompSpan_le _ hq), ?_⟩
      change laplacianLinear (p - q) = 0
      rw [map_sub, hΔ]; exact sub_self _
    simpa using Submodule.add_mem _ (harmonicHomogeneous_le_decompSpan _ hpq) hq

end OAI.AnisotropicCalderon.SphereHarmonic
