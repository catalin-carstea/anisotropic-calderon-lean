import Calderon.ActualPerturbedDefect

noncomputable section
open Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualDefectNorm
open PrincipalCommutator ScalarBaseAdjoint ReferenceDensityBounds PerturbedDensityAdjoint
open ConformalDepth ActualScalarPrincipalAdjoint ActualPerturbedDefect

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_coordinate_directionalFDeriv_le (w : R3 → E) (x : R3) (i : Fin 3) :
    ‖directionalFDeriv (coordinateDirection i) w x‖ ≤ ‖fderiv ℝ w x‖ := by
  simpa only [directionalFDeriv, norm_coordinateDirection, mul_one]
    using (fderiv ℝ w x).le_opNorm (coordinateDirection i)

lemma norm_scalar_first_order_remainder_le (w : R3 → E) (x : R3)
    (c : ℝ) (b : Fin 3 → ℝ) (beta eps Cfirst Czero : ℝ)
    (hb : 0 < beta) (he : 0 ≤ eps) (hCf : 0 ≤ Cfirst) (hCz : 0 ≤ Czero)
    (hc : |c| ≤ Czero * eps) (hbi : ∀ i, |b i| ≤ Cfirst * eps / beta) :
    ‖c • w x + ∑ i, b i • directionalFDeriv (coordinateDirection i) w x‖ ≤
      (Czero + 3*Cfirst) * eps * (‖w x‖ + ‖fderiv ℝ w x‖ / beta) := by
  have hF : 0 ≤ Cfirst * eps / beta := div_nonneg (mul_nonneg hCf he) hb.le
  have hsum : ‖∑ i : Fin 3, b i • directionalFDeriv (coordinateDirection i) w x‖ ≤
      3 * (Cfirst * eps / beta * ‖fderiv ℝ w x‖) := by
    calc
      _ ≤ ∑ i : Fin 3, ‖b i • directionalFDeriv (coordinateDirection i) w x‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, Cfirst * eps / beta * ‖fderiv ℝ w x‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hbi i) (norm_coordinate_directionalFDeriv_le w x i)
          (norm_nonneg _) hF
      _ = _ := by simp
  have hc' : ‖c • w x‖ ≤ Czero * eps * ‖w x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  have hU : 0 ≤ ‖w x‖ := norm_nonneg _
  have hV : 0 ≤ ‖fderiv ℝ w x‖ / beta := div_nonneg (norm_nonneg _) hb.le
  calc
    _ ≤ Czero * eps * ‖w x‖ + 3 * (Cfirst * eps / beta * ‖fderiv ℝ w x‖) :=
      (norm_add_le _ _).trans (add_le_add hc' hsum)
    _ = Czero * eps * ‖w x‖ + (3*Cfirst*eps) * (‖fderiv ℝ w x‖/beta) := by ring
    _ ≤ _ := by
      nlinarith [mul_nonneg (mul_nonneg hCz he) hV,
        mul_nonneg (mul_nonneg (by positivity : 0 ≤ 3*Cfirst) he) hU]

theorem exists_actual_scalar_adjoint_defect_uniform_norm_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      (∀ᶠ y in 𝓝 x, (h y).IsHermitian) →
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta → referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ w : R3 → E, ContDiff ℝ ∞ w →
      ‖scalarSecondBaseAdjoint coordinateDirection (fun y => referenceDensityFamily g L (lam,y))
        (actualPrincipalMatrix g L lam δ R p h) w x -
        scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h) w x‖ ≤
          C * eps * (‖w x‖ + ‖fderiv ℝ w x‖ / beta) := by
  obtain ⟨Cfirst,Czero,hCf,hCz,hcoeff⟩ :=
    exists_actual_adjoint_coefficients_uniform_bounds g hg L hL K hK
  refine ⟨Czero+3*Cfirst, by positivity, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps he he1 h hh hhjet hs beta hb hsmall w hw
  obtain ⟨hfirst,hzero⟩ := hcoeff lam hlam δ hδ hδ1 R hR p hp x hx eps he he1 h hh hhjet hb hsmall
  rw [actual_scalar_adjoint_defect g hg L lam δ R p h w hδ hR hh hw x hs]
  exact norm_scalar_first_order_remainder_le w x _ _ beta eps Cfirst Czero
    (by linarith) he hCf.le hCz.le hzero hfirst

lemma sq_le_twice_sum_sq_of_le (s C eps u v : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (he : 0 ≤ eps)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (h : s ≤ C*eps*(u+v)) :
    s^2 ≤ 2*C^2*eps^2*(u^2+v^2) := by
  have hsquare : s^2 ≤ (C*eps*(u+v))^2 :=
    (sq_le_sq₀ hs (by positivity)).2 h
  have huv : (u+v)^2 ≤ 2*(u^2+v^2) := by nlinarith [sq_nonneg (u-v)]
  have ht := mul_le_mul_of_nonneg_left huv (sq_nonneg (C*eps))
  nlinarith

end OAI.AnisotropicCalderon.ActualDefectNorm
