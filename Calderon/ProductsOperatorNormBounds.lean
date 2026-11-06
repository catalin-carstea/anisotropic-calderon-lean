import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsOperatorNormBounds

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The canonical full operator norm bound for the exact five ordered terms. -/
theorem norm_le_of_eq_ordered_five_terms
    (T D E : U →L[ℝ] V) (C : Fin 3 → U →L[ℝ] V)
    (N J : Fin 3 → U →L[ℝ] U) (i : Fin 3)
    (m cn cm cg r f : ℝ)
    (hm : 0 ≤ m) (hcn : 0 ≤ cn) (hcm : 0 ≤ cm) (hcg : 0 ≤ cg)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hT : ‖T‖ ≤ m / 2) (hD : ‖D‖ ≤ m)
    (hC : ∀ j, ‖C j‖ ≤ m) (hN : ∀ j, ‖N j‖ ≤ cn)
    (hJ : ∀ j, ‖J j‖ ≤ cm) (hrf : |r * f| ≤ cg)
    (hE : E = T.comp (J i) + (∑ j : Fin 3, (C j).comp (N j))
      + r • (∑ j : Fin 3, D.comp ((J j).comp (N j)))
      + (r ^ 2) • (∑ j : Fin 3, T.comp ((J j).comp (N j)))
      + (r * f) • T) :
    ‖E‖ ≤ 1 + (m / 2) * cm + 3 * m * cn + 3 * m * cm * cn
      + 3 * (m / 2) * cm * cn + cg * (m / 2) := by
  have hm2 : 0 ≤ m / 2 := div_nonneg hm (by norm_num)
  have hTJ : ‖T.comp (J i)‖ ≤ (m / 2) * cm :=
    (T.opNorm_comp_le (J i)).trans
      (mul_le_mul hT (hJ i) (norm_nonneg _) hm2)
  have hJN (j : Fin 3) : ‖(J j).comp (N j)‖ ≤ cm * cn :=
    ((J j).opNorm_comp_le (N j)).trans
      (mul_le_mul (hJ j) (hN j) (norm_nonneg _) hcm)
  have hCsum : ‖∑ j : Fin 3, (C j).comp (N j)‖ ≤ 3 * m * cn := by
    calc
      ‖∑ j : Fin 3, (C j).comp (N j)‖
          ≤ ∑ j : Fin 3, ‖(C j).comp (N j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, m * cn := Finset.sum_le_sum fun j _ =>
        ((C j).opNorm_comp_le (N j)).trans
          (mul_le_mul (hC j) (hN j) (norm_nonneg _) hm)
      _ = 3 * m * cn := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hDsum :
      ‖∑ j : Fin 3, D.comp ((J j).comp (N j))‖ ≤ 3 * m * cm * cn := by
    calc
      ‖∑ j : Fin 3, D.comp ((J j).comp (N j))‖
          ≤ ∑ j : Fin 3, ‖D.comp ((J j).comp (N j))‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, m * (cm * cn) := Finset.sum_le_sum fun j _ =>
        (D.opNorm_comp_le ((J j).comp (N j))).trans
          (mul_le_mul hD (hJN j) (norm_nonneg _) hm)
      _ = 3 * m * cm * cn := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hTsum :
      ‖∑ j : Fin 3, T.comp ((J j).comp (N j))‖ ≤ 3 * (m / 2) * cm * cn := by
    calc
      ‖∑ j : Fin 3, T.comp ((J j).comp (N j))‖
          ≤ ∑ j : Fin 3, ‖T.comp ((J j).comp (N j))‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, (m / 2) * (cm * cn) := Finset.sum_le_sum fun j _ =>
        (T.opNorm_comp_le ((J j).comp (N j))).trans
          (mul_le_mul hT (hJN j) (norm_nonneg _) hm2)
      _ = 3 * (m / 2) * cm * cn := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hDscaled :
      ‖r • (∑ j : Fin 3, D.comp ((J j).comp (N j)))‖ ≤ 3 * m * cm * cn := by
    calc
      ‖r • (∑ j : Fin 3, D.comp ((J j).comp (N j)))‖
          = r * ‖∑ j : Fin 3, D.comp ((J j).comp (N j))‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ r * (3 * m * cm * cn) := mul_le_mul_of_nonneg_left hDsum hr0
      _ ≤ 1 * (3 * m * cm * cn) :=
        mul_le_mul_of_nonneg_right hr1 (by positivity)
      _ = 3 * m * cm * cn := one_mul _
  have hrsq : r ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  have hTscaled :
      ‖(r ^ 2) • (∑ j : Fin 3, T.comp ((J j).comp (N j)))‖
        ≤ 3 * (m / 2) * cm * cn := by
    calc
      ‖(r ^ 2) • (∑ j : Fin 3, T.comp ((J j).comp (N j)))‖
          = r ^ 2 * ‖∑ j : Fin 3, T.comp ((J j).comp (N j))‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
      _ ≤ r ^ 2 * (3 * (m / 2) * cm * cn) :=
        mul_le_mul_of_nonneg_left hTsum (sq_nonneg r)
      _ ≤ 1 * (3 * (m / 2) * cm * cn) :=
        mul_le_mul_of_nonneg_right hrsq (by positivity)
      _ = 3 * (m / 2) * cm * cn := one_mul _
  have hlast : ‖(r * f) • T‖ ≤ cg * (m / 2) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hrf hT (norm_nonneg _) hcg
  calc
    ‖E‖ = ‖T.comp (J i) + (∑ j : Fin 3, (C j).comp (N j))
        + r • (∑ j : Fin 3, D.comp ((J j).comp (N j)))
        + (r ^ 2) • (∑ j : Fin 3, T.comp ((J j).comp (N j)))
        + (r * f) • T‖ := congrArg norm hE
    _ ≤ ‖T.comp (J i)‖ + ‖∑ j : Fin 3, (C j).comp (N j)‖
        + ‖r • (∑ j : Fin 3, D.comp ((J j).comp (N j)))‖
        + ‖(r ^ 2) • (∑ j : Fin 3, T.comp ((J j).comp (N j)))‖
        + ‖(r * f) • T‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ (le_refl _))
      refine (norm_add_le _ _).trans (add_le_add ?_ (le_refl _))
      refine (norm_add_le _ _).trans (add_le_add ?_ (le_refl _))
      exact norm_add_le _ _
    _ ≤ 1 + (m / 2) * cm + 3 * m * cn + 3 * m * cm * cn
        + 3 * (m / 2) * cm * cn + cg * (m / 2) := by
      linarith only [hTJ, hCsum, hDscaled, hTscaled, hlast]

/-- Nine real coefficients, each multiplying two ordered compositions. -/
theorem norm_sq_smul_sum_ordered_pairs_le
    (q : Fin 3 → Fin 3 → ℝ)
    (fl : Fin 3 → V →L[ℝ] V) (fh : Fin 3 → U →L[ℝ] U)
    (ee : Fin 3 → U →L[ℝ] V) (cq cf ce r : ℝ)
    (hcq : 0 ≤ cq) (hcf : 0 ≤ cf) (hce : 0 ≤ ce)
    (hq : ∀ i j, |q i j| ≤ cq)
    (hfl : ∀ i, ‖fl i‖ ≤ cf) (hfh : ∀ i, ‖fh i‖ ≤ cf)
    (hee : ∀ i, ‖ee i‖ ≤ ce) :
    ‖(r ^ 2) • (∑ i : Fin 3, ∑ j : Fin 3,
      (q i j) • ((fl i).comp (ee j) + (ee i).comp (fh j)))‖
      ≤ (18 * cq * cf * ce) * r ^ 2 := by
  have hpair (i j : Fin 3) :
      ‖(fl i).comp (ee j) + (ee i).comp (fh j)‖ ≤ 2 * cf * ce := by
    calc
      ‖(fl i).comp (ee j) + (ee i).comp (fh j)‖
          ≤ ‖(fl i).comp (ee j)‖ + ‖(ee i).comp (fh j)‖ := norm_add_le _ _
      _ ≤ cf * ce + ce * cf := add_le_add
        (((fl i).opNorm_comp_le (ee j)).trans
          (mul_le_mul (hfl i) (hee j) (norm_nonneg _) hcf))
        (((ee i).opNorm_comp_le (fh j)).trans
          (mul_le_mul (hee i) (hfh j) (norm_nonneg _) hce))
      _ = 2 * cf * ce := by ring
  have hweighted (i j : Fin 3) :
      ‖(q i j) • ((fl i).comp (ee j) + (ee i).comp (fh j))‖
        ≤ cq * (2 * cf * ce) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hq i j) (hpair i j) (norm_nonneg _) hcq
  have hsum :
      ‖∑ i : Fin 3, ∑ j : Fin 3,
        (q i j) • ((fl i).comp (ee j) + (ee i).comp (fh j))‖
        ≤ 18 * cq * cf * ce := by
    calc
      ‖∑ i : Fin 3, ∑ j : Fin 3,
        (q i j) • ((fl i).comp (ee j) + (ee i).comp (fh j))‖
          ≤ ∑ i : Fin 3, ‖∑ j : Fin 3,
            (q i j) • ((fl i).comp (ee j) + (ee i).comp (fh j))‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          ‖(q i j) • ((fl i).comp (ee j) + (ee i).comp (fh j))‖ :=
        Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, cq * (2 * cf * ce) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hweighted i j
      _ = 18 * cq * cf * ce := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  calc
    ‖(r ^ 2) • (∑ i : Fin 3, ∑ j : Fin 3,
      (q i j) • ((fl i).comp (ee j) + (ee i).comp (fh j)))‖
        = r ^ 2 * ‖∑ i : Fin 3, ∑ j : Fin 3,
          (q i j) • ((fl i).comp (ee j) + (ee i).comp (fh j))‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
    _ ≤ r ^ 2 * (18 * cq * cf * ce) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg r)
    _ = (18 * cq * cf * ce) * r ^ 2 := mul_comm _ _

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsOperatorNormBounds
