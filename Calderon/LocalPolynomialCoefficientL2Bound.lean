import Calderon.NativePolynomialBallSobolev
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
set_option autoImplicit false
open scoped ENNReal

-- Current selected Section 06 finite-dimensional polynomial coefficient step.
namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory

theorem exists_polynomial_coefficient_le_unitBall_eLpNorm (m : ℕ) :
    let I := {alpha : Fin 3 → Fin (m + 1) // ∑ i, (alpha i).val ≤ m}
    ∃ C : ℝ, 0 < C ∧ ∀ a : I → ℝ, ∀ alpha : I,
      |a alpha| ≤ C *
        (eLpNorm
          (fun z : R3 => ∑ beta : I,
            a beta * ∏ i : Fin 3, (z i) ^ (beta.val i).val)
          2 (volume.restrict (ball (0 : R3) 1))).toReal := by
  classical
  let I := {alpha : Fin 3 → Fin (m + 1) // ∑ i, (alpha i).val ≤ m}
  let μ : Measure R3 := volume.restrict (ball (0 : R3) 1)
  let P : (I → ℝ) → R3 → ℝ := fun a z =>
    ∑ beta : I, a beta * ∏ i : Fin 3, (z i) ^ (beta.val i).val
  change ∃ C : ℝ, 0 < C ∧ ∀ a : I → ℝ, ∀ alpha : I,
    |a alpha| ≤ C * (eLpNorm (P a) 2 μ).toReal
  -- C1: the original Euclidean polynomial is continuous and bounded on the ball.
  have hCont (a : I → ℝ) : Continuous (P a) := by
    apply continuous_finset_sum
    intro beta _
    apply continuous_const.mul
    apply continuous_finset_prod
    intro i _
    exact (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).continuous.pow _
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (measure_ball_ne_top (μ := (volume : Measure R3)))
  have hMem (a : I → ℝ) : MemLp (P a) 2 μ := by
    apply MemLp.of_bound (hCont a).aestronglyMeasurable (∑ beta : I, |a beta|)
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    have hProd (beta : I) : ‖∏ i : Fin 3, (z i) ^ (beta.val i).val‖ ≤ 1 := by
      rw [norm_prod]
      apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      intro i _
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) ((PiLp.norm_apply_le z i).trans hz1)
    calc
      ‖P a z‖ ≤ ∑ beta : I, ‖a beta * ∏ i : Fin 3, (z i) ^ (beta.val i).val‖ :=
        norm_sum_le _ _
      _ ≤ ∑ beta : I, |a beta| := by
        apply Finset.sum_le_sum
        intro beta _
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (hProd beta)
  -- C2: the SAME L2 class map is linear, using the actual toLp laws.
  have hAdd (a b : I → ℝ) : P (a + b) = P a + P b := by
    funext z
    simp only [P, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hSmul (r : ℝ) (a : I → ℝ) : P (r • a) = r • P a := by
    funext z
    simp only [P, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  let T : (I → ℝ) →ₗ[ℝ] Lp ℝ 2 μ :=
    { toFun := fun a => (hMem a).toLp (P a)
      map_add' := fun a b => by
        calc
          (hMem (a + b)).toLp (P (a + b)) =
              ((hMem a).add (hMem b)).toLp (P a + P b) :=
            MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun (hAdd a b)))
          _ = (hMem a).toLp (P a) + (hMem b).toLp (P b) :=
            MemLp.toLp_add _ _
      map_smul' := fun r a => by
        calc
          (hMem (r • a)).toLp (P (r • a)) =
              ((hMem a).const_smul r).toLp (r • P a) :=
            MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun (hSmul r a)))
          _ = r • (hMem a).toLp (P a) := MemLp.toLp_const_smul r _ }
  -- C3-C6: an L2-zero polynomial vanishes pointwise, then all its coefficients vanish.
  have hZero (a : I → ℝ) (hTa : T a = 0) : a = 0 := by
    have hAE : P a =ᵐ[μ] (fun _ : R3 => (0 : ℝ)) := by
      have h := (hMem a).coeFn_toLp
      change (T a : R3 → ℝ) =ᵐ[μ] P a at h
      rw [hTa] at h
      exact h.symm.trans (Lp.coeFn_zero ℝ 2 μ)
    have hBall : EqOn (P a) (fun _ : R3 => (0 : ℝ)) (ball (0 : R3) 1) :=
      Measure.eqOn_open_of_ae_eq (μ := (volume : Measure R3)) hAE isOpen_ball
        (hCont a).continuousOn continuous_const.continuousOn
    let e : I → (Fin 3 →₀ ℕ) := fun beta =>
      Finsupp.equivFunOnFinite.symm (fun i => (beta.val i).val)
    have he : Function.Injective e := by
      intro alpha beta h
      apply Subtype.ext
      funext i
      apply Fin.ext
      have hi := congrArg (fun d : Fin 3 →₀ ℕ => d i) h
      simpa only [e, Finsupp.coe_equivFunOnFinite_symm] using hi
    let p : MvPolynomial (Fin 3) ℝ :=
      ∑ beta : I, MvPolynomial.monomial (e beta) (a beta)
    have hEval (u : Fin 3 → ℝ) :
        MvPolynomial.eval u p = ∑ beta : I, a beta * ∏ i : Fin 3, (u i) ^ (beta.val i).val := by
      simp only [p, map_sum, MvPolynomial.eval_monomial]
      apply Finset.sum_congr rfl
      intro beta _
      congr 1
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      rfl
    have hp : p = 0 := by
      apply MvPolynomial.funext_set (fun _ : Fin 3 => Icc (-(1/2 : ℝ)) (1/2 : ℝ))
        (fun _ => Set.Icc_infinite (by norm_num : -(1/2 : ℝ) < 1/2))
      intro u hu
      let z : R3 := WithLp.toLp 2 u
      have hCoord (i : Fin 3) : (u i)^2 ≤ (1/2 : ℝ)^2 := by
        have hi := hu i (Set.mem_univ i)
        have habs : |u i| ≤ (1/2 : ℝ) := abs_le.mpr hi
        have hs := (sq_le_sq₀ (abs_nonneg (u i)) (by norm_num : (0 : ℝ) ≤ 1/2)).mpr habs
        simpa only [sq_abs] using hs
      have hNorm : ‖z‖^2 ≤ (3/4 : ℝ) := by
        calc
          ‖z‖^2 = ∑ i : Fin 3, (u i)^2 := EuclideanSpace.real_norm_sq_eq z
          _ ≤ ∑ _i : Fin 3, (1/2 : ℝ)^2 := Finset.sum_le_sum (fun i _ => hCoord i)
          _ = (3/4 : ℝ) := by norm_num
      have hz : z ∈ ball (0 : R3) 1 := by
        apply mem_ball_zero_iff.mpr
        nlinarith [norm_nonneg z]
      rw [map_zero, hEval]
      exact hBall hz
    funext alpha
    have hCoeff := congrArg (fun q : MvPolynomial (Fin 3) ℝ => q.coeff (e alpha)) hp
    have hCoeff' : (∑ x : I, if x = alpha then a x else 0) = 0 := by
      simpa [p, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, he.eq_iff] using hCoeff
    have hsum : (∑ x : I, if x = alpha then a x else 0) = a alpha := by
      classical
      exact Fintype.sum_ite_eq' alpha a
    rw [hsum] at hCoeff'
    exact hCoeff'
  -- C7-C8: finite dimensionality gives a positive bound in the existing norms.
  have hKer : LinearMap.ker T = ⊥ := by
    apply le_antisymm _ bot_le
    intro a ha
    change a = 0
    exact hZero a (LinearMap.mem_ker.mp ha)
  obtain ⟨K, hKpos, hK⟩ := T.exists_antilipschitzWith hKer
  refine ⟨(K : ℝ), hKpos, ?_⟩
  intro a alpha
  calc
    |a alpha| = ‖a alpha‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖a‖ := norm_le_pi_norm a alpha
    _ ≤ (K : ℝ) * ‖T a‖ := ZeroHomClass.bound_of_antilipschitz T hK a
    _ = (K : ℝ) * (eLpNorm (P a) 2 μ).toReal := by
      change (K : ℝ) * ‖(hMem a).toLp (P a)‖ = _
      rw [Lp.norm_toLp]

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation
