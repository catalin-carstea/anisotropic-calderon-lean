import Calderon.ProfileFrechetJets
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.RadiusProfile

lemma norm_iteratedFDeriv_exp (n : ℕ) (s : ℝ) :
    ‖iteratedFDeriv ℝ n Real.exp s‖ = Real.exp s := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have he : iteratedDeriv n Real.exp = Real.exp := by
    simpa only [one_mul, one_pow] using iteratedDeriv_exp_const_mul n (1 : ℝ)
  rw [he, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s)]

lemma norm_iteratedFDeriv_exp_comp_le (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u)
    (n : ℕ) (x : R3) (D : ℝ)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i u x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (fun y => Real.exp (u y)) x‖ ≤
      (n.factorial : ℝ) * Real.exp (u x) * D ^ n := by
  exact norm_iteratedFDeriv_comp_le Real.contDiff_exp hu (by simp) x
    (fun i _ => (norm_iteratedFDeriv_exp i (u x)).le) hD

end OAI.AnisotropicCalderon.RadiusProfile

namespace OAI.AnisotropicCalderon.ConformalDepth
open RadiusProfile

lemma contDiff_log_referenceRadius_profile (δ R L : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (fun y => Real.log (referenceRadius δ R p L y)) := by
  rw [log_referenceRadius δ R p L hδ hR]
  exact contDiff_const.add (contDiff_const.mul
    ((contDiff_scalar_log_softplus δ hδ).comp (contDiff_referenceDepth L)))

theorem exists_dilated_referenceRadius_fixed_uniform_jet_envelope
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (n : ℕ) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, ∀ i : ℕ, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i (fun y => Real.log (referenceRadius δ R p L y)) x‖ ≤
          (J * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x) ^ i := by
  classical
  have ht : ∀ i : Fin (n + 1), ∃ J : ℝ, 0 < J ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, 1 ≤ i.val →
        ‖iteratedFDeriv ℝ i.val (fun y => Real.log (referenceRadius δ R p L y)) x‖ ≤
          J * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ i.val := by
    intro i
    by_cases hi : 1 ≤ i.val
    · obtain ⟨J, hJ, hj⟩ := exists_dilated_referenceRadius_fixed_uniform_frechet_jet_bound
        g hg L hL K hK i.val hi
      exact ⟨J, hJ, fun lam hlam δ hδ hδ1 R hR p hp x hx _ =>
        hj lam hlam δ hδ hδ1 R hR p hp x hx⟩
    · exact ⟨1, by norm_num, fun _ _ _ _ _ _ _ _ _ _ _ h => (hi h).elim⟩
  choose Js hJs hbounds using ht
  let J : ℝ := max 1 (∑ i, |Js i|)
  refine ⟨J, le_max_left _ _, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx i hi hin
  let k : Fin (n + 1) := ⟨i, by omega⟩
  have hs : Js k ≤ J := by
    exact (le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (Js j))
      (Finset.mem_univ k)).trans (le_max_right _ _))
  have hpow : Js k ≤ J ^ i := hs.trans (le_self_pow₀ (le_max_left _ _) (by omega))
  have hb : 0 ≤ metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
      (fun y => Real.log (referenceRadius δ R p L y)) x := Real.sqrt_nonneg _
  have hj := hbounds k lam hlam δ hδ hδ1 R hR p hp x hx hi
  exact hj.trans (by simpa only [mul_pow] using
    mul_le_mul_of_nonneg_right hpow (pow_nonneg hb i))

theorem exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ n (referenceRadius δ R p L) x‖ ≤
          C * referenceRadius δ R p L x *
            metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
              (fun y => Real.log (referenceRadius δ R p L y)) x ^ n ∧
        ‖iteratedFDeriv ℝ n (fun y => (referenceRadius δ R p L y)⁻¹) x‖ ≤
          C * (referenceRadius δ R p L x)⁻¹ *
            metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
              (fun y => Real.log (referenceRadius δ R p L y)) x ^ n := by
  obtain ⟨J, hJ, hjets⟩ := exists_dilated_referenceRadius_fixed_uniform_jet_envelope
    g hg L hL K hK n
  refine ⟨(n.factorial : ℝ) * J ^ n, by positivity, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx
  let f : R3 → ℝ := fun y => Real.log (referenceRadius δ R p L y)
  let beta : ℝ := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) f x
  have hf : ContDiff ℝ ∞ f := contDiff_log_referenceRadius_profile δ R L p hδ hR
  have he : (fun y => Real.exp (f y)) = referenceRadius δ R p L := by
    funext y
    exact Real.exp_log (referenceRadius_pos δ R p L y hδ hR)
  have hei : (fun y => Real.exp (-f y)) = fun y => (referenceRadius δ R p L y)⁻¹ := by
    funext y
    rw [Real.exp_neg]
    exact congrArg Inv.inv (Real.exp_log (referenceRadius_pos δ R p L y hδ hR))
  have hplus := norm_iteratedFDeriv_exp_comp_le f hf n x (J * beta)
    (fun i hi hin => hjets lam hlam δ hδ hδ1 R hR p hp x hx i hi hin)
  have hminus := norm_iteratedFDeriv_exp_comp_le (fun y => -f y) hf.neg n x (J * beta)
    (fun i hi hin => by
      rw [show (fun y => -f y) = -f by rfl, iteratedFDeriv_neg_apply, norm_neg]
      exact hjets lam hlam δ hδ hδ1 R hR p hp x hx i hi hin)
  rw [he] at hplus
  rw [hei] at hminus
  have hp0 : Real.exp (f x) = referenceRadius δ R p L x := congrFun he x
  have hm0 : Real.exp (-f x) = (referenceRadius δ R p L x)⁻¹ := congrFun hei x
  rw [hp0, mul_pow] at hplus
  rw [hm0, mul_pow] at hminus
  constructor
  · convert hplus using 1 <;> ring
  · convert hminus using 1 <;> ring

end OAI.AnisotropicCalderon.ConformalDepth
