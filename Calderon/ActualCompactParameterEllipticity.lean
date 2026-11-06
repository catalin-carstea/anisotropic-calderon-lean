import Calderon.ActualCompactParameterRankOneCoercivity
import MixedKernelNativeRoomInterpolation
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.CutoffCommutator
theorem ellipticity_on_compact_parameter_space
    {X : Type*} [TopologicalSpace X] [T2Space X] {a : Fin 3 → Fin 3 → X → ℝ} (hac : ∀ i k, Continuous (a i k))
    {K : Set X} (hK : IsCompact K)
    (hpos : ∀ x ∈ K, ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → 0 < ∑ i, ∑ k, ξ i * a i k x * ξ k) :
    ∃ lamE Λ : ℝ, 0 < lamE ∧
      (∀ x ∈ K, ∀ ξ : Fin 3 → ℝ, lamE * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ k, ξ i * a i k x * ξ k) ∧
      (∀ x ∈ K, ∀ ζ ξ : Fin 3 → ℝ,
        (∑ i, ∑ k, ζ i * a i k x * ξ k) ^ 2 ≤ Λ ^ 2 * (∑ i, ζ i ^ 2) * ∑ k, ξ k ^ 2) := by
  have hQc : Continuous (fun p : X × (Fin 3 → ℝ) =>
      ∑ i, ∑ k, p.2 i * a i k p.1 * p.2 k) := by
    have hA : Continuous (fun x:X => fun i k => a i k x) := continuous_pi fun i => continuous_pi fun k => hac i k
    fun_prop
  obtain ⟨D, α, -, hα, hcoer⟩ := StrictWeightCarleman.uniform_rank_one_coercivity_on_compact_parameter_space hK
    (fun x ξ => ∑ i, ∑ k, ξ i * a i k x * ξ k) (fun _ _ => 0) hQc continuous_const
    (fun x c ξ => by simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]; ring)
    (fun x c ξ => by ring) (fun x hx ξ hξ _ => hpos x hx ξ hξ)
  have hnc : Continuous (fun x => ∑ i, ∑ k, a i k x ^ 2) := by
    have hA : Continuous (fun x:X => fun i k => a i k x) := continuous_pi fun i => continuous_pi fun k => hac i k
    fun_prop
  obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn hnc.continuousOn
  refine ⟨α, max N 1, hα, fun x hx ξ => ?_, fun x hx ζ ξ => ?_⟩
  · have h := hcoer x hx ξ
    simpa using h
  · have hrow : (∑ i, ∑ k, ζ i * a i k x * ξ k) ^ 2 ≤
        (∑ i, ζ i ^ 2) * ((∑ i, ∑ k, a i k x ^ 2) * ∑ k, ξ k ^ 2) := by
      have e : ∑ i, ∑ k, ζ i * a i k x * ξ k = ∑ i, ζ i * ∑ k, a i k x * ξ k :=
        Finset.sum_congr rfl fun i _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      rw [e]
      refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun i _ => sq_nonneg _)
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hNx : ∑ i, ∑ k, a i k x ^ 2 ≤ max N 1 ^ 2 := by
      have h1 := hN x hx
      rw [Real.norm_eq_abs] at h1
      have h2 := le_abs_self (∑ i, ∑ k, a i k x ^ 2)
      have hM1 : (1 : ℝ) ≤ max N 1 := le_max_right _ _
      have hM : max N 1 ≤ max N 1 ^ 2 := by
        rw [sq]
        exact le_mul_of_one_le_left (by linarith) hM1
      exact h2.trans (h1.trans ((le_max_left N 1).trans hM))
    have hζ : 0 ≤ ∑ i, ζ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hξ : 0 ≤ ∑ k, ξ k ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    calc _ ≤ (∑ i, ζ i ^ 2) * ((∑ i, ∑ k, a i k x ^ 2) * ∑ k, ξ k ^ 2) := hrow
      _ ≤ (∑ i, ζ i ^ 2) * (max N 1 ^ 2 * ∑ k, ξ k ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNx hξ) hζ
      _ = _ := by ring

end OAI.AnisotropicCalderon.CutoffCommutator
