import Calderon.QradFourIndexNormIdentity
import Calderon.ActualAdjacentGainedBracket
import Calderon.ActualRadialCoefficientPivots
import Calderon.ActualQradFiniteFirstOutputLifts
import Calderon.ActualAdjacentGainedFiniteFamilyCaps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual physical Qrad signed self-row.
Uses only the producers: first-output lifts, CL bracket, radial coefficient pivots,
finite-family adjacent caps, plus QradFourIndexNormIdentity/WeakForm. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology InnerProductSpace

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  SmoothSphereRotation NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)

/-! ### Generic finite-index compact cap and continuity of the signed weak integrand. -/

lemma exists_uniform_bound_fin3 {X E : Type*} [TopologicalSpace X] [SeminormedAddCommGroup E]
    (K : Set X) (hK : IsCompact K) (f : Fin 3 → X → E) (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : Fin 3, ∀ x ∈ K, ‖f i x‖ ≤ M := by
  choose Cb hCb using fun i => hK.exists_bound_of_continuousOn (hf i)
  refine ⟨∑ j : Fin 3, max (Cb j) 0, Finset.sum_nonneg fun j _ => le_max_right _ _, ?_⟩
  intro i x hx
  exact (hCb i x hx).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (f := fun j : Fin 3 => max (Cb j) 0)
      (fun j _ => le_max_right _ _) (Finset.mem_univ i)))

lemma continuousOn_qradSignedWeakSelfExpression {X : Type*} [TopologicalSpace X] {K : Set X}
    (RH LH : X → Fin 3 → Hi →L[ℝ] Half) (LL : X → Fin 3 → Half →L[ℝ] Neg)
    (CH : X → Fin 3 → Fin 3 → Hi →L[ℝ] Half) (CL : X → Fin 3 → Fin 3 → Half →L[ℝ] Neg)
    (Q : X → Fin 3 → Fin 3 → ℝ) (r : X → ℝ) (u : X → Hi)
    (hRH : ∀ i, ContinuousOn (fun x => RH x i) K) (hLH : ∀ i, ContinuousOn (fun x => LH x i) K)
    (hLL : ∀ i, ContinuousOn (fun x => LL x i) K)
    (hCH : ∀ i k, ContinuousOn (fun x => CH x i k) K)
    (hCL : ∀ i k, ContinuousOn (fun x => CL x i k) K)
    (hQ : ∀ i j, ContinuousOn (fun x => Q x i j) K) (hr : ContinuousOn r K)
    (hu : ContinuousOn u K) :
    ContinuousOn (fun x => qradSignedWeakSelfExpression (RH x) (LH x) (LL x) (CH x) (CL x)
      (Q x) (r x) (u x)) K := by
  -- the existing pivot is literally the real inner product of the common lp carrier
  have hP : ∀ (A : X → Neg) (Bv : X → Half), ContinuousOn A K → ContinuousOn Bv K →
      ContinuousOn (fun x => sphereSobolevDualPairing (-(1/2 : ℝ)) (A x) (Bv x)) K := by
    intro A Bv hA hB
    unfold sphereSobolevDualPairing
    exact hA.inner hB
  have hW : ∀ i j k l : Fin 3, ContinuousOn (fun x =>
      qradFourIndexWeakForm (RH x) (LH x) (LL x) (CH x) (CL x) i j k l (u x)) K := by
    intro i j k l
    unfold qradFourIndexWeakForm
    exact (((hP _ _ ((hCL i k).clm_apply ((hRH l).clm_apply hu)) ((hRH j).clm_apply hu)).add
      (hP _ _ ((hLL i).clm_apply ((hRH l).clm_apply hu)) ((hCH k j).clm_apply hu))).add
      (hP _ _ ((hLL j).clm_apply ((hCH i l).clm_apply hu)) ((hLH k).clm_apply hu))).add
      (hP _ _ ((hCL j l).clm_apply ((hLH i).clm_apply hu)) ((hLH k).clm_apply hu))
  unfold qradSignedWeakSelfExpression
  refine (hr.pow 6).mul ?_
  refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ =>
    continuousOn_finset_sum _ fun k _ => continuousOn_finset_sum _ fun l _ => ?_
  exact ((hQ i j).mul (hQ k l)).mul (hW i j k l)

/-- Profile step: `|r|β² ≤ θ ≤ 1`, `β ≥ 1` turn the `r^6` gain into `θβ` (checked highCore lemma). -/
lemma abs_le_theta_beta_of_radial_pow_six {D Cst r β θ N : ℝ} (hCst : 0 ≤ Cst) (hN : 0 ≤ N)
    (hD : |D| ≤ Cst * r^6 * N) (hβ : 1 ≤ β) (hrθ : |r| * β^2 ≤ θ) (hθ : θ ≤ 1) :
    |D| ≤ Cst * θ * β * N := by
  have h6 : |r|^6 ≤ θ * β := radial_pow_six_le_theta_mul_beta |r| β θ (abs_nonneg r) hβ hrθ hθ
  have hEven : Even (6 : ℕ) := ⟨3, rfl⟩
  rw [hEven.pow_abs] at h6
  calc
    |D| ≤ Cst * r^6 * N := hD
    _ ≤ Cst * (θ * β) * N := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h6 hCst) hN
    _ = Cst * θ * β * N := by ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
