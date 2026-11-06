import Calderon.UniformBufferedHarmonicJetBounds
import Mathlib.Analysis.Calculus.TaylorIntegral

noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory
open scoped ContDiff ENNReal BigOperators Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity
open EnergyBridge

-- BEFORE-only exact proposed public context. No proof or source authorization.
-- The O1 import is HELD/UNRUN, not a genuine input until Root releases its actual check.
theorem exists_uniform_dilated_metric_buffered_taylor_remainder_bound
    (a : MatrixField) (ha : IsAdmissibleMetric a) (B : ℝ) (hB : 0 < B) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧ lambda0 ≤ 1 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ d : ℝ, 0 < d →
      ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, lambda ∈ Icc (0 : ℝ) lambda0 →
      ∀ D : Set R3, IsOpen D → D ⊆ ball (0 : R3) B →
      ∀ f : R3 → ℝ, ContDiffOn ℝ ∞ f D →
      (∀ x ∈ D,
        divCoeffGrad (principalCoefficient (fun y : R3 => a (lambda • y))) f x = 0) →
      MemLp f 2 ((volume : Measure R3).restrict D) →
      ∀ c : R3, closedBall c (2 * d) ⊆ D →
      ∀ v : R3, ‖v‖ ≤ d / 2 →
        |f (c + v) -
          ∑ j ∈ Finset.range k, ((Nat.factorial j : ℕ) : ℝ)⁻¹ *
            iteratedFDeriv ℝ j f c (fun _ : Fin j => v)| ≤
          C * ‖v‖ ^ k * (eLpNorm f 2 ((volume : Measure R3).restrict D)).toReal := by
  classical
  -- T0: retain O1's cutoff, before either the derivative order or the buffer.
  obtain ⟨lambda0, hLambda0, hLambda0One, hJet⟩ :=
    exists_uniform_dilated_metric_buffered_harmonic_jet_bound a ha B hB
  refine ⟨lambda0, hLambda0, hLambda0One, ?_⟩
  intro k hk d hd
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk))
  obtain ⟨J, hJ, hBound⟩ := hJet (m + 1) d hd
  have hFacPos : 0 < ((Nat.factorial (m + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m + 1)
  refine ⟨J / ((Nat.factorial (m + 1) : ℕ) : ℝ), div_pos hJ hFacPos, ?_⟩
  intro lambda hLambda D hD hDB f hSmooth hPDE hMem c hBuffer v hv
  let N : ℝ := (eLpNorm f 2 ((volume : Measure R3).restrict D)).toReal
  -- T1: each segment point has the SAME d-buffer inside the original domain.
  have hShift (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖t • v‖ ≤ d / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc
      t * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)
      _ ≤ d / 2 := by simpa only [one_mul] using hv
  have hSegmentBuffer (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      closedBall (c + t • v) d ⊆ D := by
    intro z hz
    apply hBuffer
    apply mem_closedBall.mpr
    have hDist : dist (c + t • v) c = ‖t • v‖ := by
      rw [dist_eq_norm, add_sub_cancel_left]
    calc
      dist z c ≤ dist z (c + t • v) + dist (c + t • v) c := dist_triangle _ _ _
      _ ≤ d + d / 2 :=
        add_le_add (mem_closedBall.mp hz) (by rw [hDist]; exact hShift t ht)
      _ ≤ 2 * d := by linarith only [hd]
  have hAt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ (m + 1) f (c + t • v) :=
    (hSmooth.contDiffAt
      (hD.mem_nhds (hSegmentBuffer t ht (mem_closedBall_self hd.le)))).of_le (by simp)
  have hEval (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |iteratedFDeriv ℝ (m + 1) f (c + t • v) (fun _ : Fin (m + 1) => v)| ≤
        J * N * ‖v‖ ^ (m + 1) := by
    have hJetAt : ‖iteratedFDeriv ℝ (m + 1) f (c + t • v)‖ ≤ J * N :=
      hBound lambda hLambda D hD hDB f hSmooth hPDE hMem
        (c + t • v) (hSegmentBuffer t ht)
    calc
      |iteratedFDeriv ℝ (m + 1) f (c + t • v) (fun _ : Fin (m + 1) => v)| ≤
          ‖iteratedFDeriv ℝ (m + 1) f (c + t • v)‖ *
            ∏ _ : Fin (m + 1), ‖v‖ := by
        simpa only [Real.norm_eq_abs] using
          (iteratedFDeriv ℝ (m + 1) f (c + t • v)).le_opNorm
            (fun _ : Fin (m + 1) => v)
      _ = ‖iteratedFDeriv ℝ (m + 1) f (c + t • v)‖ * ‖v‖ ^ (m + 1) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ J * N * ‖v‖ ^ (m + 1) :=
        mul_le_mul_of_nonneg_right hJetAt (pow_nonneg (norm_nonneg v) _)
  -- T2a: evaluate the scalar Taylor weight exactly, including the k = 1 case.
  let K : ℝ := ((m + 1 : ℕ) : ℝ)
  have hKPos : 0 < K := by
    dsimp only [K]
    exact_mod_cast Nat.succ_pos m
  have hKNe : K ≠ 0 := ne_of_gt hKPos
  let G : ℝ → ℝ := fun t => -K⁻¹ * (1 - t) ^ (m + 1)
  have hGDeriv (t : ℝ) : HasDerivAt G ((1 - t) ^ m) t := by
    have hRaw : HasDerivAt G (-K⁻¹ * (K * (1 - t) ^ m * (-1))) t := by
      simpa only [G, K, Nat.add_sub_cancel] using!
        (HasDerivAt.const_mul (-K⁻¹)
          (((hasDerivAt_id t).const_sub 1).pow (m + 1)))
    apply hRaw.congr_deriv
    calc
      -K⁻¹ * (K * (1 - t) ^ m * (-1)) = (K⁻¹ * K) * (1 - t) ^ m := by ring
      _ = (1 - t) ^ m := by rw [inv_mul_cancel₀ hKNe, one_mul]
  have hWeightContinuous : Continuous (fun t : ℝ => (1 - t) ^ m) := by fun_prop
  have hWeightIntegral : (∫ t in (0 : ℝ)..1, (1 - t) ^ m) = K⁻¹ := by
    calc
      (∫ t in (0 : ℝ)..1, (1 - t) ^ m) = G 1 - G 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => hGDeriv t) (hWeightContinuous.intervalIntegrable _ _)
      _ = K⁻¹ := by
        simp only [G, sub_self, sub_zero, zero_pow (Nat.succ_ne_zero m), mul_zero,
          one_pow, mul_one, zero_sub, neg_neg]
  -- T2b: the nonnegative weight is retained in the norm-majorant integral.
  let A : ℝ := J * N * ‖v‖ ^ (m + 1)
  have hIntegralBound :
      |∫ t in (0 : ℝ)..1, (1 - t) ^ m *
        iteratedFDeriv ℝ (m + 1) f (c + t • v) (fun _ : Fin (m + 1) => v)| ≤
        A * K⁻¹ := by
    have hMajorant :
        ‖∫ t in (0 : ℝ)..1, (1 - t) ^ m *
          iteratedFDeriv ℝ (m + 1) f (c + t • v) (fun _ : Fin (m + 1) => v)‖ ≤
          ∫ t in (0 : ℝ)..1, (1 - t) ^ m * A := by
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      · filter_upwards [] with t ht
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _)]
        exact mul_le_mul_of_nonneg_left
          (hEval t ⟨ht.1.le, ht.2⟩) (pow_nonneg (sub_nonneg.mpr ht.2) _)
      · exact (hWeightContinuous.mul continuous_const).intervalIntegrable _ _
    calc
      |∫ t in (0 : ℝ)..1, (1 - t) ^ m *
          iteratedFDeriv ℝ (m + 1) f (c + t • v) (fun _ : Fin (m + 1) => v)| ≤
          ∫ t in (0 : ℝ)..1, (1 - t) ^ m * A := by
        simpa only [Real.norm_eq_abs] using hMajorant
      _ = (∫ t in (0 : ℝ)..1, (1 - t) ^ m) * A :=
        intervalIntegral.integral_mul_const A _
      _ = A * K⁻¹ := by rw [hWeightIntegral, mul_comm]
  -- T2c: the actual local Taylor identity has degree m and remainder order m+1.
  have hTaylor :
      f (c + v) =
        (∑ j ∈ Finset.range (m + 1), ((Nat.factorial j : ℕ) : ℝ)⁻¹ *
          iteratedFDeriv ℝ j f c (fun _ : Fin j => v)) +
        ((Nat.factorial m : ℕ) : ℝ)⁻¹ *
          ∫ t in (0 : ℝ)..1, (1 - t) ^ m *
            iteratedFDeriv ℝ (m + 1) f (c + t • v) (fun _ : Fin (m + 1) => v) := by
    simpa only [smul_eq_mul] using
      (map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := c) (y := v) (n := m) hAt)
  have hError :
      f (c + v) -
        (∑ j ∈ Finset.range (m + 1), ((Nat.factorial j : ℕ) : ℝ)⁻¹ *
          iteratedFDeriv ℝ j f c (fun _ : Fin j => v)) =
        ((Nat.factorial m : ℕ) : ℝ)⁻¹ *
          ∫ t in (0 : ℝ)..1, (1 - t) ^ m *
            iteratedFDeriv ℝ (m + 1) f (c + t • v) (fun _ : Fin (m + 1) => v) := by
    linarith only [hTaylor]
  have hFacMPos : 0 < ((Nat.factorial m : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos m
  have hFacSucc : ((Nat.factorial (m + 1) : ℕ) : ℝ) =
      K * ((Nat.factorial m : ℕ) : ℝ) := by
    dsimp only [K]
    rw [Nat.factorial_succ, Nat.cast_mul]
  have hInvFactor : ((Nat.factorial m : ℕ) : ℝ)⁻¹ * K⁻¹ =
      ((Nat.factorial (m + 1) : ℕ) : ℝ)⁻¹ := by
    rw [hFacSucc, mul_inv_rev]
  rw [hError, abs_mul, abs_of_pos (inv_pos.mpr hFacMPos)]
  calc
    ((Nat.factorial m : ℕ) : ℝ)⁻¹ *
        |∫ t in (0 : ℝ)..1, (1 - t) ^ m *
          iteratedFDeriv ℝ (m + 1) f (c + t • v) (fun _ : Fin (m + 1) => v)| ≤
        ((Nat.factorial m : ℕ) : ℝ)⁻¹ * (A * K⁻¹) :=
      mul_le_mul_of_nonneg_left hIntegralBound (inv_nonneg.mpr hFacMPos.le)
    _ = (((Nat.factorial m : ℕ) : ℝ)⁻¹ * K⁻¹) *
        (J * ‖v‖ ^ (m + 1) * N) := by dsimp only [A]; ring
    _ = ((Nat.factorial (m + 1) : ℕ) : ℝ)⁻¹ *
        (J * ‖v‖ ^ (m + 1) * N) := by rw [hInvFactor]
    _ = (J / ((Nat.factorial (m + 1) : ℕ) : ℝ)) * ‖v‖ ^ (m + 1) * N := by
      rw [div_eq_mul_inv]
      ring

end OAI.AnisotropicCalderon.Regularity
