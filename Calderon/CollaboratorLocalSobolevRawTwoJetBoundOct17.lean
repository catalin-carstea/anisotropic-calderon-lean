import Calderon.LocalSobolevRawTwoJetBound
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Morrey
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Proof of `LocalSobolevRawTwoJetBound`.

Route: the recorded weak derivatives of `u` agree a.e. on the ball with the classical derivatives
of the smooth representative (Tau Ceti `Wkp.iteratedGradient_ae_eq_of_contDiffOn`), so their
`L²(ball)` norms through order five are bounded by `‖u‖`. Each jet component `g = D^j uSmooth`
(`j ≤ 2`) is multiplied by a fixed smooth bump `χ` equal to one at the centre. Morrey's inequality
(`p = 6 > 3`) followed by Gagliardo–Nirenberg–Sobolev (`W^{1,2} → L⁶`) bounds `‖(χ • g) p‖` by the
`L²` norm of `D²(χ • g)`, which the Leibniz rule bounds by the `L²(ball)` norms of `D^m g`, `m ≤ 2`.
-/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Module
open scoped NNReal ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource.Literature

end OAI.AnisotropicCalderon.ExteriorSource.Literature

namespace OAI.AnisotropicCalderon.ExteriorSource.Literature.LocalSobolevJet

/-- A Sobolev function of order `m` has lower-order truncations of no larger norm with the same
value component. -/
theorem exists_lower (U : Opens R3) : ∀ (m : ℕ) (u : TauCeti.Wkp (volume : Measure R3) U 2 m)
    (k : ℕ), k ≤ m →
    ∃ v : TauCeti.Wkp (volume : Measure R3) U 2 k, ‖v‖ ≤ ‖u‖ ∧
      TauCeti.Wkp.value k v = TauCeti.Wkp.value m u
  | 0, u, k, hk => by
      obtain rfl : k = 0 := by omega
      exact ⟨u, le_rfl, rfl⟩
  | m + 1, u, k, hk => by
      rcases Nat.lt_or_ge k (m + 1) with h | h
      · obtain ⟨v, hv, hv'⟩ := exists_lower U m (TauCeti.Wkp.lowerOrder m u) k (by omega)
        refine ⟨v, hv.trans (TauCeti.Wkp.norm_lowerOrder_le m u), ?_⟩
        rw [hv', TauCeti.Wkp.value_succ]
      · obtain rfl : k = m + 1 := by omega
        exact ⟨u, le_rfl, rfl⟩

/-- Classical derivatives through the Sobolev order of a smooth representative are bounded in
`L²(U)` by the native graph norm. -/
theorem eLpNorm_iteratedFDeriv_le (U : Opens R3) (m : ℕ)
    (u : TauCeti.Wkp (volume : Measure R3) U 2 m)
    {f : R3 → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (hu : (TauCeti.Wkp.value m u : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict U] f)
    (k : ℕ) (hk : k ≤ m) :
    eLpNorm (iteratedFDeriv ℝ k f) 2 ((volume : Measure R3).restrict U) ≤
      ENNReal.ofReal ‖u‖ := by
  obtain ⟨v, hv, hvu⟩ := exists_lower U m u k hk
  have hv' : (TauCeti.Wkp.value k v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict U] f := by
    rw [hvu]; exact hu
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal hv)
  cases k with
  | zero =>
    have h : eLpNorm (iteratedFDeriv ℝ 0 f) 2 ((volume : Measure R3).restrict U) =
        eLpNorm (TauCeti.Wkp.value 0 v : R3 → ℝ) 2 ((volume : Measure R3).restrict U) := by
      refine eLpNorm_congr_norm_ae ?_ (Lp.aestronglyMeasurable _) ?_
      · exact (ContinuousOn.continuousOn_iteratedFDeriv hf U.isOpen
          (by exact_mod_cast le_top)).aestronglyMeasurable U.isOpen.measurableSet
      filter_upwards [hv'] with x hx
      rw [norm_iteratedFDeriv_zero, hx]
    rw [h, ← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (TauCeti.Wkp.norm_value_le 0 v)
  | succ j =>
    have hg := TauCeti.Wkp.iteratedGradient_ae_eq_of_contDiffOn j v
      (hf.of_le (by exact_mod_cast le_top)) hv'
    have h : eLpNorm (iteratedFDeriv ℝ (j + 1) f) 2 ((volume : Measure R3).restrict U) =
        eLpNorm (TauCeti.Wkp.iteratedGradient j v : R3 → TauCeti.IteratedGradient R3 j) 2
          ((volume : Measure R3).restrict U) := by
      refine eLpNorm_congr_norm_ae ?_ (Lp.aestronglyMeasurable _) ?_
      · exact (ContinuousOn.continuousOn_iteratedFDeriv hf U.isOpen
          (by exact_mod_cast le_top)).aestronglyMeasurable U.isOpen.measurableSet
      filter_upwards [hg] with x hx
      rw [hx, TauCeti.norm_iteratedGradientChain]
    rw [h, ← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (TauCeti.Wkp.norm_iteratedGradient_le j v)

/-- Pointwise Sobolev embedding (Morrey after Gagliardo–Nirenberg–Sobolev) for `C²` functions
supported in a fixed ball. -/
theorem pointwise_bound (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (p : R3) (r : ℝ) (hr : 0 < r) :
    ∃ K : ENNReal, K ≠ ⊤ ∧ ∀ ψ : R3 → F, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      Function.support ψ ⊆ ball p r →
      ‖ψ p‖ₑ ≤ K * eLpNorm (fderiv ℝ (fderiv ℝ ψ)) 2 volume := by
  set y : R3 := p + EuclideanSpace.single 0 r with hy_def
  have hy : y ∉ ball p r := by
    rw [mem_ball, dist_eq_norm, hy_def, add_sub_cancel_left, PiLp.norm_single,
      Real.norm_of_nonneg hr.le]
    exact lt_irrefl r
  have h3 : (finrank ℝ R3 : ℝ≥0) < (6 : ℝ≥0) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  have hM : ∃ KM : ENNReal, KM ≠ ⊤ ∧ ∀ ψ : R3 → F, ContDiff ℝ 1 ψ →
      ‖ψ p - ψ y‖ₑ ≤ KM * eLpNorm (fderiv ℝ ψ) ((6 : ℝ≥0) : ENNReal) volume :=
    ⟨_, ENNReal.ofReal_ne_top, fun ψ hψ =>
      TauCeti.enorm_sub_le_of_contDiff_of_finrank_lt (μ := volume) hψ p y h3⟩
  obtain ⟨KM, hKM, hM⟩ := hM
  have hG : ∃ KG : ENNReal, KG ≠ ⊤ ∧ ∀ φ : R3 → (R3 →L[ℝ] F), ContDiff ℝ 1 φ →
      HasCompactSupport φ →
      eLpNorm φ ((6 : ℝ≥0) : ENNReal) volume ≤
        KG * eLpNorm (fderiv ℝ φ) ((2 : ℝ≥0) : ENNReal) volume :=
    ⟨_, ENNReal.coe_ne_top, fun φ h1 h2 =>
      eLpNorm_le_eLpNorm_fderiv_of_eq volume h1 h2 (by norm_num) (by simp)
        (by rw [finrank_euclideanSpace_fin]; norm_num)⟩
  obtain ⟨KG, hKG, hG⟩ := hG
  refine ⟨KM * KG, ENNReal.mul_ne_top hKM hKG, ?_⟩
  intro ψ hψ hc hs
  have hψy : ψ y = 0 := Function.notMem_support.1 (fun h => hy (hs h))
  have h1 := hM ψ (hψ.of_le (by simp))
  rw [hψy, sub_zero] at h1
  have h2 := hG (fderiv ℝ ψ) (hψ.fderiv_right (m := 1) one_add_one_eq_two.le) (hc.fderiv (𝕜 := ℝ))
  calc ‖ψ p‖ₑ ≤ KM * eLpNorm (fderiv ℝ ψ) ((6 : ℝ≥0) : ENNReal) volume := h1
    _ ≤ KM * (KG * eLpNorm (fderiv ℝ (fderiv ℝ ψ)) ((2 : ℝ≥0) : ENNReal) volume) :=
        mul_le_mul_right h2 KM
    _ = KM * KG * eLpNorm (fderiv ℝ (fderiv ℝ ψ)) 2 volume := by
        rw [mul_assoc]; norm_cast

/-- Leibniz estimate for a cutoff times a function smooth on the ball. -/
theorem cutoff_bound (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : R3) (r : ℝ) (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ ball p r)
    (hχc : HasCompactSupport χ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ g : R3 → F, ContDiffOn ℝ ∞ g (ball p r) →
      ContDiff ℝ ∞ (fun x => χ x • g x) ∧
      eLpNorm (fderiv ℝ (fderiv ℝ (fun x => χ x • g x))) 2 volume ≤
        ENNReal.ofReal A *
          (eLpNorm (iteratedFDeriv ℝ 0 g) 2 ((volume : Measure R3).restrict (ball p r)) +
            eLpNorm (iteratedFDeriv ℝ 1 g) 2 ((volume : Measure R3).restrict (ball p r)) +
            eLpNorm (iteratedFDeriv ℝ 2 g) 2 ((volume : Measure R3).restrict (ball p r))) := by
  have hbd : ∀ i : ℕ, ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ M := fun i =>
    (hχ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hχc.iteratedFDeriv i)
  obtain ⟨M0, hM0⟩ := hbd 0
  obtain ⟨M1, hM1⟩ := hbd 1
  obtain ⟨M2, hM2⟩ := hbd 2
  have hMnn : 0 ≤ max (max M0 M1) (max M2 0) := le_max_of_le_right (le_max_right _ _)
  refine ⟨2 * max (max M0 M1) (max M2 0), by positivity, ?_⟩
  intro g hg
  have hU : IsOpen (ball p r) := isOpen_ball
  have hψ : ContDiff ℝ ∞ (fun x => χ x • g x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball p r
    · exact hχ.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds hx))
    · have hx' : x ∉ tsupport χ := fun h => hx (hχs h)
      have h0 : (fun x => χ x • g x) =ᶠ[nhds x] fun _ => (0 : F) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with z hz
        simp [hz]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  refine ⟨hψ, ?_⟩
  have hsupp : Function.support (fderiv ℝ (fderiv ℝ (fun x => χ x • g x))) ⊆ ball p r :=
    (support_fderiv_subset ℝ).trans ((tsupport_fderiv_subset ℝ).trans
      ((tsupport_smul_subset_left _ _).trans hχs))
  -- Select the second-countable source explicitly; F need not be second countable.
  letI : SecondCountableTopologyEither R3 (R3 →L[ℝ] R3 →L[ℝ] F) :=
    secondCountableTopologyEither_of_left R3 (R3 →L[ℝ] R3 →L[ℝ] F)
  have hmeas : AEStronglyMeasurable (fderiv ℝ (fderiv ℝ (fun x => χ x • g x))) volume :=
    ((hψ.fderiv_right (m := 1) (by simp)).continuous_fderiv one_ne_zero).aestronglyMeasurable
  rw [← eLpNorm_restrict_eq_of_support_subset hmeas hsupp]
  have hpt : ∀ x ∈ ball p r, ‖fderiv ℝ (fderiv ℝ (fun x => χ x • g x)) x‖ ≤
      2 * max (max M0 M1) (max M2 0) * ‖‖iteratedFDeriv ℝ 0 g x‖ + ‖iteratedFDeriv ℝ 1 g x‖ +
        ‖iteratedFDeriv ℝ 2 g x‖‖ := by
    intro x hx
    have hL := norm_iteratedFDerivWithin_smul_le hχ.contDiffOn hg hU.uniqueDiffOn hx
      (n := 2) (by simp)
    have hWχ : ∀ n : ℕ, iteratedFDerivWithin ℝ n χ (ball p r) x = iteratedFDeriv ℝ n χ x :=
      fun n => iteratedFDerivWithin_of_isOpen n hU hx
    have hWg : ∀ n : ℕ, iteratedFDerivWithin ℝ n g (ball p r) x = iteratedFDeriv ℝ n g x :=
      fun n => iteratedFDerivWithin_of_isOpen n hU hx
    rw [iteratedFDerivWithin_of_isOpen 2 hU hx] at hL
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hWχ, hWg] at hL
    simp only [show Nat.choose 2 0 = 1 from rfl,
      show Nat.choose 2 1 = 2 from rfl, show Nat.choose 2 2 = 1 from rfl, Nat.cast_one,
      Nat.cast_ofNat, one_mul] at hL
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    have a0 := mul_le_mul_of_nonneg_right ((hM0 x).trans
      ((le_max_left M0 M1).trans (le_max_left _ (max M2 0)))) (norm_nonneg (iteratedFDeriv ℝ 2 g x))
    have a1 := mul_le_mul_of_nonneg_right ((hM1 x).trans
      ((le_max_right M0 M1).trans (le_max_left _ (max M2 0)))) (norm_nonneg (iteratedFDeriv ℝ 1 g x))
    have a2 := mul_le_mul_of_nonneg_right ((hM2 x).trans
      ((le_max_left M2 0).trans (le_max_right (max M0 M1) _))) (norm_nonneg (iteratedFDeriv ℝ 0 g x))
    have b0 := norm_nonneg (iteratedFDeriv ℝ 0 g x)
    have b1 := norm_nonneg (iteratedFDeriv ℝ 1 g x)
    have b2 := norm_nonneg (iteratedFDeriv ℝ 2 g x)
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith
  have hm : ∀ i : ℕ, AEStronglyMeasurable (iteratedFDeriv ℝ i g)
      ((volume : Measure R3).restrict (ball p r)) := fun i =>
    (ContinuousOn.continuousOn_iteratedFDeriv hg hU (by exact_mod_cast le_top)).aestronglyMeasurable
      measurableSet_ball
  calc eLpNorm (fderiv ℝ (fderiv ℝ (fun x => χ x • g x))) 2
        ((volume : Measure R3).restrict (ball p r))
      ≤ ENNReal.ofReal (2 * max (max M0 M1) (max M2 0)) *
          eLpNorm ((fun x => ‖iteratedFDeriv ℝ 0 g x‖) + (fun x => ‖iteratedFDeriv ℝ 1 g x‖) +
            (fun x => ‖iteratedFDeriv ℝ 2 g x‖)) 2
            ((volume : Measure R3).restrict (ball p r)) :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas.restrict
          ((ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall hpt)) 2
    _ ≤ _ := by
        gcongr
        refine (eLpNorm_add_le (by norm_num)).trans ?_
        refine add_le_add (eLpNorm_add_le (by norm_num)) le_rfl |>.trans ?_
        rw [eLpNorm_norm _ (hm 0), eLpNorm_norm _ (hm 1), eLpNorm_norm _ (hm 2)]

/-- The value at the centre of a function smooth on the ball is controlled by its `H²(ball)`
derivative norms. -/
theorem component_bound (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (p : R3) (r : ℝ) (hr : 0 < r) :
    ∃ K : ENNReal, K ≠ ⊤ ∧ ∀ g : R3 → F, ContDiffOn ℝ ∞ g (ball p r) →
      ‖g p‖ₑ ≤ K *
          (eLpNorm (iteratedFDeriv ℝ 0 g) 2 ((volume : Measure R3).restrict (ball p r)) +
            eLpNorm (iteratedFDeriv ℝ 1 g) 2 ((volume : Measure R3).restrict (ball p r)) +
            eLpNorm (iteratedFDeriv ℝ 2 g) 2 ((volume : Measure R3).restrict (ball p r))) := by
  let b : ContDiffBump p := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hχs : tsupport (b : R3 → ℝ) ⊆ ball p r := by
    rw [b.tsupport_eq]
    exact closedBall_subset_ball (by simp only [b]; linarith)
  obtain ⟨K₁, hK₁, hpt⟩ := pointwise_bound F p r hr
  obtain ⟨A, hA, hcut⟩ := cutoff_bound F p r (b : R3 → ℝ) b.contDiff hχs b.hasCompactSupport
  refine ⟨K₁ * ENNReal.ofReal A, ENNReal.mul_ne_top hK₁ ENNReal.ofReal_ne_top, ?_⟩
  intro g hg
  obtain ⟨hψ, hbound⟩ := hcut g hg
  have hp1 : (b : R3 → ℝ) p = 1 :=
    b.one_of_mem_closedBall (mem_closedBall_self (by simp only [b]; positivity))
  have hsupp : Function.support (fun x => (b : R3 → ℝ) x • g x) ⊆ ball p r :=
    (subset_tsupport _).trans ((tsupport_smul_subset_left _ _).trans hχs)
  have hc : HasCompactSupport (fun x => (b : R3 → ℝ) x • g x) :=
    b.hasCompactSupport.smul_right
  have := hpt _ (hψ.of_le (by simp)) hc hsupp
  simp only [hp1, one_smul] at this
  calc ‖g p‖ₑ ≤ _ := this
    _ ≤ _ := mul_le_mul_right hbound K₁
    _ = _ := (mul_assoc _ _ _).symm

/-- Iterated derivatives of a function smooth on the ball are measurable there. -/
theorem aestronglyMeasurable_iteratedFDeriv {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (p : R3) (r : ℝ) {g : R3 → G} (hg : ContDiffOn ℝ ∞ g (ball p r)) (k : ℕ) :
    AEStronglyMeasurable (iteratedFDeriv ℝ k g) ((volume : Measure R3).restrict (ball p r)) :=
  (ContinuousOn.continuousOn_iteratedFDeriv hg isOpen_ball
    (by exact_mod_cast le_top)).aestronglyMeasurable measurableSet_ball

/-- Conversion of an extended-norm estimate to a real one. -/
theorem norm_le_of_enorm_le {F : Type*} [NormedAddCommGroup F] (x : F) {K : ENNReal}
    (hK : K ≠ ⊤) {t : ℝ} (ht : 0 ≤ t)
    (h : ‖x‖ₑ ≤ K * (ENNReal.ofReal t + ENNReal.ofReal t + ENNReal.ofReal t)) :
    ‖x‖ ≤ 3 * K.toReal * t := by
  rw [← ENNReal.ofReal_toReal hK, ← ENNReal.ofReal_add ht ht,
    ← ENNReal.ofReal_add (by positivity) ht, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  linarith

end OAI.AnisotropicCalderon.ExteriorSource.Literature.LocalSobolevJet

namespace OAI.AnisotropicCalderon.ExteriorSource.Literature

open LocalSobolevJet in
theorem localSobolevRawTwoJetBound : LocalSobolevRawTwoJetBound := by
  intro p r hr
  obtain ⟨K0, hK0, h0⟩ := component_bound ℝ p r hr
  obtain ⟨K1, hK1, h1⟩ := component_bound (R3 →L[ℝ] ℝ) p r hr
  obtain ⟨K2, hK2, h2⟩ := component_bound (R3 →L[ℝ] (R3 →L[ℝ] ℝ)) p r hr
  have hKs : K0 + K1 + K2 ≠ ⊤ := by finiteness
  refine ⟨3 * (K0 + K1 + K2).toReal, by positivity, ?_⟩
  intro u f hf hu
  have hf' : ContDiffOn ℝ ∞ f (ball p r) := hf
  have hD : ∀ k ≤ 5, eLpNorm (iteratedFDeriv ℝ k f) 2
      ((volume : Measure R3).restrict (ball p r)) ≤ ENNReal.ofReal ‖u‖ :=
    fun k hk => eLpNorm_iteratedFDeriv_le _ 5 u hf hu k hk
  have hf1 : ContDiffOn ℝ ∞ (fderiv ℝ f) (ball p r) :=
    hf'.fderiv_of_isOpen isOpen_ball (by simp)
  have hf2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ f)) (ball p r) :=
    hf1.fderiv_of_isOpen isOpen_ball (by simp)
  have hn1 : ∀ k : ℕ, eLpNorm (iteratedFDeriv ℝ k (fderiv ℝ f)) 2
      ((volume : Measure R3).restrict (ball p r)) =
      eLpNorm (iteratedFDeriv ℝ (k + 1) f) 2 ((volume : Measure R3).restrict (ball p r)) :=
    fun k => eLpNorm_congr_norm_ae (aestronglyMeasurable_iteratedFDeriv p r hf1 k)
      (aestronglyMeasurable_iteratedFDeriv p r hf' (k + 1))
      (Filter.Eventually.of_forall fun x => norm_iteratedFDeriv_fderiv)
  have hn2 : ∀ k : ℕ, eLpNorm (iteratedFDeriv ℝ k (fderiv ℝ (fderiv ℝ f))) 2
      ((volume : Measure R3).restrict (ball p r)) =
      eLpNorm (iteratedFDeriv ℝ (k + 1 + 1) f) 2 ((volume : Measure R3).restrict (ball p r)) :=
    fun k => (eLpNorm_congr_norm_ae (aestronglyMeasurable_iteratedFDeriv p r hf2 k)
      (aestronglyMeasurable_iteratedFDeriv p r hf1 (k + 1))
      (Filter.Eventually.of_forall fun x => norm_iteratedFDeriv_fderiv)).trans (hn1 (k + 1))
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  have b0 : ‖f p‖ ≤ 3 * K0.toReal * ‖u‖ := by
    refine norm_le_of_enorm_le _ hK0 hu0 ((h0 f hf').trans ?_)
    gcongr <;> exact hD _ (by norm_num)
  have b1 : ‖fderiv ℝ f p‖ ≤ 3 * K1.toReal * ‖u‖ := by
    refine norm_le_of_enorm_le _ hK1 hu0 ((h1 _ hf1).trans ?_)
    rw [hn1, hn1, hn1]
    gcongr <;> exact hD _ (by norm_num)
  have b2 : ‖fderiv ℝ (fderiv ℝ f) p‖ ≤ 3 * K2.toReal * ‖u‖ := by
    refine norm_le_of_enorm_le _ hK2 hu0 ((h2 _ hf2).trans ?_)
    rw [hn2, hn2, hn2]
    gcongr <;> exact hD _ (by norm_num)
  have c0 : K0.toReal ≤ (K0 + K1 + K2).toReal :=
    ENNReal.toReal_mono hKs (le_add_right (le_add_right le_rfl))
  have c1 : K1.toReal ≤ (K0 + K1 + K2).toReal :=
    ENNReal.toReal_mono hKs (le_add_right (le_add_left le_rfl))
  have c2 : K2.toReal ≤ (K0 + K1 + K2).toReal :=
    ENNReal.toReal_mono hKs (le_add_left le_rfl)
  refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · exact b0.trans (by gcongr)
  · exact b1.trans (by gcongr)
  · exact b2.trans (by gcongr)

end OAI.AnisotropicCalderon.ExteriorSource.Literature
#print axioms OAI.AnisotropicCalderon.ExteriorSource.Literature.localSobolevRawTwoJetBound
