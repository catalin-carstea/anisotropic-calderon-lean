import Calderon.CollaboratorUCPCarlemanOct17
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Algebra.Order.Star.Real

/-! # Weak unique continuation: local step and connectedness

Following Le Rousseau–Lebeau (ESAIM COCV 2012, §4), the Carleman estimate `carleman` with the
weight `ψ = s² - |x - z|² - |x - x₁|²` shows that a solution of `div(A ∇u) = 0` vanishing on a
ball `B(z, s)` vanishes near every boundary point `x₁` of that ball (`UCP.local_step`). Given a
point `y` of `Ω` in the closure of the set `Z` where `u` vanishes locally, a nearest point of
`Zᶜ` to a nearby point of `Z` contradicts the local step (`UCP.mem_of_mem_closure`), so `Z` is
relatively clopen in the connected set `Ω` (`UCP.uniqueContinuation_aux`). Coefficients given
only on `Ω` are first replaced by globally smooth positive definite ones agreeing near the
relevant point (`UCP.exists_global_coeff`). -/

noncomputable section
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.UCP

theorem divCoeffGrad_congr {A B : R3 → Matrix (Fin 3) (Fin 3) ℝ} {u v : R3 → ℝ} {x : R3}
    (hA : A =ᶠ[𝓝 x] B) (hu : u =ᶠ[𝓝 x] v) : divCoeffGrad A u x = divCoeffGrad B v x := by
  unfold divCoeffGrad
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (fun z : R3 => ∑ j : Fin 3, A z i j * fderiv ℝ u z (EuclideanSpace.single j 1))
      =ᶠ[𝓝 x] (fun z : R3 => ∑ j : Fin 3, B z i j * fderiv ℝ v z (EuclideanSpace.single j 1)) :=
    (hA.and (hu.fderiv (𝕜 := ℝ))).mono fun z ⟨h1, h2⟩ => by simp only [h1, h2]
  rw [h.fderiv_eq]

theorem divCoeffGrad_eq_zero_of_eventuallyEq_zero (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    {u : R3 → ℝ} {x : R3} (h : u =ᶠ[𝓝 x] 0) : divCoeffGrad A u x = 0 := by
  rw [divCoeffGrad_congr (EventuallyEq.refl _ A) h]; simp [divCoeffGrad]

theorem continuous_divCoeffGrad_of_contDiff {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
    {w : R3 → ℝ} (hw : ContDiff ℝ ∞ w) : Continuous (divCoeffGrad A w) := by
  unfold divCoeffGrad
  refine continuous_finsetSum _ fun i _ => ?_
  have : ContDiff ℝ ∞
      (fun z : R3 => ∑ j : Fin 3, A z i j * fderiv ℝ w z (EuclideanSpace.single j 1)) :=
    ContDiff.sum fun j _ => (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul
      ((hw.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  exact (this.continuous_fderiv (by simp)).clm_apply continuous_const

theorem contDiff_of_tsupport_subset {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : R3 → F} {O : Set R3} (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hs : tsupport f ⊆ O) :
    ContDiff ℝ ∞ f := by
  refine contDiff_of_contDiffOn_union_of_isOpen hf (t := (tsupport f)ᶜ)
    ((contDiffOn_const (c := (0 : F))).congr fun x hx => image_eq_zero_of_notMem_tsupport hx)
    ?_ hO (isClosed_tsupport f).isOpen_compl
  ext x; by_cases hx : x ∈ tsupport f
  · simp [hs hx]
  · simp [hx]

theorem hasCompactSupport_mul_sq {f g : R3 → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => g x * f x ^ 2) :=
  hf.mono fun x hx h => hx (by simp [h])

/-- Smooth globally positive definite modification of `A` near a point. -/
theorem exists_global_coeff {Ω : Set R3} (hΩ : IsOpen Ω) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ContDiffOn ℝ ∞ A Ω) (hpos : ∀ x ∈ Ω, (A x).PosDef) {c : R3} {r : ℝ} (hr : 0 < r)
    (hc : closedBall c (2 * r) ⊆ Ω) :
    ∃ A' : R3 → Matrix (Fin 3) (Fin 3) ℝ, ContDiff ℝ ∞ A' ∧ (∀ x, (A' x).PosDef) ∧
      ∀ x ∈ ball c r, A' x = A x := by
  let χ : ContDiffBump c := ⟨r, 2 * r, hr, by linarith⟩
  refine ⟨fun x => χ x • A x + (1 - χ x) • (1 : Matrix (Fin 3) (Fin 3) ℝ), ?_, ?_, ?_⟩
  · refine ContDiff.add ?_ ((contDiff_const.sub χ.contDiff).smul contDiff_const)
    refine contDiff_of_tsupport_subset hΩ (χ.contDiff.contDiffOn.smul hA) ?_
    refine (tsupport_smul_subset_left _ _).trans ?_
    rw [χ.tsupport_eq]; exact hc
  · intro x
    by_cases h0 : χ x = 0
    · simpa [h0] using Matrix.PosDef.one
    have hx : x ∈ Ω := by
      refine hc (ball_subset_closedBall ?_)
      have : x ∈ Function.support χ := h0
      rwa [χ.support_eq] at this
    have hp : 0 < χ x := lt_of_le_of_ne χ.nonneg (Ne.symm h0)
    exact ((hpos x hx).smul hp).add_posSemidef (Matrix.PosSemidef.one.smul (sub_nonneg.2 χ.le_one))
  · intro x hx
    have : χ x = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hx)
    simp [this]

/-- The convexified weight `s² - |x - z|² - |x - x₁|²`. -/
def wt (s : ℝ) (z x₁ : R3) (x : R3) : ℝ := s ^ 2 - ‖x - z‖ ^ 2 - ‖x - x₁‖ ^ 2

theorem contDiff_wt (s : ℝ) (z x₁ : R3) : ContDiff ℝ ∞ (wt s z x₁) := by
  unfold wt
  exact (contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).sub
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))

theorem fderiv_wt_ne {s r₀ : ℝ} {z x₁ : R3} (hs : 0 < s) (hd : dist x₁ z = s) (hr₀ : r₀ ≤ s / 4)
    {x : R3} (hx : x ∈ closedBall x₁ r₀) : fderiv ℝ (wt s z x₁) x ≠ 0 := by
  have hd' : HasFDerivAt (wt s z x₁) _ x :=
    ((hasFDerivAt_const (s ^ 2) x).sub ((hasFDerivAt_id x).sub_const z).norm_sq).sub
      (((hasFDerivAt_id x).sub_const x₁).norm_sq)
  intro h
  set v : R3 := (x - z) + (x - x₁) with hv
  have h0 : fderiv ℝ (wt s z x₁) x v = 0 := by rw [h]; rfl
  rw [hd'.fderiv] at h0
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply] at h0
  have hvv : inner ℝ v v = 0 := by
    rw [hv, inner_add_left]; simp only [hv] at h0 ⊢; simp at h0; linarith
  have hv0 : v = 0 := inner_self_eq_zero.mp hvv
  have he : x₁ - z = v - (2 : ℝ) • (x - x₁) := by rw [hv, two_smul]; abel
  have h1 : ‖x₁ - z‖ = s := by rw [← dist_eq_norm]; exact hd
  have h2 : ‖x - x₁‖ ≤ r₀ := by rw [← dist_eq_norm]; exact hx
  have h3 : ‖x₁ - z‖ ≤ ‖v‖ + 2 * ‖x - x₁‖ := by
    rw [he]; refine (norm_sub_le _ _).trans (le_of_eq ?_); rw [norm_smul]; norm_num
  rw [hv0, norm_zero] at h3
  linarith

theorem wt_ge {s r₀ a b : ℝ} (hs : 0 < s) (hr₀ : 0 < r₀) (ha0 : 0 ≤ a)
    (ha : a < r₀ ^ 2 / (16 * (s + r₀))) (hb0 : 0 ≤ b) (hb : b ≤ a + s) :
    -(r₀ ^ 2 / 8) ≤ s ^ 2 - b ^ 2 - a ^ 2 := by
  have hpos : 0 < 16 * (s + r₀) := by positivity
  have h1 : a * (16 * (s + r₀)) < r₀ ^ 2 := by rwa [lt_div_iff₀ hpos] at ha
  have h2 : a ≤ r₀ := by nlinarith
  have h3 : b ^ 2 ≤ (a + s) ^ 2 := pow_le_pow_left₀ hb0 hb 2
  nlinarith [mul_le_mul_of_nonneg_left h2 ha0]

theorem le_zero_of_decay {I K a b T : ℝ} (hab : a < b)
    (h : ∀ τ ≥ T, Real.exp (2 * τ * b) * I ≤ K * Real.exp (2 * τ * a)) : I ≤ 0 := by
  have hc : 0 < 2 * (b - a) := by linarith
  have ht : Tendsto (fun τ : ℝ => K * Real.exp (-(2 * (b - a) * τ))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hc)).const_mul K
    simpa using this
  refine ge_of_tendsto ht ((eventually_ge_atTop T).mono fun τ hτ => ?_)
  have h1 := h τ hτ
  have he : Real.exp (2 * τ * a) = Real.exp (-(2 * (b - a) * τ)) * Real.exp (2 * τ * b) := by
    rw [← Real.exp_add]; ring_nf
  rw [he, ← mul_assoc] at h1
  exact le_of_mul_le_mul_right (by rw [mul_comm I]; exact h1) (Real.exp_pos (2 * τ * b))


/-- **Local step.** If `div(A∇u) = 0` near `x₁` and `u` vanishes on a ball `B(z, s)` with
`x₁ ∈ ∂B(z, s)`, then `u` vanishes near `x₁`. -/
theorem local_step {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
    (hpos : ∀ x, (A x).PosDef) {u : R3 → ℝ} {x₁ z : R3} {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hd : dist x₁ z = s) (hu : ContDiffOn ℝ ∞ u (ball x₁ r))
    (hPu : ∀ x ∈ ball x₁ r, divCoeffGrad A u x = 0) (hz : ∀ x ∈ ball z s, u x = 0) :
    u =ᶠ[𝓝 x₁] 0 := by
  set r₀ := min (s / 4) (r / 2) with hr₀def
  have hr₀ : 0 < r₀ := lt_min (by linarith) (by linarith)
  have hr₀s : r₀ ≤ s / 4 := min_le_left _ _
  have hr₀r : r₀ < r := (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨lam, hlam, τ₀, C, hcar⟩ := carleman hA hpos (contDiff_wt s z x₁) x₁ hr₀
    fun x hx => fderiv_wt_ne hs hd hr₀s hx
  let χ : ContDiffBump x₁ := ⟨r₀ / 2, r₀, by positivity, by linarith⟩
  set w : R3 → ℝ := fun x => χ x * u x with hwdef
  have hwsupp : tsupport w ⊆ closedBall x₁ r₀ := by
    refine (tsupport_mul_subset_left (f := fun x => χ x)).trans ?_
    exact χ.tsupport_eq.le
  have hw : ContDiff ℝ ∞ w := contDiff_of_tsupport_subset isOpen_ball
    (χ.contDiff.contDiffOn.mul hu) (hwsupp.trans (closedBall_subset_ball hr₀r))
  have hwc : HasCompactSupport w :=
    (isCompact_closedBall x₁ r₀).of_isClosed_subset (isClosed_tsupport _) hwsupp
  have hwu : ∀ x ∈ ball x₁ (r₀ / 2), w x = u x := fun x hx => by
    simp only [hwdef, χ.one_of_mem_closedBall (ball_subset_closedBall hx), one_mul]
  have hP : ∀ x, divCoeffGrad A w x ≠ 0 → r₀ / 2 ≤ dist x x₁ ∧ s ≤ dist x z := by
    intro x hx
    constructor
    · by_contra hlt; rw [not_le] at hlt
      apply hx
      have hev : w =ᶠ[𝓝 x] u :=
        Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball.2 hlt)) hwu
      rw [divCoeffGrad_congr (EventuallyEq.refl _ A) hev]
      exact hPu x (mem_ball.2 (by linarith))
    · by_contra hlt; rw [not_le] at hlt
      apply hx
      refine divCoeffGrad_eq_zero_of_eventuallyEq_zero A ?_
      exact Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball.2 hlt))
        fun y hy => by simp [hwdef, hz y hy]
  have hPsupp : Function.support (divCoeffGrad A w) ⊆ tsupport w := by
    intro x hx; by_contra h
    exact hx (divCoeffGrad_eq_zero_of_eventuallyEq_zero A (notMem_tsupport_iff_eventuallyEq.mp h))
  have hPc : HasCompactSupport (divCoeffGrad A w) := hwc.mono' hPsupp
  have hPcont := continuous_divCoeffGrad_of_contDiff hA hw
  have hψP : ∀ x, divCoeffGrad A w x ≠ 0 → wt s z x₁ x ≤ -(r₀ ^ 2 / 4) := by
    intro x hx; obtain ⟨h1, h2⟩ := hP x hx
    rw [dist_eq_norm] at h1 h2
    unfold wt; nlinarith [norm_nonneg (x - z), norm_nonneg (x - x₁)]
  set δ := r₀ ^ 2 / (16 * (s + r₀)) with hδdef
  have hδ : 0 < δ := by positivity
  have hδr : δ ≤ r₀ / 2 := by rw [hδdef, div_le_iff₀ (by positivity)]; nlinarith
  have hψB : ∀ x ∈ ball x₁ δ, -(r₀ ^ 2 / 8) ≤ wt s z x₁ x := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    refine wt_ge hs hr₀ (norm_nonneg _) hx (norm_nonneg _) ?_
    have : ‖x₁ - z‖ = s := by rw [← dist_eq_norm]; exact hd
    calc ‖x - z‖ = ‖(x - x₁) + (x₁ - z)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ = _ := by rw [this]
  have hψc := (contDiff_wt s z x₁).continuous
  have hwcont := hw.continuous
  have hw2 : Integrable (fun x => w x ^ 2) :=
    (by fun_prop : Continuous fun x => w x ^ 2).integrable_of_hasCompactSupport
      (hwc.mono fun x hx h => hx (by simp [h]))
  set I := ∫ x in ball x₁ δ, w x ^ 2 with hIdef
  set M := ∫ x, divCoeffGrad A w x ^ 2 with hMdef
  set a := Real.exp (lam * -(r₀ ^ 2 / 4)) with ha
  set b := Real.exp (lam * -(r₀ ^ 2 / 8)) with hb
  have hI : I ≤ 0 := by
    refine le_zero_of_decay (T := max τ₀ 0) (K := max C 0 * M) (a := a) (b := b) ?_ ?_
    · exact Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left (by nlinarith) hlam)
    intro τ hτ
    have hτ0 : 0 ≤ τ := (le_max_right _ _).trans hτ
    have hτ1 : τ ≥ τ₀ := (le_max_left _ _).trans hτ
    have int1 : Integrable (fun x => Real.exp (2 * τ * Real.exp (lam * wt s z x₁ x)) * w x ^ 2) :=
      ((by fun_prop : Continuous fun x => Real.exp (2 * τ * Real.exp (lam * wt s z x₁ x))).mul
        (hw.continuous.pow 2)).integrable_of_hasCompactSupport (hasCompactSupport_mul_sq hwc)
    have int2 : Integrable (fun x => Real.exp (2 * τ * b) * w x ^ 2) := hw2.const_mul _
    have int3 : Integrable (fun x => Real.exp (2 * τ * a) * divCoeffGrad A w x ^ 2) :=
      (continuous_const.mul (hPcont.pow 2)).integrable_of_hasCompactSupport
        (hasCompactSupport_mul_sq hPc)
    calc Real.exp (2 * τ * b) * I = ∫ x in ball x₁ δ, Real.exp (2 * τ * b) * w x ^ 2 :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ x in ball x₁ δ, Real.exp (2 * τ * Real.exp (lam * wt s z x₁ x)) * w x ^ 2 :=
          setIntegral_mono_on int2.integrableOn int1.integrableOn measurableSet_ball
            fun x hx => mul_le_mul_of_nonneg_right (Real.exp_le_exp.2
              (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
                (mul_le_mul_of_nonneg_left (hψB x hx) hlam.le)) (by positivity))) (sq_nonneg _)
      _ ≤ ∫ x, Real.exp (2 * τ * Real.exp (lam * wt s z x₁ x)) * w x ^ 2 :=
          setIntegral_le_integral int1 (Eventually.of_forall fun x => by positivity)
      _ ≤ C * ∫ x, Real.exp (2 * τ * Real.exp (lam * wt s z x₁ x)) * divCoeffGrad A w x ^ 2 :=
          hcar τ hτ1 w hw hwsupp
      _ ≤ max C 0 * ∫ x, Real.exp (2 * τ * Real.exp (lam * wt s z x₁ x)) *
            divCoeffGrad A w x ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (integral_nonneg fun x => by positivity)
      _ ≤ max C 0 * ∫ x, Real.exp (2 * τ * a) * divCoeffGrad A w x ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) int3
            (Eventually.of_forall fun x => ?_)
          by_cases h0 : divCoeffGrad A w x = 0
          · simp [h0]
          · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2
              (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
                (mul_le_mul_of_nonneg_left (hψP x h0) hlam.le)) (by positivity))) (sq_nonneg _)
      _ = max C 0 * M * Real.exp (2 * τ * a) := by rw [integral_const_mul]; ring
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_ball fun x _ => sq_nonneg _
  have hae : (fun x => w x ^ 2) =ᵐ[volume.restrict (ball x₁ δ)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg (w x))
      hw2.integrableOn).mp (le_antisymm hI hI0)
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_ball (hw.continuous.pow 2).continuousOn
    continuousOn_const
  refine Filter.mem_of_superset (ball_mem_nhds x₁ hδ) fun x hx => ?_
  have h1 : w x ^ 2 = 0 := heq hx
  have h2 : w x = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
  show u x = 0
  rw [← hwu x (ball_subset_ball hδr hx)]; exact h2


/-- The set where `u` vanishes near a point is relatively closed in `Ω`. -/
theorem mem_of_mem_closure {Ω : Set R3} (hΩ : IsOpen Ω) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ContDiffOn ℝ ∞ A Ω) (hpos : ∀ x ∈ Ω, (A x).PosDef) {u : R3 → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hPu : ∀ x ∈ Ω, divCoeffGrad A u x = 0) {y : R3} (hyΩ : y ∈ Ω)
    (hy : y ∈ closure {x : R3 | u =ᶠ[𝓝 x] 0}) : u =ᶠ[𝓝 y] 0 := by
  set Z := {x : R3 | u =ᶠ[𝓝 x] 0} with hZdef
  have hZo : IsOpen Z := isOpen_setOfPred_eventually_nhds
  by_contra hyZ
  have hyZ' : y ∈ Zᶜ := hyZ
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp hΩ y hyΩ
  set ρ := ε / 8 with hρdef
  have hρ : 0 < ρ := by positivity
  obtain ⟨z, hzZ, hzy'⟩ := Metric.mem_closure_iff.mp hy ρ hρ
  have hzy : dist z y < ρ := by rw [dist_comm]; exact hzy'
  have hZc : IsClosed Zᶜ := hZo.isClosed_compl
  obtain ⟨x₁, hx₁, hdist⟩ := hZc.exists_infDist_eq_dist ⟨y, hyZ'⟩ z
  set s := infDist z Zᶜ with hsdef
  have hs : 0 < s := (hZc.notMem_iff_infDist_pos ⟨y, hyZ'⟩).mp (fun h => h hzZ)
  have hsρ : s < ρ := (infDist_le_dist_of_mem hyZ').trans_lt hzy
  have hz0 : ∀ x ∈ ball z s, u x = 0 := by
    intro x hx
    have hxZ : x ∈ Z := by
      by_contra hxZ
      have := infDist_le_dist_of_mem (x := z) (show x ∈ Zᶜ from hxZ)
      rw [mem_ball, dist_comm] at hx
      linarith
    exact hxZ.self_of_nhds
  have hx₁y : dist x₁ y < 2 * ρ := by
    have := dist_triangle x₁ z y
    rw [dist_comm x₁ z, ← hdist] at this
    linarith
  have hsub : closedBall x₁ (2 * ρ) ⊆ Ω := by
    intro x hx
    apply hεΩ
    rw [mem_closedBall] at hx
    rw [mem_ball]
    have := dist_triangle x x₁ y
    linarith
  obtain ⟨A', hA', hpos', hAA'⟩ := exists_global_coeff hΩ hA hpos hρ hsub
  have hballΩ : ball x₁ ρ ⊆ Ω :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hsub
  have hloc := local_step hA' hpos' hs hρ (by rw [dist_comm]; exact hdist.symm)
    (hu.mono hballΩ) (fun x hx => ?_) hz0
  · exact hx₁ hloc
  have hev : A' =ᶠ[𝓝 x] A := Filter.mem_of_superset (isOpen_ball.mem_nhds hx) hAA'
  rw [divCoeffGrad_congr hev (EventuallyEq.refl _ u)]
  exact hPu x (hballΩ hx)

theorem uniqueContinuation_aux : UniqueContinuation := by
  intro Ω hΩ hconn A hA hpos u hu hPu V hV hVne hVΩ hV0 x hx
  have hZo : IsOpen {x : R3 | u =ᶠ[𝓝 x] 0} := isOpen_setOfPred_eventually_nhds
  obtain ⟨v, hv⟩ := hVne
  have hsub : Ω ⊆ {x : R3 | u =ᶠ[𝓝 x] 0} := by
    refine hconn.isPreconnected.subset_of_closure_inter_subset hZo
      ⟨v, hVΩ hv, Filter.mem_of_superset (hV.mem_nhds hv) hV0⟩ ?_
    rintro y ⟨hy, hyΩ⟩
    exact mem_of_mem_closure hΩ hA hpos hu hPu hyΩ hy
  exact (hsub hx).self_of_nhds

end OAI.AnisotropicCalderon.UCP
