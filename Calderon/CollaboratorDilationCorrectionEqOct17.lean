import Calderon.CollaboratorInteriorSmoothOct17
import Calderon.CollaboratorRegularityBaseCaseOct17

/-! Weak equations: from the classical equation, pushed forward from the unit ball, and the
uniform `H¹` energy estimate (helpers for `DilationCorrection`). -/

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory TopologicalSpace Metric Filter Topology
open scoped ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity.DC
open TauCeti TauCeti.PDE EnergyBridge _root_.OAI.AnisotropicCalderon.Affine

/-! ### The weak equation from the classical one -/

/-- A `W^{1,2}(ball c r)` function with a smooth representative solving `div(A ∇f) = 0`
classically solves the equation weakly. -/
theorem weak_of_classical (c : R3) {r : ℝ} (hr : 0 < r) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ContDiff ℝ ∞ A) (w : W1p (volume : Measure R3) (ballO c r) 2) {f : R3 → ℝ}
    (hf : ContDiffOn ℝ ∞ f (ball c r))
    (hwf : ⇑(W1p.value w) =ᵐ[(volume : Measure R3).restrict (ball c r)] f)
    (heq : ∀ x ∈ ball c r, divCoeffGrad A f x = 0) (φ : 𝓓(ballO c r, ℝ)) :
    ∫ x in ball c r, matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient w x) = 0 := by
  have hgrad := IS.gradient_ae_eq w hf hwf
  have hK : tsupport (φ : R3 → ℝ) ⊆ ball c r := φ.tsupport_subset
  obtain ⟨r0, hr0, hK0⟩ := exists_lt_subset_ball (isClosed_tsupport _) hK
  set r1 : ℝ := max r0 (r / 2) with hr1
  have hr1r : r1 < r := max_lt hr0 (by linarith)
  have hr1p : 0 < r1 := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hK1 : tsupport (φ : R3 → ℝ) ⊆ ball c r1 := hK0.trans (ball_subset_ball (le_max_left _ _))
  let χ : ContDiffBump c := ⟨(r1 + r) / 2, (r1 + 3 * r) / 4, by linarith, by linarith⟩
  let ψ : R3 → ℝ := fun z => χ z * f z
  have hχts : tsupport (χ : R3 → ℝ) ⊆ ball c r := by
    rw [χ.tsupport_eq]; exact closedBall_subset_ball (by simp [χ]; linarith)
  have hψ : ContDiff ℝ ∞ ψ := by
    refine contDiff_iff_contDiffAt.2 fun y => ?_
    by_cases hy : y ∈ ball c r
    · exact χ.contDiff.contDiffAt.mul (hf.contDiffAt (isOpen_ball.mem_nhds hy))
    · have hy' : y ∉ tsupport (χ : R3 → ℝ) := fun h => hy (hχts h)
      refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hy'] with z hz
      simp [ψ, image_eq_zero_of_notMem_tsupport hz]
  have hψf : ∀ y ∈ ball c r1, ψ =ᶠ[𝓝 y] f := by
    intro y hy
    have hy' : ball c r1 ∈ 𝓝 y := isOpen_ball.mem_nhds hy
    filter_upwards [hy'] with z hz
    have hz' : z ∈ closedBall c ((r1 + r) / 2) :=
      ball_subset_closedBall (ball_subset_ball (by linarith) hz)
    simp [ψ, χ.one_of_mem_closedBall (by simpa [χ] using hz')]
  have hzero : ∀ z, (φ : R3 → ℝ) z * divCoeffGrad A ψ z = 0 := by
    intro z
    by_cases hz : z ∈ tsupport (φ : R3 → ℝ)
    · have hz1 := hK1 hz
      have hev := hψf z hz1
      have e : divCoeffGrad A ψ z = divCoeffGrad A f z := by
        rw [IS.divCoeffGrad_eq, IS.divCoeffGrad_eq]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        refine Filter.EventuallyEq.fderiv_eq ?_
        filter_upwards [hev.fderiv (𝕜 := ℝ)] with z' hz'
        simp only [IS.cf, hz']
      rw [e, heq z (hK hz), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have h2 : ∫ z in ball c r, matrixBilinearForm (A z) (gradient (φ : R3 → ℝ) z)
      (W1p.gradient w z) = ∫ z in ball c r, matrixBilinearForm (A z) (∇ (φ : R3 → ℝ) z) (∇ ψ z) := by
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with z hz
    by_cases hzg : z ∈ tsupport (φ : R3 → ℝ)
    · have e : ∇ f z = ∇ ψ z := by
        simp only [gradient, (hψf z (hK1 hzg)).fderiv_eq (𝕜 := ℝ)]
      rw [hz, e]
    · rw [HO.gradient_eq_zero_of_notMem_tsupport hzg]; simp
  have h3 : ∫ z in ball c r, matrixBilinearForm (A z) (∇ (φ : R3 → ℝ) z) (∇ ψ z) =
      ∫ z, matrixBilinearForm (A z) (∇ (φ : R3 → ℝ) z) (∇ ψ z) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [HO.gradient_eq_zero_of_notMem_tsupport (fun h => hz (hK h))]; simp
  rw [h2, h3, IS.integral_mbf_eq hA hψ φ.contDiff φ.hasCompactSupport]
  simp [hzero]

/-! ### Pushing an equation forward from the unit ball -/

theorem push_eq (c : R3) {s : ℝ} (hs : 0 < s) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (v : W1p (volume : Measure R3) (ballO c s) 2)
    (heq : ∀ ψ : 𝓓(ballOpens, ℝ), ∫ y in (ballOpens : Set R3),
      matrixBilinearForm (A (c + s • y)) (gradient (ψ : R3 → ℝ) y)
        (W1p.gradient (pullWkp c hs 1 v : W1p (volume : Measure R3) ballOpens 2) y) = 0)
    (φ : 𝓓(ballO c s, ℝ)) :
    ∫ x in ball c s, matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient v x) = 0 := by
  let ψ : 𝓓(ballOpens, ℝ) := compTest hs (isAff_ball c hs) φ
  have hψ : ∀ y, ∇ (ψ : R3 → ℝ) y = s • ∇ (φ : R3 → ℝ) (c + s • y) := fun y =>
    IS.gradient_comp_aff (φ.contDiff.differentiable (by simp)) c s y
  let g : R3 → ℝ := fun x => matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient v x)
  have h1 := heq ψ
  have hint : ∫ y in (ballOpens : Set R3), matrixBilinearForm (A (c + s • y))
      (gradient (ψ : R3 → ℝ) y)
      (W1p.gradient (pullWkp c hs 1 v : W1p (volume : Measure R3) ballOpens 2) y) =
      ∫ y in (ballOpens : Set R3), s ^ 2 * g (c + s • y) := by
    refine integral_congr_ae ?_
    filter_upwards [gradient_pullWkp_one c hs v] with y hy
    rw [hy, hψ]
    simp only [g, map_smul, _root_.smul_apply, smul_eq_mul]
    ring
  rw [hint, integral_const_mul, BallReg.setIntegral_comp c hs g] at h1
  have hs2 : s ^ 2 ≠ 0 := by positivity
  have hsc : (sc s).toReal⁻¹ ≠ 0 := by
    exact inv_ne_zero (ENNReal.toReal_ne_zero.2 ⟨sc_ne_zero hs, sc_ne_top⟩)
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd h hs2
  · rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' hsc
    · exact h'

/-! ### Uniform ellipticity of the dilated coefficients -/

theorem exists_uniform_elliptic (c : R3) {R : ℝ} (hR : 0 < R)
    {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : Continuous A) (hpos : ∀ x, (A x).PosDef) :
    ∃ lam Lam : ℝ, ∀ s : ℝ, 0 < s → s ≤ R →
      UniformlyEllipticOn (ballOpens : Set R3) (fun y => A (c + s • y)) lam Lam := by
  have ha : Continuous fun y : R3 => A (c + R • y) := hA.comp (by fun_prop)
  obtain ⟨lam, Lam, hell⟩ := BallReg.exists_uniformlyEllipticOn ha (fun y => hpos (c + R • y))
  refine ⟨lam, Lam, fun s hs hsR => ⟨hell.1, hell.2.1, fun y hy => ?_⟩⟩
  have hy' : ‖y‖ < 1 := by simpa [B] using hy
  have hmem : (s / R) • y ∈ (ballOpens : Set R3) := by
    show (s / R) • y ∈ B
    simp only [B, mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hs hR)]
    have : s / R ≤ 1 := (div_le_one hR).2 hsR
    nlinarith [norm_nonneg y, div_pos hs hR]
  have e : c + R • ((s / R) • y) = c + s • y := by
    rw [smul_smul, mul_div_cancel₀ _ hR.ne']
  have := hell.2.2 hmem
  simp only [e] at this
  exact this

/-! ### Solving the Dirichlet problem with an `H¹` bound (generic instance path) -/

section GenI

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

theorem energyFormH1_zero_eq (u v : W1p mu Omega 2) :
    energyFormH1 a 0 0 u v = ∫ x in Omega,
      matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x) ∂mu := by
  rw [energyFormH1_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [energyIntegrand_apply]

theorem weak_of_isWeak {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) (φ : W1p mu Omega 2)
    (hφ : φ ∈ w1p0Submodule mu Omega 2) :
    ∫ x in Omega, matrixBilinearForm (a x) (W1p.gradient φ x)
        (W1p.gradient (u : W1p mu Omega 2) x) ∂mu =
      ∫ x in Omega, f x * W1p.value φ x ∂mu := by
  have := hu ⟨φ, hφ⟩
  rw [energyFormH1_zero_eq, dirichletForcing_apply_eq_setIntegral] at this
  exact this

end GenI

section Gen

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}

theorem gen_exists (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 ≤ R)
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃ u : W1p0 volume Omega 2, IsWeakSolutionDirichlet a 0 0 f u := by
  have key := UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_subset_ball
    (b := 0) (c := 0) (beta := 0) (gamma := 0) h ha aestronglyMeasurable_const
    aestronglyMeasurable_const le_rfl (by simp) (by simp) (by simp) hR hball
    (by simpa using h.pos) f
  exact key.exists

theorem gen_solve (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 ≤ R)
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃ w : W1p (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2,
      w ∈ w1p0Submodule (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 ∧
      ∀ φ : W1p (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2,
        φ ∈ w1p0Submodule (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 →
        ∫ x in Omega, matrixBilinearForm (a x) (W1p.gradient φ x) (W1p.gradient w x) =
          ∫ x in Omega, f x * W1p.value φ x := by
  obtain ⟨u, hu⟩ := gen_exists h ha hR hball f
  exact ⟨u, u.2, fun φ hφ => weak_of_isWeak hu φ hφ⟩

theorem gen_bound (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    {f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    {w : W1p (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2}
    (hw : w ∈ w1p0Submodule (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2)
    (heq : ∀ φ : W1p (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2,
        φ ∈ w1p0Submodule (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 →
        ∫ x in Omega, matrixBilinearForm (a x) (W1p.gradient φ x) (W1p.gradient w x) =
          ∫ x in Omega, f x * W1p.value φ x) :
    (lam ^ 2 - 0 ^ 2 * (2 * R) ^ 2) / (2 * lam * ((2 * R) ^ 2 + 1)) * ‖w‖ ≤ ‖f‖ := by
  have hlow := UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_subset_ball
    (b := 0) (c := 0) (beta := 0) (gamma := 0) h ha aestronglyMeasurable_const
    aestronglyMeasurable_const (by simp) (by simp) (by simp) hball hw
  rw [energyFormH1_zero_eq, heq w hw] at hlow
  have hin : ∫ x in Omega, f x * W1p.value w x = inner ℝ f (W1p.value w) := by
    rw [L2.inner_def]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp [RCLike.inner_apply, mul_comm])
  rw [hin] at hlow
  have hle : inner ℝ f (W1p.value w) ≤ ‖f‖ * ‖w‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (W1p.norm_value_le w)
      (norm_nonneg f))
  set C := (lam ^ 2 - 0 ^ 2 * (2 * R) ^ 2) / (2 * lam * ((2 * R) ^ 2 + 1))
  rcases eq_or_lt_of_le (norm_nonneg w) with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg f
  · have : C * ‖w‖ * ‖w‖ ≤ ‖f‖ * ‖w‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

end Gen

end OAI.AnisotropicCalderon.Regularity.DC
