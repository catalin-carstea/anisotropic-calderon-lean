import Calderon.FixedDirichletRegularity
import Calderon.FixedSobolevCalculus
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Preparation of the coefficient matrix for task 05: a globally smooth copy of `a` near the
closed unit ball, and a globally uniformly elliptic, Lipschitz copy agreeing with `a` on
`B_{7/8}`. -/

noncomputable section
open MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity
open TauCeti TauCeti.PDE EnergyBridge

/-- A smooth function with compact support is Lipschitz. -/
theorem exists_lipschitzWith_of_hasCompactSupport {f : R3 → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : ∃ K : NNReal, LipschitzWith K f := by
  have hcont : Continuous (fun x => ‖fderiv ℝ f x‖₊) :=
    continuous_nnnorm.comp (hf.continuous_fderiv one_ne_zero)
  have hcs : HasCompactSupport (fun x => ‖fderiv ℝ f x‖₊) := (hc.fderiv (𝕜 := ℝ)).comp_left nnnorm_zero
  obtain ⟨K, hK⟩ := hcont.bddAbove_range_of_hasCompactSupport hcs
  exact ⟨K, lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero)
    fun x => hK ⟨x, rfl⟩⟩

/-- The smooth bump on `R3` equal to one on `closedBall 0 r` and supported in `closedBall 0 R`. -/
def bump (r R : ℝ) (hr : 0 < r) (hrR : r < R) : ContDiffBump (0 : R3) := ⟨r, R, hr, hrR⟩

@[simp] theorem bump_rIn (r R : ℝ) (hr : 0 < r) (hrR : r < R) : (bump r R hr hrR).rIn = r := rfl
@[simp] theorem bump_rOut (r R : ℝ) (hr : 0 < r) (hrR : r < R) : (bump r R hr hrR).rOut = R := rfl

theorem contDiff_entry {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {n : WithTop ℕ∞} (ha : ContDiff ℝ n a)
    (i j : Fin 3) : ContDiff ℝ n (fun x => a x i j) :=
  contDiff_pi.mp (contDiff_pi.mp ha i) j

/-- A smooth copy of `a` near the closed unit ball: `â = χ a` with a bump `χ`. -/
theorem exists_smooth_extension {a : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (ha : ContDiffOn ℝ ∞ a (closedBall 0 2)) :
    ∃ â : R3 → Matrix (Fin 3) (Fin 3) ℝ, ContDiff ℝ ∞ â ∧
      (∀ x ∈ closedBall (0 : R3) (3 / 2), â x = a x) ∧ HasCompactSupport â := by
  let χ := bump (3 / 2) (7 / 4) (by norm_num) (by norm_num)
  refine ⟨fun x => χ x • a x, ?_, fun x hx => ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x‖ < 2
    · have hmem : closedBall (0 : R3) 2 ∈ nhds x :=
        closedBall_mem_nhds_of_mem (by simpa using hx)
      exact (χ.contDiff.contDiffAt).smul (ha.contDiffAt hmem)
    · have hfar : ∀ᶠ y in nhds x, (fun y => χ y • a y) y = (fun _ => (0 : Matrix _ _ ℝ)) y := by
        have hout : x ∉ closedBall (0 : R3) (7 / 4) := by
          simp only [mem_closedBall, dist_zero_right, not_le]; linarith
        have : ∀ᶠ y in nhds x, y ∉ tsupport χ := by
          rw [χ.tsupport_eq]
          exact isClosed_closedBall.isOpen_compl.mem_nhds hout
        filter_upwards [this] with y hy
        simp [image_eq_zero_of_notMem_tsupport hy]
      exact contDiffAt_const.congr_of_eventuallyEq hfar
  · simp only
    rw [χ.one_of_mem_closedBall (by simpa [χ] using hx), one_smul]
  · refine χ.hasCompactSupport.mono' fun x hx => subset_tsupport _ ?_
    rw [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by simp only [h0, zero_smul])


theorem dotProduct_self_eq_norm_sq (ξ : R3) : ξ.ofLp ⬝ᵥ ξ.ofLp = ‖ξ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

theorem abs_dotProduct_le (η ξ : R3) : |η.ofLp ⬝ᵥ ξ.ofLp| ≤ ‖η‖ * ‖ξ‖ := by
  have := abs_real_inner_le_norm ξ η
  rw [EuclideanSpace.inner_eq_star_dotProduct] at this
  simpa [mul_comm] using this

/-- The coefficient `χ â + (1 - χ) λ I`, uniformly elliptic on all of `R3`. -/
def ellExt (â : R3 → Matrix (Fin 3) (Fin 3) ℝ) (lam : ℝ) : R3 → Matrix (Fin 3) (Fin 3) ℝ :=
  fun x => bump (7 / 8) (15 / 16) (by norm_num) (by norm_num) x • â x +
    (1 - bump (7 / 8) (15 / 16) (by norm_num) (by norm_num) x) • (lam • (1 : Matrix _ _ ℝ))

theorem ellExt_eq {â : R3 → Matrix (Fin 3) (Fin 3) ℝ} {lam : ℝ} {x : R3}
    (hx : x ∈ ball (0 : R3) (7 / 8)) : ellExt â lam x = â x := by
  have h1 : bump (7 / 8) (15 / 16) (by norm_num) (by norm_num) x = 1 :=
    ContDiffBump.one_of_mem_closedBall _ (by simpa using (mem_ball.mp hx).le)
  simp [ellExt, h1]

theorem uniformlyEllipticOn_ellExt {a â : R3 → Matrix (Fin 3) (Fin 3) ℝ} {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hâ : ∀ x ∈ closedBall (0 : R3) (3 / 2), â x = a x) :
    UniformlyEllipticOn (Set.univ : Set R3) (ellExt â lam) lam Lam := by
  obtain ⟨hlam, hlL, hx⟩ := hell
  refine ⟨hlam, hlL, fun x _ => ?_⟩
  set χ := bump (7 / 8) (15 / 16) (by norm_num) (by norm_num)
  have hc0 : 0 ≤ χ x := χ.nonneg
  have hc1 : χ x ≤ 1 := χ.le_one
  -- where `χ x ≠ 0`, `x` lies in the ball and `â x = a x` is elliptic
  have hin : χ x ≠ 0 → x ∈ (ballOpens : Set R3) ∧ â x = a x := fun h => by
    have hts : x ∈ tsupport χ := subset_tsupport _ h
    rw [χ.tsupport_eq] at hts
    have hn : ‖x‖ ≤ 15 / 16 := by simpa [χ] using hts
    refine ⟨by simp only [coe_ballOpens, B, mem_ball, dist_zero_right]; linarith,
      hâ x (by simp only [mem_closedBall, dist_zero_right]; linarith)⟩
  have hform : ∀ η ξ : R3, η.ofLp ⬝ᵥ (ellExt â lam x).mulVec ξ.ofLp =
      χ x * (η.ofLp ⬝ᵥ (â x).mulVec ξ.ofLp) + (1 - χ x) * lam * (η.ofLp ⬝ᵥ ξ.ofLp) := by
    intro η ξ
    simp only [ellExt, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul, χ]
    ring
  constructor
  · intro ξ
    rw [Matrix.toQuadraticForm'_apply, hform, dotProduct_self_eq_norm_sq]
    by_cases h : χ x = 0
    · rw [h]; nlinarith [sq_nonneg ‖ξ‖]
    · obtain ⟨hxB, heq⟩ := hin h
      have := (hx hxB).1 ξ
      rw [Matrix.toQuadraticForm'_apply, ← heq] at this
      nlinarith [sq_nonneg ‖ξ‖]
  · intro η ξ
    rw [hform]
    have hdot := abs_dotProduct_le η ξ
    have hnn : 0 ≤ ‖η‖ * ‖ξ‖ := by positivity
    by_cases h : χ x = 0
    · rw [h, zero_mul, zero_add, sub_zero, one_mul, abs_mul, abs_of_pos hlam]
      calc lam * |η.ofLp ⬝ᵥ ξ.ofLp| ≤ lam * (‖η‖ * ‖ξ‖) := by gcongr
        _ ≤ Lam * ‖η‖ * ‖ξ‖ := by nlinarith
    · obtain ⟨hxB, heq⟩ := hin h
      have hb := (hx hxB).2 η ξ
      rw [← heq] at hb
      calc |χ x * (η.ofLp ⬝ᵥ (â x).mulVec ξ.ofLp) + (1 - χ x) * lam * (η.ofLp ⬝ᵥ ξ.ofLp)|
          ≤ |χ x * (η.ofLp ⬝ᵥ (â x).mulVec ξ.ofLp)| + |(1 - χ x) * lam * (η.ofLp ⬝ᵥ ξ.ofLp)| :=
            abs_add_le _ _
        _ = χ x * |η.ofLp ⬝ᵥ (â x).mulVec ξ.ofLp| + (1 - χ x) * lam * |η.ofLp ⬝ᵥ ξ.ofLp| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc0,
              abs_of_nonneg (sub_nonneg.mpr hc1), abs_of_pos hlam]
        _ ≤ χ x * (Lam * ‖η‖ * ‖ξ‖) + (1 - χ x) * lam * (‖η‖ * ‖ξ‖) := by
            gcongr
        _ ≤ Lam * ‖η‖ * ‖ξ‖ := by nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hnn]

theorem contDiff_ellExt {â : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hâ : ContDiff ℝ ∞ â) (lam : ℝ) :
    ContDiff ℝ ∞ (ellExt â lam) :=
  ((ContDiffBump.contDiff _).smul hâ).add
    ((contDiff_const.sub (ContDiffBump.contDiff _)).smul contDiff_const)

/-- Entries of a smooth matrix field with compact support are Lipschitz, uniformly. -/
theorem exists_lipschitz_entries {â : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hâ : ContDiff ℝ ∞ â)
    (hc : HasCompactSupport â) : ∃ K : NNReal, ∀ i j, LipschitzWith K (fun x => â x i j) := by
  have h : ∀ i j, ∃ K : NNReal, LipschitzWith K (fun x => â x i j) := fun i j =>
    exists_lipschitzWith_of_hasCompactSupport ((contDiff_entry hâ i j).of_le (by simp))
      (hc.comp_left (g := fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) rfl)
  choose K hK using h
  refine ⟨∑ i, ∑ j, K i j, fun i j => (hK i j).weaken ?_⟩
  exact (Finset.single_le_sum (fun j _ => (K i j).zero_le_coe) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, K i j) (fun i _ => (∑ j, K i j).zero_le_coe) (Finset.mem_univ i))

theorem exists_lipschitz_ellExt {â : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hâ : ContDiff ℝ ∞ â)
    (lam : ℝ) : ∃ K : NNReal, ∀ i j, LipschitzWith K (fun x => ellExt â lam x i j) := by
  -- `ellExt â lam - λ I` is smooth with compact support
  set χ := bump (7 / 8) (15 / 16) (by norm_num) (by norm_num)
  have hdiff : ContDiff ℝ ∞ (fun x => ellExt â lam x - lam • (1 : Matrix (Fin 3) (Fin 3) ℝ)) :=
    (contDiff_ellExt hâ lam).sub contDiff_const
  have hcs : HasCompactSupport
      (fun x => ellExt â lam x - lam • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
    refine χ.hasCompactSupport.mono' fun x hx => subset_tsupport _ ?_
    rw [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    simp only [ellExt, χ] at h0 ⊢
    rw [h0]
    simp
  obtain ⟨K, hK⟩ := exists_lipschitz_entries hdiff hcs
  refine ⟨K, fun i j => ?_⟩
  have := (hK i j).add (LipschitzWith.const (α := R3) ((lam • (1 : Matrix (Fin 3) (Fin 3) ℝ)) i j))
  simpa using this

end OAI.AnisotropicCalderon.Regularity
