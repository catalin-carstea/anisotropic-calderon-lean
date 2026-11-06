import Calderon.CollaboratorLocalJetsOpsOct17
import Calderon.CollaboratorLocalSobolevRawTwoJetBoundOct17

/-! The perturbative step of Lassas–Liimatainen–Salo, Prop. A.5 (Step 2): local solutions whose
2-jets approximate a prescribed compatible jet. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory TopologicalSpace Metric Set
open scoped InnerProductSpace ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity.Jets
open TauCeti TauCeti.PDE EnergyBridge

theorem norm_iteratedFDeriv_const_mul_le {g : R3 → ℝ} (hg : ContDiff ℝ ∞ g) (a : ℝ) (j : ℕ)
    (y : R3) :
    ‖iteratedFDeriv ℝ j (fun y => a * g y) y‖ ≤ |a| * ‖iteratedFDeriv ℝ j g y‖ := by
  have h : (fun y => a * g y) = a • g := rfl
  rw [h, iteratedFDeriv_const_smul_apply (hg.contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul, Real.norm_eq_abs]

theorem uniformlyEllipticOn_rescale {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} {p : R3} {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (closedBall p 1) A lam Lam) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    UniformlyEllipticOn (ballOpens : Set R3) (fun y => A (p + ε • y)) lam Lam := by
  refine ⟨hell.1, hell.2.1, fun y hy => hell.2.2 ?_⟩
  have hy' : ‖y‖ < 1 := by simpa [B] using hy
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos hε]
  nlinarith [norm_nonneg y]

theorem uniformlyEllipticOn_const {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} {p : R3} {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (closedBall p 1) A lam Lam) :
    UniformlyEllipticOn (ballOpens : Set R3) (fun _ => A p) lam Lam :=
  ⟨hell.1, hell.2.1, fun _ _ => hell.2.2 (mem_closedBall_self zero_le_one)⟩

/-- Uniform derivative bounds for the entries of `A` near `p`. -/
theorem exists_entry_bound {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A) (p : R3) :
    ∃ KA : ℝ, 0 ≤ KA ∧ ∀ i k : Fin 3, ∀ j ≤ 5, ∀ x ∈ closedBall p 2,
      ‖iteratedFDeriv ℝ j (fun x => A x i k) x‖ ≤ KA := by
  have h : ∀ i k : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ 5, ∀ x ∈ closedBall p 2,
      ‖iteratedFDeriv ℝ j (fun x => A x i k) x‖ ≤ C := fun i k =>
    exists_bound_iteratedFDeriv (G := fun x => A x i k)
      (contDiff_entry hA i k) (isCompact_closedBall p 2) 5
  choose C hC0 hC using h
  refine ⟨∑ i, ∑ k, C i k, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hC0 i k,
    fun i k j hj x hx => (hC i k j hj x hx).trans ?_⟩
  calc C i k ≤ ∑ k', C i k' :=
        Finset.single_le_sum (f := fun k' => C i k') (fun k' _ => hC0 i k') (Finset.mem_univ k)
    _ ≤ ∑ i', ∑ k', C i' k' :=
        Finset.single_le_sum (f := fun i' => ∑ k', C i' k')
          (fun i' _ => Finset.sum_nonneg fun k' _ => hC0 i' k') (Finset.mem_univ i)

theorem contDiff_affine (p : R3) (ε : ℝ) : ContDiff ℝ ∞ (fun y : R3 => p + ε • y) :=
  contDiff_const.add (contDiff_const_smul ε)

/-- **Step 2 of Prop. A.5.** On the unit ball, after rescaling `x = p + ε y`, the polynomial with
a compatible jet `c` is corrected by `w` to a solution, with the 2-jet of `w` at the centre of
size `O(ε³ ‖c‖)`. -/
theorem key {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
    (hpos : ∀ x, (A x).PosDef) (p : R3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ c : J, (∀ v w, c.2.2 v w = c.2.2 w v) → Γ A p p c = 0 →
      ∃ w : R3 → ℝ, ContDiffOn ℝ ∞ w B ∧
        (∀ y ∈ B, divCoeffGrad (fun y => A (p + ε • y))
          (fun y => quad p c (p + ε • y) + w y) y = 0) ∧
        ‖jet w 0‖ ≤ K * ε ^ 3 * ‖c‖ := by
  obtain ⟨lam, Lam, hell⟩ :=
    exists_uniformlyEllipticOn hA.continuous hpos (isCompact_closedBall p 1)
  obtain ⟨C₀, hC₀, hbnd⟩ := exists_const_bound (A p) (uniformlyEllipticOn_const hell)
  obtain ⟨CP, hCP, hpert⟩ := exists_pert_op
  obtain ⟨CF, hCF, hforc⟩ := exists_wkp3_bound
  obtain ⟨KA, hKA, hKAb⟩ := exists_entry_bound hA p
  obtain ⟨KΓ, hKΓ, hKΓb⟩ := norm_iteratedFDeriv_Γ_le hA p
  obtain ⟨CJ, hCJ, hjet⟩ := ExteriorSource.Literature.localSobolevRawTwoJetBound 0 1 one_pos
  refine ⟨CJ * (2 * C₀) * (CF * (2 * KΓ)), by positivity,
    min 1 (1 / (4 * C₀ * CP * KA + 1)), by positivity, min_le_left _ _, ?_⟩
  intro ε hε hεε₀ c hH hΓ
  have hε1 : ε ≤ 1 := hεε₀.trans (min_le_left _ _)
  have hεs : ε ≤ 1 / (4 * C₀ * CP * KA + 1) := hεε₀.trans (min_le_right _ _)
  -- the rescaled coefficient and its deviation from `A p`
  have ha : ContDiff ℝ ∞ (fun y => A (p + ε • y)) := hA.comp (contDiff_affine p ε)
  have hella := uniformlyEllipticOn_rescale hell hε hε1
  have hM : ContDiff ℝ ∞ (fun y => A (p + ε • y) - A p) := ha.sub contDiff_const
  have hMb : ∀ i k : Fin 3, ∀ j ≤ 5, ∀ y ∈ closedBall (0 : R3) 2,
      ‖iteratedFDeriv ℝ j (fun y => (A (p + ε • y) - A p) i k) y‖ ≤ 2 * KA * ε := by
    intro i k
    exact norm_iteratedFDeriv_rescale_le (contDiff_entry hA i k)
      (fun j hj x hx => hKAb i k j hj x hx) (by norm_num) hε hε1
  obtain ⟨T, hT, hTeq⟩ := hpert _ hM (2 * KA * ε) (by positivity) hMb
  -- the forcing `g = div(a ∇ q)`
  have hG : ContDiff ℝ ∞ (fun x => Γ A p x c) := (contDiff_Γ hA p).clm_apply contDiff_const
  have hGa : ContDiff ℝ ∞ (fun y => Γ A p (p + ε • y) c) := hG.comp (contDiff_affine p ε)
  have hg : ContDiff ℝ ∞ (fun y => ε ^ 2 * Γ A p (p + ε • y) c) := contDiff_const.mul hGa
  have hgb : ∀ j ≤ 4, ∀ y ∈ closedBall (0 : R3) 2,
      ‖iteratedFDeriv ℝ j (fun y => ε ^ 2 * Γ A p (p + ε • y) c) y‖ ≤
        ε ^ 2 * (2 * (KΓ * ‖c‖) * ε) := by
    intro j hj y hy
    have h1 := norm_iteratedFDeriv_rescale_le hG (K := KΓ * ‖c‖)
      (fun j hj x hx => hKΓb c j hj x hx) (by norm_num : 1 ≤ 5) hε hε1 j (by omega) y hy
    have hgg : (fun y => ε ^ 2 * Γ A p (p + ε • y) c) =
        fun y => ε ^ 2 * (Γ A p (p + ε • y) c - Γ A p p c) := by
      funext y; rw [hΓ, sub_zero]
    rw [hgg]
    refine (norm_iteratedFDeriv_const_mul_le (hGa.sub contDiff_const) _ j y).trans ?_
    rw [abs_of_nonneg (by positivity)]
    gcongr
  obtain ⟨fg, hfg, hfgn⟩ := hforc _ hg _ (by positivity) hgb
  -- the weak solution and its regularity
  obtain ⟨u, hu0, hu⟩ := exists_weakEq ha.continuous hella (Wkp.value 3 fg)
  have hFall : ∀ m, Wkp.value 3 fg ∈ HO.Hs m := by
    intro m
    obtain ⟨fm, hfm⟩ := exists_wkp_of_contDiff m hg
    exact HO.mem_Hs.mpr ⟨fm, Lp.ext (hfm.trans hfg.symm)⟩
  have hall := value_mem_Hs_all ha hella hFall hu0 hu
  obtain ⟨W, hW⟩ := HO.exists_of_value_mem_Hs 4 u (hall 5)
  -- the constant-coefficient equation and absorption
  have hu' : WeakEq (fun _ => A p) (Wkp.value 3 (fg + T W)) (Wkp.firstOrder 4 W) := by
    have h := weakEq_sub_pert ha.continuous hM.continuous hu (G := Wkp.value 3 (T W))
      (fun φ => by rw [← hW]; exact hTeq W φ)
    have hfun : (fun x => A (p + ε • x) - (A (p + ε • x) - A p)) = fun _ => A p := by
      funext x; rw [sub_sub_cancel]
    rw [hfun] at h
    rw [hW, Wkp.value_add]
    exact h
  have hWb := hbnd (fg + T W) W (hW ▸ hu0) hu'
  have hWle : ‖W‖ ≤ 2 * C₀ * ‖fg‖ := by
    have h1 : ‖fg + T W‖ ≤ ‖fg‖ + CP * (2 * KA * ε) * ‖W‖ :=
      (norm_add_le _ _).trans (by
        gcongr
        exact (T.le_opNorm W).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _)))
    have h2 : C₀ * (CP * (2 * KA * ε)) ≤ 1 / 2 := by
      have hpos' : 0 < 4 * C₀ * CP * KA + 1 := by positivity
      have h3 : ε * (4 * C₀ * CP * KA + 1) ≤ 1 := by
        rw [le_div_iff₀ hpos'] at hεs; linarith
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC₀ hCP) hKA) hε.le]
    have h4 : ‖W‖ ≤ C₀ * ‖fg‖ + C₀ * (CP * (2 * KA * ε)) * ‖W‖ := by
      calc ‖W‖ ≤ C₀ * ‖fg + T W‖ := hWb
        _ ≤ C₀ * (‖fg‖ + CP * (2 * KA * ε) * ‖W‖) := by gcongr
        _ = _ := by ring
    nlinarith [norm_nonneg W, norm_nonneg fg]
  -- the smooth representative
  obtain ⟨w, hw, hwu⟩ := exists_smooth_rep hall
  refine ⟨w, hw, ?_, ?_⟩
  · have hq : ContDiff ℝ ∞ (fun y => quad p c (p + ε • y)) :=
      (contDiff_quad p c).comp (contDiff_affine p ε)
    refine divCoeffGrad_eq_zero_of_sum ha hq (fun y _ => ?_) hfg hu hw hwu
    rw [divCoeffGrad_comp_affine A (quad p c) p hε.ne' y, divCoeffGrad_quad hA p hH]
  · have hv : (Wkp.value 5 W : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens] w := by
      rw [← Wkp.value_firstOrder, hW]; exact hwu.symm
    have hj : ‖jet w 0‖ ≤ CJ * ‖W‖ := hjet W w hw hv
    calc ‖jet w 0‖ ≤ CJ * ‖W‖ := hj
      _ ≤ CJ * (2 * C₀ * (CF * (ε ^ 2 * (2 * (KΓ * ‖c‖) * ε)))) := by
        gcongr
        exact hWle.trans (by gcongr)
      _ = _ := by ring

theorem norm_jet_rescale_le (j : J) {t : ℝ} (ht : 1 ≤ t) :
    ‖((j.1, t • j.2.1, t ^ 2 • j.2.2) : J)‖ ≤ t ^ 2 * ‖j‖ := by
  have ht0 : 0 ≤ t := by linarith
  have ht2 : t ≤ t ^ 2 := by nlinarith
  have h1 : ‖j.1‖ ≤ ‖j‖ := norm_fst_le j
  have h2 : ‖j.2.1‖ ≤ ‖j‖ := (norm_fst_le j.2).trans (norm_snd_le j)
  have h3 : ‖j.2.2‖ ≤ ‖j‖ := (norm_snd_le j.2).trans (norm_snd_le j)
  have hj0 : 0 ≤ ‖j‖ := norm_nonneg j
  refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · nlinarith
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]; nlinarith
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; nlinarith

/-- **Step 2 of Prop. A.5, unscaled.** There is a radius `ρ` such that every compatible jet is
approximated, up to half its size, by the jet of a solution on `ball p ρ`. -/
theorem approx {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
    (hpos : ∀ x, (A x).PosDef) (p : R3) :
    ∃ ρ > 0, ∀ c : J, (∀ v w, c.2.2 v w = c.2.2 w v) → Γ A p p c = 0 →
      ∃ u : R3 → ℝ, ContDiffOn ℝ ∞ u (ball p ρ) ∧ (∀ x ∈ ball p ρ, divCoeffGrad A u x = 0) ∧
        ‖jet u p - c‖ ≤ 1 / 2 * ‖c‖ := by
  obtain ⟨K, hK, ε₀, hε₀, hε₀1, hkey⟩ := key hA hpos p
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min ε₀ (1 / (2 * K + 1)) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hεε₀ : ε ≤ ε₀ := hεdef ▸ min_le_left _ _
  have hεK : ε ≤ 1 / (2 * K + 1) := hεdef ▸ min_le_right _ _
  have hε1 : ε ≤ 1 := hεε₀.trans hε₀1
  refine ⟨ε, hε, fun c hH hΓ => ?_⟩
  obtain ⟨w, hw, heq, hjw⟩ := hkey ε hε hεε₀ c hH hΓ
  have hεi : ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
  have hL : ∀ x : R3, p + ε • (-(ε⁻¹ • p) + ε⁻¹ • x) = x := fun x => by
    rw [smul_add, smul_neg, smul_smul, smul_smul, mul_inv_cancel₀ hε.ne', one_smul, one_smul]
    abel
  have hLB : ∀ x ∈ ball p ε, -(ε⁻¹ • p) + ε⁻¹ • x ∈ B := fun x hx => by
    have : -(ε⁻¹ • p) + ε⁻¹ • x = ε⁻¹ • (x - p) := by rw [smul_sub]; abel
    rw [this]
    simp only [B, mem_ball, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hε]
    rw [mem_ball, dist_eq_norm] at hx
    rw [inv_mul_lt_iff₀ hε, mul_one]; exact hx
  have hBo : IsOpen B := isOpen_ball
  have h0 : -(ε⁻¹ • p) + ε⁻¹ • p = 0 := neg_add_cancel _
  have hw0 : ContDiffAt ℝ 2 (fun x => w (-(ε⁻¹ • p) + ε⁻¹ • x)) p := by
    have h1 : ContDiffAt ℝ 2 w (-(ε⁻¹ • p) + ε⁻¹ • p) := by
      rw [h0]
      exact (hw.contDiffAt (hBo.mem_nhds (by simp [B]))).of_le (by simp)
    exact h1.comp p ((contDiff_affine _ _).contDiffAt.of_le (by simp))
  refine ⟨fun x => quad p c x + w (-(ε⁻¹ • p) + ε⁻¹ • x), ?_, ?_, ?_⟩
  · exact (contDiff_quad p c).contDiffOn.add
      (hw.comp (contDiff_affine _ _).contDiffOn fun x hx => hLB x hx)
  · intro x hx
    have h := divCoeffGrad_comp_affine (fun y => A (p + ε • y))
      (fun y => quad p c (p + ε • y) + w y) (-(ε⁻¹ • p)) hεi x
    simp only [hL] at h
    rw [heq _ (hLB x hx), mul_zero] at h
    exact h
  · have hj : jet (fun x => quad p c x + w (-(ε⁻¹ • p) + ε⁻¹ • x)) p =
        jet (quad p c) p + jet (fun x => w (-(ε⁻¹ • p) + ε⁻¹ • x)) p :=
      jet_add (((contDiff_quad p c).contDiffAt).of_le (by simp)) hw0
    rw [hj, jet_quad p hH, add_sub_cancel_left, jet_comp_affine w _ hεi p, h0]
    have hε1' : 1 ≤ ε⁻¹ := by rw [le_inv_comm₀ one_pos hε, inv_one]; exact hε1
    refine (norm_jet_rescale_le (jet w 0) hε1').trans ?_
    have hc0 := norm_nonneg c
    calc ε⁻¹ ^ 2 * ‖jet w 0‖ ≤ ε⁻¹ ^ 2 * (K * ε ^ 3 * ‖c‖) := by gcongr
      _ = K * ε * ‖c‖ := by field_simp
      _ ≤ 1 / 2 * ‖c‖ := by
        gcongr
        rw [le_div_iff₀ (by positivity)] at hεK
        nlinarith

/-! ### Step 3: exact jets by finite dimensionality -/

/-- The compatible jets at `p`. -/
def compatSub (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (p : R3) : Submodule ℝ J where
  carrier := {c | (∀ v w, c.2.2 v w = c.2.2 w v) ∧ Γ A p p c = 0}
  add_mem' := fun {c d} hc hd => ⟨fun v w => by
      simp only [Prod.snd_add, add_apply, hc.1 v w, hd.1 v w],
    by rw [map_add, hc.2, hd.2, add_zero]⟩
  zero_mem' := ⟨fun v w => by simp, by rw [map_zero]⟩
  smul_mem' := fun t c hc => ⟨fun v w => by
      simp only [Prod.smul_snd, smul_apply, hc.1 v w],
    by rw [map_smul, hc.2, smul_zero]⟩

theorem mem_compatSub {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} {p : R3} {c : J} :
    c ∈ compatSub A p ↔ (∀ v w, c.2.2 v w = c.2.2 w v) ∧ Γ A p p c = 0 := Iff.rfl

theorem contDiffAt_two_of_ball {u : R3 → ℝ} {p : R3} {ρ : ℝ}
    (hu : ContDiffOn ℝ ∞ u (ball p ρ)) {x : R3} (hx : x ∈ ball p ρ) : ContDiffAt ℝ 2 u x :=
  (hu.contDiffAt (isOpen_ball.mem_nhds hx)).of_le (by simp)

/-- The 2-jets at `p` of solutions on `ball p ρ`. -/
def solSub {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A) (p : R3) {ρ : ℝ}
    (hρ : 0 < ρ) : Submodule ℝ J where
  carrier := {j | ∃ u : R3 → ℝ, ContDiffOn ℝ ∞ u (ball p ρ) ∧
    (∀ x ∈ ball p ρ, divCoeffGrad A u x = 0) ∧ jet u p = j}
  add_mem' := by
    rintro _ _ ⟨u, hu, hue, rfl⟩ ⟨v, hv, hve, rfl⟩
    refine ⟨u + v, hu.add hv, fun x hx => ?_, jet_add (contDiffAt_two_of_ball hu
      (mem_ball_self hρ)) (contDiffAt_two_of_ball hv (mem_ball_self hρ))⟩
    rw [divCoeffGrad_add ((hA.differentiable (by simp)) x) (contDiffAt_two_of_ball hu hx)
      (contDiffAt_two_of_ball hv hx), hue x hx, hve x hx, add_zero]
  zero_mem' := by
    refine ⟨0, contDiffOn_const, fun x _ => ?_, jet_zero p⟩
    have h := divCoeffGrad_smul (A := A) (u := (0 : R3 → ℝ)) 0
      ((hA.differentiable (by simp)) x) contDiffAt_const
    rwa [zero_smul, zero_mul] at h
  smul_mem' := by
    rintro t _ ⟨u, hu, hue, rfl⟩
    refine ⟨t • u, hu.const_smul t, fun x hx => ?_,
      jet_smul t (contDiffAt_two_of_ball hu (mem_ball_self hρ))⟩
    rw [divCoeffGrad_smul t ((hA.differentiable (by simp)) x) (contDiffAt_two_of_ball hu hx),
      hue x hx, mul_zero]

theorem mem_solSub {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} {hA : ContDiff ℝ ∞ A} {p : R3} {ρ : ℝ}
    {hρ : 0 < ρ} {j : J} :
    j ∈ solSub hA p hρ ↔ ∃ u : R3 → ℝ, ContDiffOn ℝ ∞ u (ball p ρ) ∧
      (∀ x ∈ ball p ρ, divCoeffGrad A u x = 0) ∧ jet u p = j := Iff.rfl

theorem solSub_le_compatSub {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A) (p : R3)
    {ρ : ℝ} (hρ : 0 < ρ) : solSub hA p hρ ≤ compatSub A p := by
  rintro _ ⟨u, hu, hue, rfl⟩
  have hp := contDiffAt_two_of_ball hu (mem_ball_self hρ)
  refine ⟨jet_symm hp, ?_⟩
  rw [Γ_apply_self, ← hue p (mem_ball_self hρ),
    divCoeffGrad_eq_jet ((hA.differentiable (by simp)) p) hp]
  rfl

/-- **Step 3 of Prop. A.5.** On a suitable ball, every compatible 2-jet is the jet of a
solution: the solution jets form a subspace of the finite-dimensional space of compatible jets
that approximates every compatible jet within half its norm (Riesz's lemma). -/
theorem exists_radius_compatSub_le_solSub {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ContDiff ℝ ∞ A) (hpos : ∀ x, (A x).PosDef) (p : R3) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ, compatSub A p ≤ solSub hA p hρ := by
  obtain ⟨ρ, hρ, happrox⟩ := approx hA hpos p
  refine ⟨ρ, hρ, fun c hcC => ?_⟩
  by_contra hcS
  let C := compatSub A p
  let F : Submodule ℝ C := (solSub hA p hρ).comap C.subtype
  have hF : IsClosed (F : Set C) := Submodule.closed_of_finiteDimensional F
  obtain ⟨x₀, hx₀F, hx₀⟩ := riesz_lemma hF ⟨⟨c, hcC⟩, hcS⟩ (r := 3 / 4) (by norm_num)
  obtain ⟨u, hu, hue, hun⟩ := happrox x₀.1 x₀.2.1 x₀.2.2
  have hsS : jet u p ∈ solSub hA p hρ := ⟨u, hu, hue, rfl⟩
  let y : C := ⟨jet u p, solSub_le_compatSub hA p hρ hsS⟩
  have hy : y ∈ F := hsS
  have h1 := hx₀ y hy
  have h2 : ‖x₀ - y‖ = ‖jet u p - (x₀ : J)‖ := by
    rw [← norm_neg, neg_sub]; rfl
  have h3 : ‖x₀‖ = ‖(x₀ : J)‖ := rfl
  rw [h2] at h1
  have h4 : ‖x₀‖ = 0 := by nlinarith [norm_nonneg x₀]
  rw [norm_eq_zero] at h4
  apply hx₀F
  rw [h4]
  exact F.zero_mem

end OAI.AnisotropicCalderon.Regularity.Jets
