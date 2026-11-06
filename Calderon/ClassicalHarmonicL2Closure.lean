import Calderon.FiniteHarmonicProductL2Limit
import Calderon.CollaboratorUCPLocalOct17
import Calderon.CollaboratorAffineSobolevOct17
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Sequences

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set Filter TopologicalSpace
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise ENNReal
namespace OAI.AnisotropicCalderon.Regularity
open EnergyBridge

theorem exists_contDiffOn_of_tendsto_L2_classical_harmonic_on_unitBall
    {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ContDiff ℝ ∞ A) (hpos : ∀ x, (A x).PosDef)
    (u : ℕ → R3 → ℝ)
    (hu : ∀ j, ContDiffOn ℝ ∞ (u j) (ball (0 : R3) 2))
    (hP : ∀ j, ∀ x ∈ (ballOpens : Set R3), divCoeffGrad A (u j) x = 0)
    (v : ℕ → Lp ℝ 2 ((volume : Measure R3).restrict (ballOpens : Set R3)))
    (w : Lp ℝ 2 ((volume : Measure R3).restrict (ballOpens : Set R3)))
    (hv : ∀ j, (v j : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict (ballOpens : Set R3)] u j)
    (hlim : Tendsto v atTop (𝓝 w)) :
    ∃ U : R3 → ℝ, ContDiffOn ℝ ∞ U (ball (0 : R3) (1/4 : ℝ)) ∧
      U =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) (1/4 : ℝ))] (w : R3 → ℝ) ∧
      ∀ x ∈ ball (0 : R3) (1/4 : ℝ), divCoeffGrad A U x = 0
 := by
  classical
  let ν : Measure R3 := (volume : Measure R3).restrict (ballOpens : Set R3)
  let μ : Measure (R3 × R3) := ν.prod ν
  let V : Set R3 := ball (0 : R3) (1/4 : ℝ)
  have hνfinite : (volume : Measure R3) (ballOpens : Set R3) ≠ ⊤ := by
    change (volume : Measure R3) (ball (0 : R3) 1) ≠ ⊤
    exact measure_ball_ne_top
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hνfinite
  let lift : Lp ℝ 2 ν → Lp ℝ 2 μ :=
    fun q => ((Lp.memLp q).comp_fst ν).toLp (fun p : R3 × R3 => q p.1)
  have hLift (q : Lp ℝ 2 ν) :
      (lift q : R3 × R3 → ℝ) =ᵐ[μ] fun p => q p.1 :=
    ((Lp.memLp q).comp_fst ν).coeFn_toLp
  have hLiftSub (q r : Lp ℝ 2 ν) : lift (q-r) = lift q-lift r := by
    apply Lp.ext
    filter_upwards [hLift (q-r), hLift q, hLift r, Lp.coeFn_sub (lift q) (lift r),
      (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae (Lp.coeFn_sub q r)]
      with p h1 h2 h3 h4 h5
    rw [h1, h4, Pi.sub_apply, h2, h3]
    exact h5
  have hNormSq (q : Lp ℝ 2 ν) : ‖lift q‖^2 = (ν Set.univ).toReal * ‖q‖^2 := by
    calc
      ‖lift q‖^2 = ∫ p, (lift q p)^2 ∂μ := by
        simpa only [L2.inner_def, Real.inner_apply, ← pow_two] using
          (real_inner_self_eq_norm_sq (lift q)).symm
      _ = ∫ p : R3 × R3, (q p.1)^2 * (1 : ℝ) ∂ν.prod ν := by
        apply integral_congr_ae
        filter_upwards [hLift q] with p hp
        simp only [hp, mul_one]
      _ = (∫ x, (q x)^2 ∂ν) * (ν Set.univ).toReal := by
        calc
          _ = (∫ x : R3, (q x)^2 ∂ν) * (∫ _y : R3, (1 : ℝ) ∂ν) :=
            integral_prod_mul (μ := ν) (ν := ν)
              (fun x : R3 => (q x)^2) (fun _y : R3 => (1 : ℝ))
          _ = (∫ x : R3, (q x)^2 ∂ν) * (ν Set.univ).toReal := by
            rw [integral_const, smul_eq_mul, mul_one, measureReal_def]
      _ = (ν Set.univ).toReal * ‖q‖^2 := by
        have hq : (∫ x, (q x)^2 ∂ν) = ‖q‖^2 := by
          simpa only [L2.inner_def, Real.inner_apply, ← pow_two]
            using real_inner_self_eq_norm_sq q
        rw [hq, mul_comm]
  have hNorm (q : Lp ℝ 2 ν) : ‖lift q‖ = Real.sqrt (ν Set.univ).toReal * ‖q‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
    exact hNormSq q
  have hLiftLim : Tendsto (fun j => lift (v j)) atTop (𝓝 (lift w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have he : (fun j => ‖lift (v j)-lift w‖) =
        (fun j => Real.sqrt (ν Set.univ).toReal * ‖v j-w‖) := by
      funext j
      rw [← hLiftSub, hNorm]
    rw [he]
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hlim))
  have hProdVal (j : ℕ) :
      (lift (v j) : R3 × R3 → ℝ) =ᵐ[μ]
        (fun p => ∑ _i : Fin 1, u j p.1 * (1 : ℝ)) := by
    filter_upwards [hLift (v j),
      (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae (hv j)] with p hp hvp
    simpa only [Finset.univ_unique, Finset.sum_singleton, mul_one] using hp.trans hvp
  obtain ⟨H, hH, hHW, hHP, _hHP2, _hJets⟩ :=
    exists_contDiffOn_of_tendsto_L2_harmonic_product_sums hA hpos
      (A2 := fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ)) contDiff_const
      (fun _ => Matrix.PosDef.one) (fun _ => 1)
      (fun j _ => u j) (fun _ _ _ => (1 : ℝ)) (fun j _ => hu j)
      (fun j _ => hP j) (fun _ _ => contDiffOn_const)
      (by intro j i x hx; simp [divCoeffGrad])
      (fun j => lift (v j)) (lift w) hProdVal hLiftLim
  have hVU : V ⊆ (ballOpens : Set R3) :=
    ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1)
  let σ : Measure R3 := (volume : Measure R3).restrict V
  have hMeasure : μ.restrict (V ×ˢ V) = σ.prod σ := by
    dsimp only [μ, σ]
    rw [← Measure.prod_restrict]
    simp only [ν, Measure.restrict_restrict_of_subset hVU]
  have hSliceProd : H =ᵐ[σ.prod σ] fun p => w p.1 := by
    have hwLift := ae_restrict_of_ae (s := V ×ˢ V) (hLift w)
    rw [hMeasure] at hwLift
    have hH' : H =ᵐ[σ.prod σ] (lift w : R3 × R3 → ℝ) := by
      rw [← hMeasure]
      exact hHW
    exact hH'.trans hwLift
  have hSwap : (fun p : R3 × R3 => H (p.2,p.1)) =ᵐ[σ.prod σ]
      (fun p => w p.2) :=
    (Measure.measurePreserving_swap (μ := σ) (ν := σ)).quasiMeasurePreserving.ae hSliceProd
  have hSlices : ∀ᵐ y ∂σ, (fun x => H (x,y)) =ᵐ[σ] (w : R3 → ℝ) :=
    Measure.ae_ae_of_ae_prod hSwap
  have hVpos : (volume : Measure R3) V ≠ 0 := by
    exact (isOpen_ball.measure_pos volume ⟨0, mem_ball_self (by norm_num)⟩).ne'
  have hσne : σ ≠ 0 := by
    intro he
    have hm := congrArg (fun η : Measure R3 => η Set.univ) he
    apply hVpos
    simpa only [σ, Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using hm
  letI : NeZero σ := ⟨hσne⟩
  obtain ⟨y, hy, hySlice⟩ :=
    ((ae_restrict_mem measurableSet_ball).and hSlices).exists
  refine ⟨fun x => H (x,y), ?_, hySlice, ?_⟩
  · exact hH.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => ⟨hx, hy⟩)
  · intro x hx
    exact hHP (x,y) ⟨hx, hy⟩

theorem exists_contDiffOn_representative_of_mem_closure_L2_classical_harmonics
    (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (w : Lp ℝ 2 ((volume : Measure R3).restrict D))
    (hw : w ∈ closure {v : Lp ℝ 2 ((volume : Measure R3).restrict D) |
      ∃ u : R3 → ℝ, ContDiffOn ℝ ∞ u D ∧
        (∀ x ∈ D, divCoeffGrad A u x = 0) ∧
        (v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict D] u}) :
    ∃ U : R3 → ℝ, ContDiffOn ℝ ∞ U D ∧
      U =ᵐ[(volume : Measure R3).restrict D] (w : R3 → ℝ) ∧
      ∀ x ∈ D, divCoeffGrad A U x = 0
 := by
  classical
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp hw
  choose u hu hPu hval using hv
  have hlocal : ∀ c ∈ D, ∃ r > 0, ball c r ⊆ D ∧
      ∃ U : R3 → ℝ, ContDiffOn ℝ ∞ U (ball c r) ∧
        U =ᵐ[(volume : Measure R3).restrict (ball c r)] (w : R3 → ℝ) ∧
        ∀ x ∈ ball c r, divCoeffGrad A U x = 0 := by
    intro c hc
    obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD c hc
    let ρ : ℝ := ε/8
    have hρ : 0 < ρ := by dsimp only [ρ]; positivity
    have hRoom : closedBall c (2*(2*ρ)) ⊆ D := by
      apply Set.Subset.trans (closedBall_subset_ball (by dsimp only [ρ]; linarith)) hεD
    obtain ⟨Ahat, hAhat, hposhat, hEq⟩ :=
      UCP.exists_global_coeff hD hA hpos (by positivity : 0 < 2*ρ) hRoom
    let Ω : Opens R3 := Affine.ballO c ρ
    let Ωq : Opens R3 := Affine.ballO c (ρ/4)
    let Vq : Opens R3 := Affine.ballO (0 : R3) (1/4)
    have hΩD : (Ω : Set R3) ⊆ D := by
      exact (ball_subset_ball (by dsimp only [ρ]; linarith : ρ ≤ ε)).trans hεD
    have hAff : Affine.IsAff Ω ballOpens c ρ := by
      intro z
      change c+ρ • z ∈ ball c ρ ↔ z ∈ ball (0 : R3) 1
      simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, norm_smul,
        Real.norm_eq_abs, abs_of_pos hρ]
      constructor
      · intro h
        nlinarith
      · intro h
        nlinarith
    have hAffq : Affine.IsAff Ωq Vq c ρ := by
      intro z
      change c+ρ • z ∈ ball c (ρ/4) ↔ z ∈ ball (0 : R3) (1/4)
      simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, norm_smul,
        Real.norm_eq_abs, abs_of_pos hρ]
      constructor <;> intro h <;> nlinarith
    have hRestr : (volume : Measure R3).restrict (Ω : Set R3) ≤
        (1 : ℝ≥0∞) • (volume : Measure R3).restrict D := by
      simpa only [one_smul] using Measure.restrict_mono_set volume hΩD
    let R : Lp ℝ 2 ((volume : Measure R3).restrict D) →L[ℝ]
        Lp ℝ 2 ((volume : Measure R3).restrict (Ω : Set R3)) :=
      Lp.LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤) hRestr
    let T : Lp ℝ 2 ((volume : Measure R3).restrict D) →L[ℝ]
        Lp ℝ 2 ((volume : Measure R3).restrict (ballOpens : Set R3)) :=
      (Affine.compL hρ hAff).comp R
    have hRVal (q : Lp ℝ 2 ((volume : Measure R3).restrict D)) :
        (R q : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict (Ω : Set R3)]
          (q : R3 → ℝ) :=
      Lp.coeFn_LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤) hRestr q
    have hTVal (q : Lp ℝ 2 ((volume : Measure R3).restrict D)) :
        (T q : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict (ballOpens : Set R3)]
          fun z => q (c+ρ • z) := by
      exact (Affine.compL_ae hρ hAff (R q)).trans
        ((Affine.qmp hρ hAff).ae (hRVal q))
    let B : R3 → Matrix (Fin 3) (Fin 3) ℝ := fun z => Ahat (c+ρ • z)
    let un : ℕ → R3 → ℝ := fun j z => u j (c+ρ • z)
    have hB : ContDiff ℝ ∞ B := hAhat.comp (contDiff_const.add (contDiff_id.const_smul ρ))
    have hBpos : ∀ z, (B z).PosDef := fun z => hposhat (c+ρ • z)
    have hImage2 : ∀ z ∈ ball (0 : R3) 2, c+ρ • z ∈ ball c (2*ρ) := by
      intro z hz
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hρ]
      have hz' : ‖z‖ < 2 := mem_ball_zero_iff.mp hz
      nlinarith
    have hRoomD : ball c (2*ρ) ⊆ D :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hRoom
    have hun (j : ℕ) : ContDiffOn ℝ ∞ (un j) (ball (0 : R3) 2) :=
      (hu j).comp (contDiff_const.add (contDiff_id.const_smul ρ)).contDiffOn
        (fun z hz => hRoomD (hImage2 z hz))
    have hPUn (j : ℕ) : ∀ z ∈ (ballOpens : Set R3), divCoeffGrad B (un j) z = 0 := by
      intro z hz
      have hz2 : z ∈ ball (0 : R3) 2 :=
        ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz
      have hx : c+ρ • z ∈ ball c (2*ρ) := hImage2 z hz2
      have hCoeff : Ahat =ᶠ[𝓝 (c+ρ • z)] A :=
        Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) (fun t ht => hEq t ht)
      have hP0 : divCoeffGrad Ahat (u j) (c+ρ • z) = 0 := by
        rw [UCP.divCoeffGrad_congr hCoeff Filter.EventuallyEq.rfl]
        exact hPu j _ (hRoomD hx)
      simpa only [B, un, hP0, mul_zero] using
        Jets.divCoeffGrad_comp_affine Ahat (u j) c hρ.ne' z
    have hTV (j : ℕ) : (T (v j) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ballOpens : Set R3)] un j := by
      have hvΩ := ae_restrict_of_ae_restrict_of_subset hΩD (hval j)
      exact (hTVal (v j)).trans ((Affine.qmp hρ hAff).ae hvΩ)
    have hTLim : Tendsto (fun j => T (v j)) atTop (𝓝 (T w)) :=
      (T.continuous.tendsto w).comp hlim
    obtain ⟨Uhat, hUhat, hUhatVal, hUhatP⟩ :=
      exists_contDiffOn_of_tendsto_L2_classical_harmonic_on_unitBall
        hB hBpos un hun hPUn (fun j => T (v j)) (T w) hTV hTLim
    let inv : R3 → R3 := fun x => -(ρ⁻¹ • c)+ρ⁻¹ • x
    let F : R3 → ℝ := fun x => Uhat (inv x)
    have hInv (x : R3) : c+ρ • inv x=x := by
      dsimp only [inv]
      rw [smul_add, smul_neg, smul_smul, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
      simp only [one_smul]
      abel
    have hInvAff (z : R3) : inv (c+ρ • z)=z := by
      dsimp only [inv]
      rw [smul_add, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
      abel
    have hInvRoom : ∀ x ∈ ball c (ρ/4), inv x ∈ ball (0 : R3) (1/4) := by
      intro x hx
      have hxq : c+ρ • inv x ∈ (Ωq : Set R3) := by
        change c+ρ • inv x ∈ ball c (ρ/4)
        simpa only [hInv] using hx
      exact (hAffq (inv x)).mp hxq
    have hF : ContDiffOn ℝ ∞ F (ball c (ρ/4)) :=
      hUhat.comp (contDiff_const.add (contDiff_id.const_smul ρ⁻¹)).contDiffOn hInvRoom
    have hTValq := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1)) (hTVal w)
    have hEqBack : (fun z => Uhat z) =ᵐ[(volume : Measure R3).restrict (Vq : Set R3)]
        (fun z => w (c+ρ • z)) := hUhatVal.trans hTValq
    have hBack := (Affine.qmp (inv_pos.mpr hρ) (Affine.isAff_symm hρ hAffq)).ae hEqBack
    have hFVal : F =ᵐ[(volume : Measure R3).restrict (ball c (ρ/4))] (w : R3 → ℝ) := by
      filter_upwards [hBack] with x hx
      change Uhat (inv x) = w (c+ρ • inv x) at hx
      simpa only [F, hInv] using hx
    have hFP : ∀ x ∈ ball c (ρ/4), divCoeffGrad A F x = 0 := by
      intro x hx
      let z : R3 := inv x
      have hz : z ∈ ball (0 : R3) (1/4) := hInvRoom x hx
      have hFun : (fun t => F (c+ρ • t)) = Uhat := by
        funext t
        simp only [F, hInvAff]
      have hScaled := Jets.divCoeffGrad_comp_affine Ahat F c hρ.ne' z
      have hAhatEq : Ahat =ᶠ[𝓝 x] A :=
        Filter.eventually_of_mem (isOpen_ball.mem_nhds
          (ball_subset_ball (by linarith : ρ/4 ≤ 2*ρ) hx)) (fun t ht => hEq t ht)
      have hZero : divCoeffGrad B Uhat z = 0 := hUhatP z hz
      rw [hFun] at hScaled
      change divCoeffGrad B Uhat z = ρ^2 * divCoeffGrad Ahat F (c+ρ • z) at hScaled
      rw [hZero] at hScaled
      simp only [z, hInv] at hScaled
      have hNative : divCoeffGrad Ahat F x = 0 :=
        (mul_eq_zero.mp hScaled.symm).resolve_left (pow_ne_zero 2 hρ.ne')
      rw [← UCP.divCoeffGrad_congr hAhatEq Filter.EventuallyEq.rfl]
      exact hNative
    exact ⟨ρ/4, by positivity,
      (ball_subset_ball (by linarith : ρ/4 ≤ ρ)).trans hΩD, F, hF, hFVal, hFP⟩
  choose r hr hrD f hf hfw hfp using hlocal
  let U : R3 → ℝ := fun x => if hx : x ∈ D then f x hx x else 0
  have hKey : ∀ c (hc : c ∈ D), ∀ x ∈ ball c (r c hc), U x=f c hc x := by
    intro c hc x hx
    have hxD : x ∈ D := hrD c hc hx
    have hUx : U x=f x hxD x := by simp only [U, dif_pos hxD]
    rw [hUx]
    let S : Set R3 := ball c (r c hc) ∩ ball x (r x hxD)
    have hxS : x ∈ S := ⟨hx, mem_ball_self (hr x hxD)⟩
    have h1 : f c hc =ᵐ[(volume : Measure R3).restrict S] (w : R3 → ℝ) :=
      ae_restrict_of_ae_restrict_of_subset (s := S) Set.inter_subset_left (hfw c hc)
    have h2 : f x hxD =ᵐ[(volume : Measure R3).restrict S] (w : R3 → ℝ) :=
      ae_restrict_of_ae_restrict_of_subset (s := S) Set.inter_subset_right (hfw x hxD)
    have hEq : f x hxD =ᵐ[(volume : Measure R3).restrict S] f c hc := by
      filter_upwards [h1, h2] with y hy1 hy2
      exact hy2.trans hy1.symm
    exact Measure.eqOn_open_of_ae_eq hEq
      (isOpen_ball.inter isOpen_ball) ((hf x hxD).continuousOn.mono Set.inter_subset_right)
      ((hf c hc).continuousOn.mono Set.inter_subset_left) hxS
  refine ⟨U, ?_, ?_, ?_⟩
  · intro c hc
    have he : U =ᶠ[𝓝 c] f c hc :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self (hr c hc))) (hKey c hc)
    exact (((hf c hc).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self (hr c hc)))).congr_of_eventuallyEq he).contDiffWithinAt
  · obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun i : D => ball (i : R3) (r i i.2)) (fun _ => isOpen_ball)
    have hCover : D=⋃ i ∈ T, ball (i : R3) (r i i.2) := by
      rw [hTU]
      ext x
      simp only [Set.mem_iUnion]
      exact ⟨fun hx => ⟨⟨x,hx⟩,mem_ball_self (hr x hx)⟩,
        fun ⟨i,hi⟩ => hrD i i.2 hi⟩
    let Wfun : R3 → ℝ := (w : R3 → ℝ)
    change U =ᵐ[(volume : Measure R3).restrict D] Wfun
    rw [hCover, Filter.EventuallyEq, ae_restrict_biUnion_iff _ hT]
    intro i hi
    filter_upwards [hfw i i.2, ae_restrict_mem measurableSet_ball] with x hx hxb
    rw [hKey i i.2 x hxb, hx]
  · intro c hc
    have he : U =ᶠ[𝓝 c] f c hc :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self (hr c hc))) (hKey c hc)
    rw [UCP.divCoeffGrad_congr Filter.EventuallyEq.rfl he]
    exact hfp c hc c (mem_ball_self (hr c hc))

end OAI.AnisotropicCalderon.Regularity

#print axioms OAI.AnisotropicCalderon.Regularity.exists_contDiffOn_of_tendsto_L2_classical_harmonic_on_unitBall
#print axioms OAI.AnisotropicCalderon.Regularity.exists_contDiffOn_representative_of_mem_closure_L2_classical_harmonics
