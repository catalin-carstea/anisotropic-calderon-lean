import Calderon.CollaboratorBallRegularityOct17
import Calderon.CollaboratorSmoothRepOct17
import Calderon.CollaboratorUniqueContinuationDefinitionOct17

/-! Interior smoothness of weak solutions of `div(A ∇w) = 0` (helper for tasks 07–09).

The weak solution is pulled back to the unit ball, where a bootstrap with nested cutoffs and
`ball_regularity` shows that cutoffs of it lie in every `H^k`; this is transported back and
`exists_contDiffOn_ae_eq` gives a smooth representative. The classical equation follows by
integration by parts and the fundamental lemma. -/

noncomputable section
open MeasureTheory TopologicalSpace Metric
open scoped ContDiff Matrix.Norms.Elementwise Distributions Gradient
namespace OAI.AnisotropicCalderon.Regularity.IS
open TauCeti TauCeti.PDE _root_.OAI.AnisotropicCalderon.Affine

set_option maxSynthPendingDepth 10

open EnergyBridge HO
open scoped InnerProductSpace

/-! ### Radii and cutoffs -/

/-- Radii of the nested balls, decreasing from `3/4` to `1/2`. -/
def rr (n : ℕ) : ℝ := 1 / 2 + (1 / 2) ^ (n + 2)

theorem half_lt_rr (n : ℕ) : 1 / 2 < rr n := by
  unfold rr; have := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 2); linarith

theorem rr_succ_lt (n : ℕ) : rr (n + 1) < rr n := by
  unfold rr
  have := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 2)
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
  linarith

theorem rr_le (n : ℕ) : rr n ≤ 3 / 4 := by
  unfold rr
  have : ((1 : ℝ) / 2) ^ (n + 2) ≤ (1 / 2) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at this ⊢; linarith

theorem exists_bound {ζ : R3 → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x, |ζ x| ≤ M) ∧ ∀ x, ‖∇ ζ x‖ ≤ M := by
  obtain ⟨M1, h1⟩ := hζ.continuous.bounded_above_of_compact_support hc
  obtain ⟨M2, h2⟩ := (ContDiff.continuous_gradient hζ).bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ) |>.comp_left (g := (InnerProductSpace.toDual ℝ R3).symm) (by simp))
  refine ⟨max 0 (max M1 M2), le_max_left _ _, fun x => ?_, fun x => ?_⟩
  · exact (by simpa using h1 x : |ζ x| ≤ M1).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h2 x).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem divCoeffGradient_eq_zero {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {ζ : R3 → ℝ} (hζ : ContDiff ℝ ∞ ζ) {x : R3} (hx : x ∉ tsupport ζ) :
    divCoeffGradient a ζ x = 0 := by
  have hev : ∀ᶠ y in nhds x, ∇ ζ y = 0 := by
    filter_upwards [(isClosed_tsupport ζ).isOpen_compl.mem_nhds hx] with y hy
    exact gradient_eq_zero_of_notMem_tsupport hy
  refine Finset.sum_eq_zero fun i _ => ?_
  have hd : DifferentiableAt ℝ (fun y => matrixBilinearForm (a y)
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (∇ ζ y)) x := by
    have : (fun y => matrixBilinearForm (a y) (EuclideanSpace.basisFun (Fin 3) ℝ i) (∇ ζ y)) =
        fun y => ∑ i', ∑ k, (EuclideanSpace.basisFun (Fin 3) ℝ i) i' *
          a y i' k * ∇ ζ y k := funext fun y => matrixBilinearForm_eq_sum _ _ _
    rw [this]
    exact (ContDiff.sum fun i' _ => ContDiff.sum fun k _ =>
      (contDiff_const.mul (contDiff_matrix_entry ha i' k)).mul
        (contDiff_gradient_coord hζ k)).differentiable (by simp) x
  rw [hd.lineDeriv_eq_fderiv]
  have h0 : (fun y => matrixBilinearForm (a y) (EuclideanSpace.basisFun (Fin 3) ℝ i) (∇ ζ y))
      =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [hev] with y hy
    rw [hy, map_zero]
  rw [h0.fderiv_eq]
  simp

/-! ### The bootstrap on the unit ball -/

theorem hasCompactSupport_of_tsupport {ζ : R3 → ℝ} {r : ℝ} (h : tsupport ζ ⊆ ball (0 : R3) r) :
    HasCompactSupport ζ :=
  (isCompact_closedBall (0 : R3) r).of_isClosed_subset (isClosed_tsupport ζ)
    (h.trans ball_subset_closedBall)

/-- One regularity step: from `H^n` forcing to `H^{n+2}` for the localized function. -/
theorem step {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a) (hpos : ∀ x, (a x).PosDef)
    (u : W1p (volume : Measure R3) ballOpens 2)
    (heq : ∀ φ : 𝓓(ballOpens, ℝ), ∫ x in (ballOpens : Set R3),
      matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (W1p.gradient u x) = 0)
    (n : ℕ) {ζ : R3 → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hts : tsupport ζ ⊆ ball (0 : R3) (3 / 4))
    (hF : ∀ F : L2B, ⇑F =ᵐ[(volume : Measure R3).restrict ballOpens]
      locForcing a ζ (0 : L2B) u → F ∈ Hs n) :
    AEIn (Hs (n + 2)) (fun x => ζ x * W1p.value u x) := by
  have hc := hasCompactSupport_of_tsupport hts
  have htsB : tsupport ζ ⊆ (ballOpens : Set R3) :=
    hts.trans (ball_subset_ball (by norm_num))
  obtain ⟨M, hM, hζM, hgM⟩ := exists_bound hζ hc
  let v : W1p (volume : Measure R3) ballOpens 2 :=
    W1p.contDiffSMul ζ hζ hM (fun x _ => hζM x) (fun x _ => hgM x) u
  have hv0 : v ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by norm_num) hζ hM _ _ hc htsB u
  have hvv := W1p.value_contDiffSMul_ae hζ hM (fun x _ => hζM x) (fun x _ => hgM x) u
  have hvg := W1p.gradient_contDiffSMul_ae hζ hM (fun x _ => hζM x) (fun x _ => hgM x) u
  have hu0 : ∀ φ : 𝓓(ballOpens, ℝ), ∫ x in (ballOpens : Set R3),
      matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (W1p.gradient u x) =
        ∫ x in (ballOpens : Set R3), (0 : L2B) x * φ x := by
    intro φ
    rw [heq φ]
    symm
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)] with x hx
    have : ((0 : L2B) : R3 → ℝ) x * φ x = 0 := by rw [hx]; simp
    exact this
  obtain ⟨F, hFl, hFeq⟩ := exists_localized_forcing_eq ha hu0 hζ
  have hFn := hF F hFl
  obtain ⟨G, hG⟩ := mem_Hs.mp hFn
  have htest : ∀ φ : 𝓓(ballOpens, ℝ), ∫ x in (ballOpens : Set R3),
      matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (W1p.gradient v x) =
        ∫ x in (ballOpens : Set R3), F x * φ x := by
    intro φ
    rw [← hFeq φ]
    refine integral_congr_ae ?_
    filter_upwards [hvg] with x hx
    rw [hx]
  have heqv : ∀ φ : W1p (volume : Measure R3) (ballO 0 1) 2,
      φ ∈ w1p0Submodule (volume : Measure R3) (ballO 0 1) 2 →
      ∫ x in ball (0 : R3) 1, matrixBilinearForm (a x) (W1p.gradient φ x) (W1p.gradient v x) =
        ∫ x in ball (0 : R3) 1, Wkp.value n G x * W1p.value φ x := by
    intro φ hφ
    rw [hG]
    exact eq_of_testFunction ha.continuous htest φ hφ
  obtain ⟨W, hW⟩ := ball_regularity 0 one_pos ha hpos n G v hv0 heqv
  have hmem : W1p.value v ∈ Hs (n + 2) := by
    have h1 : W1p.value (Wkp.firstOrder (n + 1) W) = W1p.value v := congrArg W1p.value hW
    have := value_firstOrder_mem_Hs (n + 1) W
    exact h1 ▸ this
  refine aeIn_congr (aeIn_of_mem hmem) ?_
  filter_upwards [hvv] with x hx
  rw [hx, smul_eq_mul]


theorem gradient_eq_zero_of_eventuallyEq_const {f : R3 → ℝ} {x : R3} {c : ℝ}
    (h : f =ᶠ[nhds x] fun _ => c) : ∇ f x = 0 := by
  simp [gradient, h.fderiv_eq]

/-- The localized forcing is `H^{m+1}` once `η u ∈ H^{m+2}` for some `η = 1` near `supp ζ`. -/
theorem forcing_reg {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    (u : W1p (volume : Measure R3) ballOpens 2) (m : ℕ) {ζ η : R3 → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) {r : ℝ}
    (hζr : tsupport ζ ⊆ ball (0 : R3) r) (hη1 : ∀ x ∈ ball (0 : R3) r, η x = 1)
    (hηu : AEIn (Hs (m + 2)) (fun x => η x * W1p.value u x)) (F : L2B)
    (hF : ⇑F =ᵐ[(volume : Measure R3).restrict ballOpens] locForcing a ζ (0 : L2B) u) :
    F ∈ Hs (m + 1) := by
  obtain ⟨M, hM, hηM, hgM⟩ := exists_bound hη hηc
  let v : W1p (volume : Measure R3) ballOpens 2 :=
    W1p.contDiffSMul η hη hM (fun x _ => hηM x) (fun x _ => hgM x) u
  have hvv := W1p.value_contDiffSMul_ae hη hM (fun x _ => hηM x) (fun x _ => hgM x) u
  have hvg := W1p.gradient_contDiffSMul_ae hη hM (fun x _ => hηM x) (fun x _ => hgM x) u
  have hmem : W1p.value v ∈ Hs (m + 1 + 1) := by
    refine mem_of_aeIn (aeIn_congr hηu ?_)
    filter_upwards [hvv] with x hx
    rw [hx, smul_eq_mul]
  obtain ⟨U, hU⟩ := exists_of_value_mem_Hs (m + 1) v hmem
  have h := aeIn_locForcing m ha hζ (F := (0 : L2B)) (Submodule.zero_mem _) U
  rw [hU] at h
  refine mem_of_aeIn (aeIn_congr h ?_)
  refine Filter.EventuallyEq.trans ?_ hF.symm
  filter_upwards [hvv, hvg] with x h1 h2
  by_cases hx : x ∈ ball (0 : R3) r
  · have hg : ∇ η x = 0 := by
      refine gradient_eq_zero_of_eventuallyEq_const (c := 1) ?_
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hη1 y hy
    simp only [locForcing, v] at h1 h2 ⊢
    rw [h1, h2, hη1 x hx, hg]
    simp
  · have hxζ : x ∉ tsupport ζ := fun h' => hx (hζr h')
    simp [locForcing, image_eq_zero_of_notMem_tsupport hxζ,
      gradient_eq_zero_of_notMem_tsupport hxζ, divCoeffGradient_eq_zero ha hζ hxζ]

/-- **Interior bootstrap on the unit ball.** -/
theorem boot {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a) (hpos : ∀ x, (a x).PosDef)
    (u : W1p (volume : Measure R3) ballOpens 2)
    (heq : ∀ φ : 𝓓(ballOpens, ℝ), ∫ x in (ballOpens : Set R3),
      matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (W1p.gradient u x) = 0) :
    ∀ n : ℕ, ∀ ζ : R3 → ℝ, ContDiff ℝ ∞ ζ → tsupport ζ ⊆ ball (0 : R3) (rr n) →
      AEIn (Hs (n + 2)) (fun x => ζ x * W1p.value u x)
  | 0, ζ, hζ, hts => step ha hpos u heq 0 hζ (hts.trans (ball_subset_ball (rr_le 0)))
      fun F _ => mem_Hs_zero F
  | m + 1, ζ, hζ, hts => by
      have h1 := rr_succ_lt m
      have h2 : 0 < rr (m + 1) := lt_trans (by norm_num) (half_lt_rr (m + 1))
      let η := bump (rr (m + 1)) ((rr (m + 1) + rr m) / 2) h2 (by linarith)
      have hηts : tsupport (η : R3 → ℝ) ⊆ ball (0 : R3) (rr m) := by
        rw [η.tsupport_eq]
        exact closedBall_subset_ball (by simp [η]; linarith)
      have hηu := boot ha hpos u heq m η η.contDiff hηts
      refine step ha hpos u heq (m + 1) hζ (hts.trans (ball_subset_ball (rr_le (m + 1)))) ?_
      exact forcing_reg ha u m hζ η.contDiff (hasCompactSupport_of_tsupport hηts) hts
        (fun x hx => η.one_of_mem_closedBall (by simpa [η] using (mem_ball.1 hx).le)) hηu

/-! ### Affine transport -/

theorem gradient_comp_aff {f : R3 → ℝ} (hf : Differentiable ℝ f) (c : R3) (s : ℝ) (z : R3) :
    ∇ (fun z => f (c + s • z)) z = s • ∇ f (c + s • z) := by
  have hd : HasFDerivAt (fun z => f (c + s • z))
      ((fderiv ℝ f (c + s • z)).comp (s • ContinuousLinearMap.id ℝ R3)) z :=
    (hf _).hasFDerivAt.comp z (((hasFDerivAt_id z).const_smul s).const_add c)
  refine ext_inner_right ℝ fun v => ?_
  rw [real_inner_smul_left]
  simp only [gradient, InnerProductSpace.toDual_symm_apply, hd.fderiv]
  simp

/-- The weak equation pulled back from `ball x ρ` to the unit ball. -/
theorem pull_eq (x : R3) {ρ : ℝ} (hρ : 0 < ρ) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (W : W1p (volume : Measure R3) (ballO x ρ) 2)
    (heq : ∀ φ : 𝓓(ballO x ρ, ℝ), ∫ z in ball x ρ,
      matrixBilinearForm (A z) (gradient (φ : R3 → ℝ) z) (W1p.gradient W z) = 0)
    (ψ : 𝓓(ballOpens, ℝ)) :
    ∫ y in (ballOpens : Set R3), matrixBilinearForm (A (x + ρ • y)) (gradient (ψ : R3 → ℝ) y)
      (W1p.gradient (pullWkp x hρ 1 W : W1p (volume : Measure R3) ballOpens 2) y) = 0 := by
  let φ : 𝓓(ballO x ρ, ℝ) := compTest (inv_pos.2 hρ) (isAff_symm hρ (isAff_ball x hρ)) ψ
  have hφ : ∀ z, ∇ (φ : R3 → ℝ) z = ρ⁻¹ • ∇ (ψ : R3 → ℝ) (-(ρ⁻¹ • x) + ρ⁻¹ • z) := fun z =>
    gradient_comp_aff (ψ.contDiff.differentiable (by simp)) _ _ z
  let g : R3 → ℝ := fun z =>
    matrixBilinearForm (A z) (gradient (φ : R3 → ℝ) z) (W1p.gradient W z)
  have h0 : ∫ y in ball (0 : R3) 1, g (x + ρ • y) = 0 := by
    have h1 := integral_comp_aff x hρ ((ball x ρ).indicator g)
    rw [integral_indicator measurableSet_ball, heq φ, smul_zero] at h1
    rw [← integral_indicator measurableSet_ball, ← h1]
    congr 1; funext y
    have hy : x + ρ • y ∈ ball x ρ ↔ y ∈ ball (0 : R3) 1 := isAff_ball x hρ y
    by_cases h : y ∈ ball (0 : R3) 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hy.2 h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hy.1 h'))]
  have hint : ∫ y in (ballOpens : Set R3), matrixBilinearForm (A (x + ρ • y))
      (gradient (ψ : R3 → ℝ) y)
      (W1p.gradient (pullWkp x hρ 1 W : W1p (volume : Measure R3) ballOpens 2) y) =
      ∫ y in ball (0 : R3) 1, ρ ^ 2 * g (x + ρ • y) := by
    refine integral_congr_ae ?_
    filter_upwards [gradient_pullWkp_one x hρ W] with y hy
    rw [hy]
    simp only [g, hφ, aff_symm_aff_zero hρ, map_smul, smul_apply, smul_eq_mul]
    field_simp
  rw [hint, integral_const_mul, h0, mul_zero]


/-- Regularity of a cutoff of the pullback, transported back to `ball x (ρ / 4)`. -/
theorem push_reg (x : R3) {ρ : ℝ} (hρ : 0 < ρ) (W : W1p (volume : Measure R3) (ballO x ρ) 2)
    {w : R3 → ℝ} (hWw : ⇑(W1p.value W) =ᵐ[(volume : Measure R3).restrict (ball x ρ)] w)
    {ζ : R3 → ℝ} (hζ1 : ∀ y ∈ ball (0 : R3) (1 / 4), ζ y = 1)
    (hreg : ∀ k, AEIn (Hs k) (fun y => ζ y *
      W1p.value (pullWkp x hρ 1 W : W1p (volume : Measure R3) ballOpens 2) y)) (k : ℕ) :
    ∃ V : Wkp (volume : Measure R3) (⟨ball x (ρ / 4), isOpen_ball⟩ : Opens R3) 2 k,
      ⇑(Wkp.value k V) =ᵐ[(volume : Measure R3).restrict (ball x (ρ / 4))] w := by
  set u : W1p (volume : Measure R3) ballOpens 2 := pullWkp x hρ 1 W with hu
  obtain ⟨g, hg, hge⟩ := hreg k
  obtain ⟨Z, hZ⟩ := mem_Hs.mp hg
  let V0 : Wkp (volume : Measure R3) (ballO x ρ) 2 k := (pullWkp x hρ k).symm Z
  have hV0 := value_pullWkp_symm x hρ k Z
  have hT := (qmp (inv_pos.2 hρ) (isAff_symm hρ (isAff_ball x hρ))).ae_eq_comp hge
  have hW : ⇑(W1p.value W) =ᵐ[(volume : Measure R3).restrict (ballO x ρ)]
      fun z => W1p.value u (ρ⁻¹ • (z - x)) := by
    have h1 := value_pullWkp_symm x hρ 1 u
    have e : (pullWkp x hρ 1).symm u = W := (pullWkp x hρ 1).symm_apply_apply W
    rw [e] at h1
    have e1 : Wkp.value 1 W = W1p.value W := Wkp.value_one W
    have e2 : Wkp.value 1 u = W1p.value u := Wkp.value_one u
    rw [e1, e2] at h1
    exact h1
  have hle : (⟨ball x (ρ / 4), isOpen_ball⟩ : Opens R3) ≤ ballO x ρ := fun z hz =>
    ball_subset_ball (by linarith) hz
  refine ⟨Wkp.restrictL hle k V0, ?_⟩
  have hsub : ball x (ρ / 4) ⊆ ball x ρ := ball_subset_ball (by linarith)
  filter_upwards [Wkp.value_restrictL_ae hle k V0,
    ae_restrict_of_ae_restrict_of_subset hsub (hV0.and (hT.and (hW.and hWw))),
    ae_restrict_mem measurableSet_ball] with z h1 h2 hz
  obtain ⟨h3, h4, h5, h6⟩ := h2
  have hz' : ρ⁻¹ • (z - x) ∈ ball (0 : R3) (1 / 4) := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hρ),
      ← dist_eq_norm]
    have := mem_ball.1 hz
    rw [inv_mul_lt_iff₀ hρ]; linarith
  have e : -(ρ⁻¹ • x) + ρ⁻¹ • z = ρ⁻¹ • (z - x) := by rw [smul_sub]; abel
  simp only [Function.comp, aff, e] at h4
  rw [h1, h3, hZ, h4, hζ1 _ hz', one_mul, ← h5, h6]

/-! ### The classical equation -/

theorem gradient_apply_coord (f : R3 → ℝ) (z : R3) (k : Fin 3) :
    ∇ f z k = fderiv ℝ f z (EuclideanSpace.single k 1) := by
  have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single k (1 : ℝ))
    (y := fderiv ℝ f z)
  rw [← this, EuclideanSpace.inner_single_right]
  simp [gradient]

/-- The conormal field components `∑ⱼ A i j ∂ⱼ ψ`. -/
def cf (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (ψ : R3 → ℝ) (i : Fin 3) (z : R3) : ℝ :=
  ∑ j : Fin 3, A z i j * fderiv ℝ ψ z (EuclideanSpace.single j 1)

theorem contDiff_cf {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A) {ψ : R3 → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (i : Fin 3) : ContDiff ℝ ∞ (cf A ψ i) :=
  ContDiff.sum fun j _ => (contDiff_matrix_entry hA i j).mul
    ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

theorem divCoeffGrad_eq (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (ψ : R3 → ℝ) (z : R3) :
    divCoeffGrad A ψ z = ∑ i : Fin 3, fderiv ℝ (cf A ψ i) z (EuclideanSpace.single i 1) := rfl

theorem continuous_divCoeffGrad {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
    {ψ : R3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) : Continuous (divCoeffGrad A ψ) := by
  have : divCoeffGrad A ψ = fun z =>
      ∑ i : Fin 3, fderiv ℝ (cf A ψ i) z (EuclideanSpace.single i 1) :=
    funext (divCoeffGrad_eq A ψ)
  rw [this]
  exact continuous_finsetSum _ fun i _ =>
    ((contDiff_cf hA hψ i).continuous_fderiv (by simp)).clm_apply continuous_const

/-- Integration by parts for the divergence-form operator. -/
theorem integral_mbf_eq {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
    {ψ φ : R3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ z, matrixBilinearForm (A z) (∇ φ z) (∇ ψ z) = -∫ z, φ z * divCoeffGrad A ψ z := by
  have hpt : ∀ z, matrixBilinearForm (A z) (∇ φ z) (∇ ψ z) =
      ∑ i : Fin 3, fderiv ℝ φ z (EuclideanSpace.single i 1) * cf A ψ i z := by
    intro z
    rw [matrixBilinearForm_eq_sum]
    simp only [cf, gradient_apply_coord, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hd1 : ∀ i : Fin 3, Continuous fun z => fderiv ℝ φ z (EuclideanSpace.single i 1) :=
    fun i => (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hd2 : ∀ i : Fin 3, Continuous fun z => fderiv ℝ (cf A ψ i) z (EuclideanSpace.single i 1) :=
    fun i => ((contDiff_cf hA hψ i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs1 : ∀ i : Fin 3, HasCompactSupport fun z => fderiv ℝ φ z (EuclideanSpace.single i 1) :=
    fun i => (hφc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : R3 →L[ℝ] ℝ =>
      L (EuclideanSpace.single i 1)) (by simp)
  have hint1 : ∀ i : Fin 3, Integrable fun z => fderiv ℝ φ z (EuclideanSpace.single i 1) *
      cf A ψ i z := fun i =>
    ((hd1 i).mul (contDiff_cf hA hψ i).continuous).integrable_of_hasCompactSupport
      (hcs1 i).mul_right
  have hint2 : ∀ i : Fin 3, Integrable fun z => φ z *
      fderiv ℝ (cf A ψ i) z (EuclideanSpace.single i 1) := fun i =>
    (hφ.continuous.mul (hd2 i)).integrable_of_hasCompactSupport hφc.mul_right
  have hint3 : ∀ i : Fin 3, Integrable fun z => φ z * cf A ψ i z := fun i =>
    (hφ.continuous.mul (contDiff_cf hA hψ i).continuous).integrable_of_hasCompactSupport
      hφc.mul_right
  simp only [hpt, divCoeffGrad_eq, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint1 i, integral_finsetSum _ fun i _ => hint2 i,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hint1 i) (hint2 i) (hint3 i)
    (fun z _ => hφ.differentiable (by simp) z)
    (fun z _ => (contDiff_cf hA hψ i).differentiable (by simp) z), neg_neg]


/-- The weak gradient of a representative that is smooth on the ball is the classical one. -/
theorem gradient_ae_eq {x : R3} {ρ : ℝ} (W : W1p (volume : Measure R3) (ballO x ρ) 2)
    {f : R3 → ℝ} (hf : ContDiffOn ℝ ∞ f (ball x ρ))
    (hWf : ⇑(W1p.value W) =ᵐ[(volume : Measure R3).restrict (ball x ρ)] f) :
    ⇑(W1p.gradient W) =ᵐ[(volume : Measure R3).restrict (ball x ρ)] ∇ f := by
  have hc := hf.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  have hd := ((W1p.hasWeakFDerivOn W).congr_ae hWf).ae_eq_fderiv
    (hc.locallyIntegrableOn measurableSet_ball)
    (fun z hz => (hf.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by simp))
  filter_upwards [hd] with z hz
  refine ext_inner_right ℝ fun v => ?_
  have h1 := congrArg (fun L : R3 →L[ℝ] ℝ => L v) hz
  simp only [innerSL_apply_apply] at h1
  rw [h1]
  simp [gradient]

/-- The classical equation at the centre of a ball on which the weak equation holds. -/
theorem classical_eq {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
    {x : R3} {ρ : ℝ} (hρ : 0 < ρ) {w' : R3 → ℝ} (hw' : ContDiffOn ℝ ∞ w' (ball x ρ))
    (W : W1p (volume : Measure R3) (ballO x ρ) 2)
    (hWv : ⇑(W1p.value W) =ᵐ[(volume : Measure R3).restrict (ball x ρ)] w')
    (heq : ∀ φ : 𝓓(ballO x ρ, ℝ), ∫ z in ball x ρ,
      matrixBilinearForm (A z) (gradient (φ : R3 → ℝ) z) (W1p.gradient W z) = 0) :
    divCoeffGrad A w' x = 0 := by
  have hgrad := gradient_ae_eq W hw' hWv
  -- the cutoff
  let χ : ContDiffBump x := ⟨ρ / 2, 3 * ρ / 4, by positivity, by linarith⟩
  let ψ : R3 → ℝ := fun z => χ z * w' z
  have hχts : tsupport (χ : R3 → ℝ) ⊆ ball x ρ := by
    rw [χ.tsupport_eq]; exact closedBall_subset_ball (by simp [χ]; linarith)
  have hψ : ContDiff ℝ ∞ ψ := by
    refine contDiff_iff_contDiffAt.2 fun y => ?_
    by_cases hy : y ∈ ball x ρ
    · exact χ.contDiff.contDiffAt.mul (hw'.contDiffAt (isOpen_ball.mem_nhds hy))
    · have hy' : y ∉ tsupport (χ : R3 → ℝ) := fun h => hy (hχts h)
      refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hy'] with z hz
      simp [ψ, image_eq_zero_of_notMem_tsupport hz]
  have hψw : ∀ y ∈ ball x (ρ / 2), ψ =ᶠ[nhds y] w' := by
    intro y hy
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    simp [ψ, χ.one_of_mem_closedBall (by simpa [χ] using (mem_ball.1 hz).le)]
  have hD := continuous_divCoeffGrad hA hψ
  -- the weak equation against test functions supported in `ball x (ρ / 2)`
  have hzero : ∀ g : R3 → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ ball x (ρ / 2) → ∫ z, g z • divCoeffGrad A ψ z = 0 := by
    intro g hg hgc hgts
    have hgts' : tsupport g ⊆ (ballO x ρ : Set R3) :=
      hgts.trans (ball_subset_ball (by linarith))
    let φ : 𝓓(ballO x ρ, ℝ) := ⟨g, hg, hgc, hgts'⟩
    have h1 := heq φ
    have h2 : ∫ z in ball x ρ, matrixBilinearForm (A z) (gradient (φ : R3 → ℝ) z)
        (W1p.gradient W z) =
        ∫ z in ball x ρ, matrixBilinearForm (A z) (∇ g z) (∇ ψ z) := by
      refine integral_congr_ae ?_
      filter_upwards [hgrad] with z hz
      show matrixBilinearForm (A z) (∇ g z) (W1p.gradient W z) =
        matrixBilinearForm (A z) (∇ g z) (∇ ψ z)
      by_cases hzg : z ∈ tsupport g
      · have e : ∇ w' z = ∇ ψ z := by
          simp only [gradient, (hψw z (hgts hzg)).fderiv_eq (𝕜 := ℝ)]
        rw [hz, e]
      · rw [gradient_eq_zero_of_notMem_tsupport hzg]; simp
    have h3 : ∫ z in ball x ρ, matrixBilinearForm (A z) (∇ g z) (∇ ψ z) =
        ∫ z, matrixBilinearForm (A z) (∇ g z) (∇ ψ z) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [gradient_eq_zero_of_notMem_tsupport (fun h => hz (hgts' h))]; simp
    rw [h2, h3] at h1
    rw [integral_mbf_eq hA hψ hg hgc] at h1
    simpa [smul_eq_mul] using h1
  have hae := isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hD.locallyIntegrable.locallyIntegrableOn _) hzero
  have hae' : divCoeffGrad A ψ =ᵐ[(volume : Measure R3).restrict (ball x (ρ / 2))] fun _ => 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
    exact hae
  have hx0 : divCoeffGrad A ψ x = 0 := Measure.eqOn_open_of_ae_eq hae' isOpen_ball hD.continuousOn continuousOn_const
    (mem_ball_self (by positivity : 0 < ρ / 2))
  suffices h : divCoeffGrad A w' x = divCoeffGrad A ψ x by rw [h]; exact hx0
  -- locality of `divCoeffGrad`
  have hev := hψw x (mem_ball_self (by positivity))
  rw [divCoeffGrad_eq, divCoeffGrad_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [hev.fderiv (𝕜 := ℝ)] with z hz
  simp only [cf, hz]

end OAI.AnisotropicCalderon.Regularity.IS

namespace OAI.AnisotropicCalderon.Regularity
open TauCeti TauCeti.PDE _root_.OAI.AnisotropicCalderon.Affine

open IS HO in
/-- A function that is locally a `W^{1,2}` weak solution of `div(A ∇w) = 0` on an open set `O`
has a smooth representative there, which solves the equation classically. -/
theorem exists_smooth_of_weak {O : Set R3} (hO : IsOpen O) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ContDiff ℝ ∞ A) (hpos : ∀ x, (A x).PosDef) {w : R3 → ℝ}
    (hw : ∀ x ∈ O, ∃ ρ > 0, ball x ρ ⊆ O ∧ ∃ W : W1p (volume : Measure R3) (ballO x ρ) 2,
      ⇑(W1p.value W) =ᵐ[(volume : Measure R3).restrict (ball x ρ)] w ∧
      ∀ φ : 𝓓(ballO x ρ, ℝ), ∫ x in ball x ρ,
        matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient W x) = 0) :
    ∃ w' : R3 → ℝ, ContDiffOn ℝ ∞ w' O ∧ w' =ᵐ[(volume : Measure R3).restrict O] w ∧
      ∀ x ∈ O, divCoeffGrad A w' x = 0 := by
  have hloc : ∀ x ∈ O, ∃ r > 0, ball x r ⊆ O ∧ ∀ k : ℕ,
      ∃ V : Wkp (volume : Measure R3) (⟨ball x r, isOpen_ball⟩ : Opens R3) 2 k,
        ⇑(Wkp.value k V) =ᵐ[(volume : Measure R3).restrict (ball x r)] w := by
    intro x hx
    obtain ⟨ρ, hρ, hρO, W, hWv, heq⟩ := hw x hx
    refine ⟨ρ / 4, by positivity, (ball_subset_ball (by linarith)).trans hρO, fun k => ?_⟩
    have ha : ContDiff ℝ ∞ (fun y : R3 => A (x + ρ • y)) := hA.comp (by fun_prop)
    have heq' := pull_eq x hρ W heq
    let ζ := bump (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    have hts : ∀ n, tsupport (ζ : R3 → ℝ) ⊆ ball (0 : R3) (rr n) := fun n => by
      rw [ζ.tsupport_eq]
      exact closedBall_subset_ball (by simpa [ζ] using half_lt_rr n)
    refine push_reg x hρ W hWv (ζ := ζ) (fun y hy => ζ.one_of_mem_closedBall
      (by simpa [ζ] using (mem_ball.1 hy).le)) (fun n => ?_) k
    exact aeIn_mono (by omega : n ≤ n + 2)
      (boot ha (fun y => hpos _) _ heq' n ζ ζ.contDiff (hts n))
  obtain ⟨w', hw's, hw'w⟩ := exists_contDiffOn_ae_eq hO hloc
  refine ⟨w', hw's, hw'w, fun x hx => ?_⟩
  obtain ⟨ρ, hρ, hρO, W, hWv, heq⟩ := hw x hx
  exact classical_eq hA hρ (hw's.mono hρO) W
    (hWv.trans (ae_restrict_of_ae_restrict_of_subset hρO hw'w.symm)) heq

end OAI.AnisotropicCalderon.Regularity
