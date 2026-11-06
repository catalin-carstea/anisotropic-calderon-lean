import C3Geometry
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

open Geometry

section C3JetEvaluation
open MeasureTheory
open scoped ENNReal Nat Matrix.Norms.Elementwise

/-- The closed native harmonic space, viewed as a submodule of `L²(D)`. -/
abbrev harmonicSub (D : Set R3) (hD : IsOpen D) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) : Submodule ℝ (Lp ℝ 2 ((volume : Measure R3).restrict D)) :=
  (Regularity.classicalHarmonicL2Space D hD A hA).toSubmodule

theorem harmonicRep_exists (D : Set R3) (hD : IsOpen D) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (u : harmonicSub D hD A hA) :
    ∃ U : R3 → ℝ, ContDiffOn ℝ ∞ U D ∧
      U =ᵐ[(volume : Measure R3).restrict D]
        ((u : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ) ∧
      ∀ x ∈ D, divCoeffGrad A U x = 0 :=
  Regularity.exists_contDiffOn_representative_of_mem_closure_L2_classical_harmonics
    D hD A hA hpos _ (by exact u.property)

/-- C3-D1.1: the closure444 smooth representative of the SAME class. -/
def harmonicRep (D : Set R3) (hD : IsOpen D) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (u : harmonicSub D hD A hA) : R3 → ℝ :=
  Classical.choose (harmonicRep_exists D hD A hA hpos u)

theorem harmonicRep_spec (D : Set R3) (hD : IsOpen D) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (u : harmonicSub D hD A hA) :
    ContDiffOn ℝ ∞ (harmonicRep D hD A hA hpos u) D ∧
      harmonicRep D hD A hA hpos u =ᵐ[(volume : Measure R3).restrict D]
        ((u : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ) ∧
      ∀ x ∈ D, divCoeffGrad A (harmonicRep D hD A hA hpos u) x = 0 :=
  Classical.choose_spec (harmonicRep_exists D hD A hA hpos u)

/-- C3-D1.2: continuous representatives that agree a.e. on an open set agree on it. -/
theorem eqOn_of_ae_eq_restrict_open {D : Set R3} (hD : IsOpen D) {f g : R3 → ℝ}
    (hf : ContinuousOn f D) (hg : ContinuousOn g D)
    (h : f =ᵐ[(volume : Measure R3).restrict D] g) : EqOn f g D :=
  fun _ hx => Measure.eqOn_open_of_ae_eq h hD hf hg hx

/-- C3-D1.3: additivity of the canonical representative on `D`. -/
theorem harmonicRep_add (D : Set R3) (hD : IsOpen D) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (u v : harmonicSub D hD A hA) :
    EqOn (harmonicRep D hD A hA hpos (u + v))
      (harmonicRep D hD A hA hpos u + harmonicRep D hD A hA hpos v) D := by
  obtain ⟨h1, h2, -⟩ := harmonicRep_spec D hD A hA hpos (u + v)
  obtain ⟨hu1, hu2, -⟩ := harmonicRep_spec D hD A hA hpos u
  obtain ⟨hv1, hv2, -⟩ := harmonicRep_spec D hD A hA hpos v
  refine eqOn_of_ae_eq_restrict_open hD h1.continuousOn (hu1.add hv1).continuousOn ?_
  have hc : (((u + v : harmonicSub D hD A hA) : Lp ℝ 2 ((volume : Measure R3).restrict D)) :
      R3 → ℝ) =ᵐ[(volume : Measure R3).restrict D]
        ((u : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ) +
        ((v : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ) := by
    rw [Submodule.coe_add]
    exact Lp.coeFn_add _ _
  filter_upwards [h2, hu2, hv2, hc] with x a b c d
  simp only [Pi.add_apply] at d ⊢
  rw [a, b, c]
  exact d

/-- C3-D1.3: homogeneity of the canonical representative on `D`. -/
theorem harmonicRep_smul (D : Set R3) (hD : IsOpen D) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (a : ℝ) (u : harmonicSub D hD A hA) :
    EqOn (harmonicRep D hD A hA hpos (a • u)) (a • harmonicRep D hD A hA hpos u) D := by
  obtain ⟨h1, h2, -⟩ := harmonicRep_spec D hD A hA hpos (a • u)
  obtain ⟨hu1, hu2, -⟩ := harmonicRep_spec D hD A hA hpos u
  refine eqOn_of_ae_eq_restrict_open hD h1.continuousOn (hu1.const_smul a).continuousOn ?_
  have hc : (((a • u : harmonicSub D hD A hA) : Lp ℝ 2 ((volume : Measure R3).restrict D)) :
      R3 → ℝ) =ᵐ[(volume : Measure R3).restrict D]
        a • ((u : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ) := by
    rw [Submodule.coe_smul]
    exact Lp.coeFn_smul _ _
  filter_upwards [h2, hu2, hc] with x p q r
  simp only [Pi.smul_apply] at r ⊢
  rw [p, q]
  exact r

theorem harmonicRep_contDiffAt (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (u : harmonicSub D hD A hA) (n : ℕ) {x : R3} (hx : x ∈ D) :
    ContDiffAt ℝ n (harmonicRep D hD A hA hpos u) x :=
  ((harmonicRep_spec D hD A hA hpos u).1.contDiffAt (hD.mem_nhds hx)).of_le
    (by exact_mod_cast le_top)

/-- C3-D1.4: additivity of the jet at a point of `D`. -/
theorem harmonicRep_iteratedFDeriv_add (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (n : ℕ) {x : R3} (hx : x ∈ D) (u v : harmonicSub D hD A hA) :
    iteratedFDeriv ℝ n (harmonicRep D hD A hA hpos (u + v)) x =
      iteratedFDeriv ℝ n (harmonicRep D hD A hA hpos u) x +
        iteratedFDeriv ℝ n (harmonicRep D hD A hA hpos v) x := by
  have hgerm : harmonicRep D hD A hA hpos (u + v) =ᶠ[𝓝 x]
      harmonicRep D hD A hA hpos u + harmonicRep D hD A hA hpos v :=
    Filter.eventually_of_mem (hD.mem_nhds hx) (harmonicRep_add D hD A hA hpos u v)
  rw [(hgerm.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]
  exact iteratedFDeriv_add_apply (harmonicRep_contDiffAt D hD A hA hpos u n hx)
    (harmonicRep_contDiffAt D hD A hA hpos v n hx)

/-- C3-D1.4: homogeneity of the jet at a point of `D`. -/
theorem harmonicRep_iteratedFDeriv_smul (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (n : ℕ) {x : R3} (hx : x ∈ D) (a : ℝ) (u : harmonicSub D hD A hA) :
    iteratedFDeriv ℝ n (harmonicRep D hD A hA hpos (a • u)) x =
      a • iteratedFDeriv ℝ n (harmonicRep D hD A hA hpos u) x := by
  have hgerm : harmonicRep D hD A hA hpos (a • u) =ᶠ[𝓝 x]
      a • harmonicRep D hD A hA hpos u :=
    Filter.eventually_of_mem (hD.mem_nhds hx) (harmonicRep_smul D hD A hA hpos a u)
  rw [(hgerm.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]
  exact iteratedFDeriv_const_smul_apply (harmonicRep_contDiffAt D hD A hA hpos u n hx)

/-- C3-D1.5: local jet bound by affine transport of the checked interior estimate 416.
The radius and constant are chosen before `u`. -/
theorem harmonicRep_local_jet_bound (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (c : R3) (hc : c ∈ D) (n : ℕ) :
    ∃ r > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : harmonicSub D hD A hA, ∀ x ∈ ball c r,
      ‖iteratedFDeriv ℝ n (harmonicRep D hD A hA hpos u) x‖ ≤ C * ‖u‖ := by
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD c hc
  obtain ⟨ρ, hρ, hρε⟩ : ∃ ρ : ℝ, 0 < ρ ∧ 8 * ρ = ε := ⟨ε / 8, by positivity, by ring⟩
  have hRoom : closedBall c (2 * (2 * ρ)) ⊆ D :=
    (closedBall_subset_ball (by linarith)).trans hεD
  obtain ⟨Ahat, hAhat, hposhat, hEq⟩ :=
    UCP.exists_global_coeff hD hA hpos (by positivity : 0 < 2 * ρ) hRoom
  let B : R3 → Matrix (Fin 3) (Fin 3) ℝ := fun z => Ahat (c + ρ • z)
  have hB : ContDiff ℝ ∞ B := hAhat.comp (contDiff_const.add (contDiff_id.const_smul ρ))
  have hBpos : ∀ z, (B z).PosDef := fun z => hposhat (c + ρ • z)
  obtain ⟨Cn, hCn, hJet⟩ := Regularity.exists_classical_harmonic_interior_jet_bound hB hBpos n
  let Ω : TopologicalSpace.Opens R3 := Affine.ballO c ρ
  have hΩD : (Ω : Set R3) ⊆ D := (ball_subset_ball (by linarith : ρ ≤ ε)).trans hεD
  have hAff : Affine.IsAff Ω ballOpens c ρ := by
    intro z
    change c + ρ • z ∈ ball c ρ ↔ z ∈ ball (0 : R3) 1
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, norm_smul,
      Real.norm_eq_abs, abs_of_pos hρ]
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith
  have hRestr : (volume : Measure R3).restrict (Ω : Set R3) ≤
      (1 : ℝ≥0∞) • (volume : Measure R3).restrict D := by
    simpa only [one_smul] using Measure.restrict_mono_set volume hΩD
  let T : Lp ℝ 2 ((volume : Measure R3).restrict D) →L[ℝ]
      Lp ℝ 2 ((volume : Measure R3).restrict (ballOpens : Set R3)) :=
    (Affine.compL hρ hAff).comp
      (Lp.LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤) hRestr)
  have hTVal (q : Lp ℝ 2 ((volume : Measure R3).restrict D)) :
      (T q : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict (ballOpens : Set R3)]
        fun z => q (c + ρ • z) :=
    (Affine.compL_ae hρ hAff _).trans ((Affine.qmp hρ hAff).ae
      (Lp.coeFn_LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤) hRestr q))
  let g : R3 ≃L[ℝ] R3 := ContinuousLinearEquiv.equivOfInverse
    (ρ⁻¹ • ContinuousLinearMap.id ℝ R3) (ρ • ContinuousLinearMap.id ℝ R3)
    (fun y => by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul,
        mul_inv_cancel₀ hρ.ne', one_smul])
    (fun y => by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul,
        inv_mul_cancel₀ hρ.ne', one_smul])
  have hgApply (y : R3) : g y = ρ⁻¹ • y := rfl
  refine ⟨ρ / 4, by positivity, Cn * ‖T‖ * ‖(g : R3 →L[ℝ] R3)‖ ^ n, by positivity, ?_⟩
  intro u x hx
  obtain ⟨hU, hUval, hUP⟩ := harmonicRep_spec D hD A hA hpos u
  set U := harmonicRep D hD A hA hpos u with hUdef
  let Uh : R3 → ℝ := fun z => U (c + ρ • z)
  have hImage2 : ∀ z ∈ ball (0 : R3) 2, c + ρ • z ∈ ball c (2 * ρ) := by
    intro z hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hρ]
    have hz' : ‖z‖ < 2 := mem_ball_zero_iff.mp hz
    nlinarith
  have hRoomD : ball c (2 * ρ) ⊆ D :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hRoom
  have hUh : ContDiffOn ℝ ∞ Uh (ball (0 : R3) 2) :=
    hU.comp (contDiff_const.add (contDiff_id.const_smul ρ)).contDiffOn
      (fun z hz => hRoomD (hImage2 z hz))
  have hPUh : ∀ z ∈ (ballOpens : Set R3), divCoeffGrad B Uh z = 0 := by
    intro z hz
    have hz2 : z ∈ ball (0 : R3) 2 :=
      ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz
    have hx2 : c + ρ • z ∈ ball c (2 * ρ) := hImage2 z hz2
    have hCoeff : Ahat =ᶠ[𝓝 (c + ρ • z)] A :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hx2) (fun t ht => hEq t ht)
    have hP0 : divCoeffGrad Ahat U (c + ρ • z) = 0 := by
      rw [UCP.divCoeffGrad_congr hCoeff Filter.EventuallyEq.rfl]
      exact hUP _ (hRoomD hx2)
    simpa only [B, Uh, hP0, mul_zero] using
      Regularity.Jets.divCoeffGrad_comp_affine Ahat U c hρ.ne' z
  have hTU : (T (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict (ballOpens : Set R3)] Uh := by
    have hΩ := ae_restrict_of_ae_restrict_of_subset hΩD hUval.symm
    exact (hTVal _).trans ((Affine.qmp hρ hAff).ae hΩ)
  have hNorm : Real.sqrt (∫ z in (ballOpens : Set R3), Uh z ^ 2) =
      ‖T (u : Lp ℝ 2 ((volume : Measure R3).restrict D))‖ := by
    have hI : (∫ z in (ballOpens : Set R3), Uh z ^ 2) =
        ‖T (u : Lp ℝ 2 ((volume : Measure R3).restrict D))‖ ^ 2 := by
      calc
        _ = ∫ z in (ballOpens : Set R3),
            (T (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) z) ^ 2 := by
          apply integral_congr_ae
          filter_upwards [hTU] with z hz
          exact congrArg (fun a : ℝ => a ^ 2) hz.symm
        _ = _ := by
          simpa only [L2.inner_def, Real.inner_apply, ← pow_two] using
            real_inner_self_eq_norm_sq (T (u : Lp ℝ 2 ((volume : Measure R3).restrict D)))
    rw [hI, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  -- derivative transport `U = Uh ∘ g ∘ (· - c)`
  have hfun : U = fun y => (Uh ∘ g) (y - c) := by
    funext y
    simp only [Function.comp_apply, Uh, hgApply, smul_smul, mul_inv_cancel₀ hρ.ne',
      one_smul, add_sub_cancel]
  have hDer : iteratedFDeriv ℝ n U x =
      (iteratedFDeriv ℝ n Uh (g (x - c))).compContinuousLinearMap
        (fun _ => (g : R3 →L[ℝ] R3)) := by
    rw [hfun, iteratedFDeriv_comp_sub]
    simpa only [preimage_univ, iteratedFDerivWithin_univ] using
      g.iteratedFDerivWithin_comp_right Uh uniqueDiffOn_univ (mem_univ _) n
  have hz : g (x - c) ∈ closedBall (0 : R3) (1 / 4) := by
    rw [hgApply, mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hρ)]
    have hxc : ‖x - c‖ < ρ / 4 := by
      simpa only [mem_ball, dist_eq_norm] using hx
    rw [inv_mul_le_iff₀ hρ]
    linarith
  have hJ := hJet Uh hUh hPUh _ hz
  have hT := T.le_opNorm (u : Lp ℝ 2 ((volume : Measure R3).restrict D))
  have hun : ‖(u : Lp ℝ 2 ((volume : Measure R3).restrict D))‖ = ‖u‖ := rfl
  rw [hNorm] at hJ
  calc ‖iteratedFDeriv ℝ n U x‖
      ≤ ‖iteratedFDeriv ℝ n Uh (g (x - c))‖ * ∏ _i : Fin n, ‖(g : R3 →L[ℝ] R3)‖ := by
        rw [hDer]
        exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ n Uh (g (x - c))‖ * ‖(g : R3 →L[ℝ] R3)‖ ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (Cn * (‖T‖ * ‖u‖)) * ‖(g : R3 →L[ℝ] R3)‖ ^ n := by
        gcongr
        exact hJ.trans (mul_le_mul_of_nonneg_left (hun ▸ hT) hCn.le)
    _ = Cn * ‖T‖ * ‖(g : R3 →L[ℝ] R3)‖ ^ n * ‖u‖ := by ring

/-- C3-D1.6: a jet constant uniform on a compact subset of `D`, chosen before `u`. -/
theorem harmonicRep_jet_bound_on_compact (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (K : Set R3) (hK : IsCompact K) (hKD : K ⊆ D) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : harmonicSub D hD A hA, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ n (harmonicRep D hD A hA hpos u) x‖ ≤ C * ‖u‖ := by
  have hloc : ∀ c : D, ∃ r > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : harmonicSub D hD A hA,
      ∀ x ∈ ball (c : R3) r,
        ‖iteratedFDeriv ℝ n (harmonicRep D hD A hA hpos u) x‖ ≤ C * ‖u‖ :=
    fun c => harmonicRep_local_jet_bound D hD A hA hpos c c.2 n
  choose r hr C hC hbound using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c : D => ball (c : R3) (r c))
    (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hKD hx⟩, mem_ball_self (hr _)⟩)
  refine ⟨∑ c ∈ t, C c, Finset.sum_nonneg (fun c _ => hC c), ?_⟩
  intro u x hx
  obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.mp (ht hx)
  calc _ ≤ C c * ‖u‖ := hbound c u x hxc
    _ ≤ (∑ c ∈ t, C c) * ‖u‖ :=
      mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun c _ => hC c) hct)
        (norm_nonneg _)

/-- C3-D1.7: the actual bounded derivative-evaluation map at a point of `D`. -/
def harmonicJetCLM (D : Set R3) (hD : IsOpen D) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (n : ℕ) (x : R3) (hx : x ∈ D) :
    harmonicSub D hD A hA →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => R3) ℝ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun u => iteratedFDeriv ℝ n (harmonicRep D hD A hA hpos u) x
      map_add' := fun u v => harmonicRep_iteratedFDeriv_add D hD A hA hpos n hx u v
      map_smul' := fun a u => harmonicRep_iteratedFDeriv_smul D hD A hA hpos n hx a u }
    (by
      obtain ⟨C, -, hC⟩ := harmonicRep_jet_bound_on_compact D hD A hA hpos {x}
        isCompact_singleton (singleton_subset_iff.mpr hx) n
      exact ⟨C, fun u => hC u x rfl⟩)

theorem harmonicJetCLM_apply (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (n : ℕ) (x : R3) (hx : x ∈ D) (u : harmonicSub D hD A hA) :
    harmonicJetCLM D hD A hA hpos n x hx u =
      iteratedFDeriv ℝ n (harmonicRep D hD A hA hpos u) x := rfl

/-- C3-D2 (pointwise): the native multivariate Taylor remainder of the SAME representative
along a segment inside a compact `K ⊆ D`; the constant `L` is chosen before `u`. -/
theorem harmonicRep_taylor_remainder (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (K : Set R3) (hK : IsCompact K) (hKD : K ⊆ D) (s : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u : harmonicSub D hD A hA, ∀ c h : R3,
      (∀ t ∈ Icc (0 : ℝ) 1, c + t • h ∈ K) →
      |harmonicRep D hD A hA hpos u (c + h) -
          ∑ k ∈ Finset.range (s + 1), (k ! : ℝ)⁻¹ •
            iteratedFDeriv ℝ k (harmonicRep D hD A hA hpos u) c (fun _ => h)|
        ≤ (s ! : ℝ)⁻¹ * (L * ‖u‖ * ‖h‖ ^ (s + 1)) := by
  obtain ⟨L, hL, hbound⟩ := harmonicRep_jet_bound_on_compact D hD A hA hpos K hK hKD (s + 1)
  refine ⟨L, hL, ?_⟩
  intro u c h hseg
  have hT := map_add_eq_sum_add_integral_iteratedFDeriv (n := s)
    (f := harmonicRep D hD A hA hpos u) (x := c) (y := h)
    (fun t ht => harmonicRep_contDiffAt D hD A hA hpos u (s + 1) (hKD (hseg t ht)))
  rw [hT, add_sub_cancel_left, smul_eq_mul, abs_mul, abs_inv, Nat.abs_cast]
  gcongr
  rw [← Real.norm_eq_abs]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := L * ‖u‖ * ‖h‖ ^ (s + 1))
    (f := fun t => (1 - t) ^ s • iteratedFDeriv ℝ (s + 1)
      (harmonicRep D hD A hA hpos u) (c + t • h) (fun _ => h)) (by
      intro t ht
      rw [uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have h1 : ‖(1 - t) ^ s‖ ≤ 1 := by
        rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
        exact pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1])
      have h2 : ‖iteratedFDeriv ℝ (s + 1) (harmonicRep D hD A hA hpos u) (c + t • h)
          (fun _ => h)‖ ≤ L * ‖u‖ * ‖h‖ ^ (s + 1) := by
        refine ((iteratedFDeriv ℝ (s + 1) (harmonicRep D hD A hA hpos u)
          (c + t • h)).le_opNorm _).trans ?_
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        gcongr
        exact hbound u _ (hseg t ht')
      rw [norm_smul]
      calc ‖(1 - t) ^ s‖ * _ ≤ 1 * (L * ‖u‖ * ‖h‖ ^ (s + 1)) :=
            mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = _ := one_mul _)
  simpa only [sub_zero, abs_one, mul_one] using hI

/-! ### C3-D3: the actual cellwise Taylor finite-rank operator -/

/-- The fixed orthonormal coordinate basis of `R3`. -/
abbrev coordBasis : OrthonormalBasis (Fin 3) ℝ R3 := EuclideanSpace.basisFun (Fin 3) ℝ

/-- Coordinate monomial of a basis word. -/
def wordMono {k : ℕ} (w : Fin k → Fin 3) (y : R3) : ℝ :=
  ∏ j, inner ℝ (coordBasis (w j)) y

theorem continuous_wordMono {k : ℕ} (w : Fin k → Fin 3) (c : R3) :
    Continuous fun x : R3 => wordMono w (x - c) :=
  continuous_finsetProd _ fun _ _ => continuous_const.inner (continuous_id.sub continuous_const)

theorem abs_wordMono_le {k : ℕ} (w : Fin k → Fin 3) (y : R3) :
    |wordMono w y| ≤ ‖y‖ ^ k := by
  rw [wordMono, Finset.abs_prod]
  calc ∏ j, |inner ℝ (coordBasis (w j)) y| ≤ ∏ _j : Fin k, ‖y‖ := by
        gcongr with j
        exact (abs_real_inner_le_norm _ _).trans
          (by rw [coordBasis.orthonormal.1 (w j), one_mul])
    _ = ‖y‖ ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Exact basis-word expansion of a multilinear diagonal value (`3^k` coefficients). -/
theorem multilinear_diag_expand {k : ℕ}
    (m : ContinuousMultilinearMap ℝ (fun _ : Fin k => R3) ℝ) (y : R3) :
    m (fun _ => y) = ∑ w : Fin k → Fin 3, m (fun j => coordBasis (w j)) * wordMono w y := by
  have hy : (fun _ : Fin k => y) =
      fun _ => ∑ i, inner ℝ (coordBasis i) y • coordBasis i := by
    funext _
    exact (coordBasis.sum_repr' y).symm
  rw [hy, m.map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [m.map_smul_univ, smul_eq_mul, mul_comm]
  rfl

/-- The `3^k` actual jet coefficients at a point of `D`, as one CLM. -/
def harmonicCoeffCLM (D : Set R3) (hD : IsOpen D) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (k : ℕ) (x : R3) (hx : x ∈ D) :
    harmonicSub D hD A hA →L[ℝ] ((Fin k → Fin 3) → ℝ) :=
  ContinuousLinearMap.pi fun w =>
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => R3) ℝ
      (fun j => coordBasis (w j))).comp (harmonicJetCLM D hD A hA hpos k x hx)

/-- The actual restriction CLM `E → L²(S)` of ER446. -/
def harmonicRestrict (D : Set R3) (hD : IsOpen D) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (S : Set R3) (hSD : S ⊆ D) :
    harmonicSub D hD A hA →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict S) :=
  (Lp.LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    (show (volume : Measure R3).restrict S ≤ (1 : ℝ≥0∞) • (volume : Measure R3).restrict D from
      by simpa only [one_smul] using Measure.restrict_mono_set volume hSD)).comp
    (harmonicSub D hD A hA).subtypeL

/-- Restriction to a subset is contractive, including a zero harmonic carrier. -/
theorem harmonicRestrict_norm_le_one (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (S : Set R3) (hSD : S ⊆ D) :
    ‖harmonicRestrict D hD A hA S hSD‖ ≤ 1 := by
  have hc : (1 : ℝ≥0∞) ≠ ⊤ := by simp
  have hle : (volume : Measure R3).restrict S ≤
      (1 : ℝ≥0∞) • (volume : Measure R3).restrict D := by
    simpa only [one_smul] using Measure.restrict_mono_set volume hSD
  let J : Lp ℝ 2 ((volume : Measure R3).restrict D) →L[ℝ]
      Lp ℝ 2 ((volume : Measure R3).restrict S) :=
    Lp.LpToLpOfMeasureLeSMul hc hle
  have hJ : ‖J‖ ≤ 1 := by
    simpa [J] using
      (Lp.norm_LpToLpOfMeasureLeSMul_le
        (E := ℝ) (p := (2 : ℝ≥0∞)) hc hle)
  change ‖J.comp (harmonicSub D hD A hA).subtypeL‖ ≤ 1
  calc
    ‖J.comp (harmonicSub D hD A hA).subtypeL‖
        ≤ ‖J‖ * ‖(harmonicSub D hD A hA).subtypeL‖ :=
      J.opNorm_comp_le _
    _ ≤ 1 * 1 :=
      mul_le_mul hJ (Submodule.norm_subtypeL_le _)
        (norm_nonneg (harmonicSub D hD A hA).subtypeL) zero_le_one
    _ = 1 := one_mul 1


theorem cellMono_memLp (S : Set R3) [IsFiniteMeasure ((volume : Measure R3).restrict S)]
    (Q : Set R3) (hQ : MeasurableSet Q) (c : R3) (δ : ℝ) (hδ : 0 ≤ δ)
    (hQδ : ∀ x ∈ Q, ‖x - c‖ ≤ δ) {k : ℕ} (w : Fin k → Fin 3) :
    MemLp (fun x => Q.indicator (fun x => (k ! : ℝ)⁻¹ * wordMono w (x - c)) x) 2
      ((volume : Measure R3).restrict S) := by
  have hcont : Continuous fun x : R3 => (k ! : ℝ)⁻¹ * wordMono w (x - c) :=
    continuous_const.mul (continuous_wordMono w c)
  refine MemLp.of_bound ((hcont.aestronglyMeasurable).indicator hQ) ((k ! : ℝ)⁻¹ * δ ^ k)
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Q
  · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast]
    gcongr
    exact (abs_wordMono_le w _).trans (pow_le_pow_left₀ (norm_nonneg _) (hQδ x hx) k)
  · rw [indicator_of_notMem hx, norm_zero]
    positivity

/-- The finite coefficient space: `3^k` coefficients per cell and degree `k ≤ s`. -/
abbrev CoeffSpace (N s : ℕ) : Type := ∀ p : Fin N × Fin (s + 1), (Fin p.2 → Fin 3) → ℝ

theorem coeffSpace_finrank (N s : ℕ) :
    Module.finrank ℝ (CoeffSpace N s) = N * ∑ k ∈ Finset.range (s + 1), 3 ^ k := by
  rw [Module.finrank_pi_fintype]
  calc ∑ p : Fin N × Fin (s + 1), Module.finrank ℝ ((Fin p.2 → Fin 3) → ℝ)
      = ∑ p : Fin N × Fin (s + 1), 3 ^ (p.2 : ℕ) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin]
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          Fin.sum_univ_eq_sum_range (fun k => 3 ^ k) (s + 1)]

/-- One cell monomial `1_{Q_i}(x)·(k!)⁻¹·(x−c_i)^w`. -/
def cellPhi {N s : ℕ} (Q : Fin N → Set R3) (c : Fin N → R3) (p : Fin N × Fin (s + 1))
    (w : Fin p.2 → Fin 3) (x : R3) : ℝ :=
  (Q p.1).indicator (fun x => (((p.2 : ℕ)) ! : ℝ)⁻¹ * wordMono w (x - c p.1)) x

/-- The cellwise polynomial with coefficient vector `a`. -/
def cellFun {N s : ℕ} (Q : Fin N → Set R3) (c : Fin N → R3) (a : CoeffSpace N s)
    (x : R3) : ℝ :=
  ∑ p, ∑ w, a p w * cellPhi Q c p w x

theorem cellFun_memLp (S : Set R3) [IsFiniteMeasure ((volume : Measure R3).restrict S)]
    {N s : ℕ} (Q : Fin N → Set R3) (c : Fin N → R3) (δ : ℝ) (hδ : 0 ≤ δ)
    (hQ : ∀ i, MeasurableSet (Q i)) (hQδ : ∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ)
    (a : CoeffSpace N s) :
    MemLp (cellFun Q c a) 2 ((volume : Measure R3).restrict S) := by
  unfold cellFun cellPhi
  exact memLp_finsetSum _ fun p _ => memLp_finsetSum _ fun w _ =>
    (cellMono_memLp S (Q p.1) (hQ p.1) (c p.1) δ hδ (hQδ p.1) w).const_mul (a p w)

/-- The actual finite-dimensional synthesis map into `L²(S)`. -/
def cellV (S : Set R3) [IsFiniteMeasure ((volume : Measure R3).restrict S)]
    {N : ℕ} (s : ℕ) (Q : Fin N → Set R3) (c : Fin N → R3) (δ : ℝ) (hδ : 0 ≤ δ)
    (hQ : ∀ i, MeasurableSet (Q i)) (hQδ : ∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ) :
    CoeffSpace N s →ₗ[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict S) where
  toFun a := (cellFun_memLp S Q c δ hδ hQ hQδ a).toLp (cellFun Q c a)
  map_add' a a' := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [cellFun, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r a := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [cellFun, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem cellV_ae (S : Set R3) [IsFiniteMeasure ((volume : Measure R3).restrict S)]
    {N s : ℕ} (Q : Fin N → Set R3) (c : Fin N → R3) (δ : ℝ) (hδ : 0 ≤ δ)
    (hQ : ∀ i, MeasurableSet (Q i)) (hQδ : ∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ)
    (a : CoeffSpace N s) :
    (cellV S s Q c δ hδ hQ hQδ a : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict S]
      cellFun Q c a :=
  (cellFun_memLp S Q c δ hδ hQ hQδ a).coeFn_toLp

theorem cellFun_eq_of_mem {N s : ℕ} (Q : Fin N → Set R3) (c : Fin N → R3)
    (hdisj : Pairwise (fun i j => Disjoint (Q i) (Q j))) (a : CoeffSpace N s) (x : R3)
    (i0 : Fin N) (hx : x ∈ Q i0) :
    cellFun Q c a x = ∑ k : Fin (s + 1), (((k : ℕ)) ! : ℝ)⁻¹ *
      ∑ w : Fin k → Fin 3, a (i0, k) w * wordMono w (x - c i0) := by
  simp only [cellFun, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i0]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [cellPhi, indicator_of_mem hx]
    ring
  · intro i _ hi
    have hxi : x ∉ Q i := fun h => Set.disjoint_left.mp (hdisj hi) h hx
    simp only [cellPhi, indicator_of_notMem hxi, mul_zero, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- All actual jet coefficients at all cell centres, as one CLM. -/
def coeffAll (D : Set R3) (hD : IsOpen D) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (N s : ℕ) (c : Fin N → R3) (hc : ∀ i, c i ∈ D) :
    harmonicSub D hD A hA →L[ℝ] CoeffSpace N s :=
  ContinuousLinearMap.pi fun p => harmonicCoeffCLM D hD A hA hpos p.2 (c p.1) (hc p.1)

theorem coeffAll_apply (D : Set R3) (hD : IsOpen D) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (N s : ℕ) (c : Fin N → R3) (hc : ∀ i, c i ∈ D) (u : harmonicSub D hD A hA)
    (p : Fin N × Fin (s + 1)) (w : Fin p.2 → Fin 3) :
    coeffAll D hD A hA hpos N s c hc u p w =
      iteratedFDeriv ℝ p.2 (harmonicRep D hD A hA hpos u) (c p.1)
        (fun j => coordBasis (w j)) := rfl

theorem harmonicRestrict_ae (D : Set R3) (hD : IsOpen D) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (S : Set R3) (hSD : S ⊆ D) (u : harmonicSub D hD A hA) :
    (harmonicRestrict D hD A hA S hSD u : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict S]
      ((u : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ) :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    (show (volume : Measure R3).restrict S ≤ (1 : ℝ≥0∞) • (volume : Measure R3).restrict D from
      by simpa only [one_smul] using Measure.restrict_mono_set volume hSD) _

/-- C3-D3 error: the actual cell operator against the actual restriction, pointwise in `u`. -/
theorem cell_taylor_error (D : Set R3) (hD : IsOpen D) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (S : Set R3) (hS : MeasurableSet S) (hSD : S ⊆ D)
    [IsFiniteMeasure ((volume : Measure R3).restrict S)]
    (K : Set R3) (s : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hrem : ∀ u : harmonicSub D hD A hA, ∀ c h : R3,
      (∀ t ∈ Icc (0 : ℝ) 1, c + t • h ∈ K) →
      |harmonicRep D hD A hA hpos u (c + h) -
          ∑ k ∈ Finset.range (s + 1), (k ! : ℝ)⁻¹ •
            iteratedFDeriv ℝ k (harmonicRep D hD A hA hpos u) c (fun _ => h)|
        ≤ (s ! : ℝ)⁻¹ * (L * ‖u‖ * ‖h‖ ^ (s + 1)))
    {N : ℕ} (Q : Fin N → Set R3) (c : Fin N → R3) (δ : ℝ) (hδ : 0 ≤ δ)
    (hQ : ∀ i, MeasurableSet (Q i)) (hdisj : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    (hcover : S ⊆ ⋃ i, Q i) (hc : ∀ i, c i ∈ D)
    (hgeom : ∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ ∧ ∀ t ∈ Icc (0 : ℝ) 1, c i + t • (x - c i) ∈ K)
    (u : harmonicSub D hD A hA) :
    ‖harmonicRestrict D hD A hA S hSD u -
        cellV S s Q c δ hδ hQ (fun i x hx => (hgeom i x hx).1)
          (coeffAll D hD A hA hpos N s c hc u)‖ ≤
      ((measureUnivNNReal ((volume : Measure R3).restrict S) ^
        ((2 : ℝ≥0∞).toReal⁻¹) : NNReal) : ℝ) *
        ((s ! : ℝ)⁻¹ * (L * ‖u‖ * δ ^ (s + 1))) := by
  have hC : 0 ≤ (s ! : ℝ)⁻¹ * (L * ‖u‖ * δ ^ (s + 1)) :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (mul_nonneg (mul_nonneg hL (norm_nonneg _)) (pow_nonneg hδ _))
  refine Lp.norm_le_of_ae_bound hC ?_
  have hRu := harmonicRestrict_ae D hD A hA S hSD u
  have hPu := cellV_ae S Q c δ hδ hQ (fun i x hx => (hgeom i x hx).1)
    (coeffAll D hD A hA hpos N s c hc u)
  have hrep := ae_restrict_of_ae_restrict_of_subset hSD
    (harmonicRep_spec D hD A hA hpos u).2.1
  filter_upwards [Lp.coeFn_sub (harmonicRestrict D hD A hA S hSD u)
      (cellV S s Q c δ hδ hQ (fun i x hx => (hgeom i x hx).1)
        (coeffAll D hD A hA hpos N s c hc u)), hRu, hPu, hrep,
    ae_restrict_mem hS] with x h1 h2 h3 h4 hxS
  obtain ⟨i0, hx0⟩ := mem_iUnion.mp (hcover hxS)
  obtain ⟨hδx, hseg⟩ := hgeom i0 x hx0
  have hpoly : cellFun Q c (coeffAll D hD A hA hpos N s c hc u) x =
      ∑ k ∈ Finset.range (s + 1), (k ! : ℝ)⁻¹ •
        iteratedFDeriv ℝ k (harmonicRep D hD A hA hpos u) (c i0) (fun _ => x - c i0) := by
    rw [cellFun_eq_of_mem Q c hdisj _ x i0 hx0, ← Fin.sum_univ_eq_sum_range (fun k => (k ! : ℝ)⁻¹ •
      iteratedFDeriv ℝ k (harmonicRep D hD A hA hpos u) (c i0) (fun _ => x - c i0)) (s + 1)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_eq_mul, multilinear_diag_expand]
    simp only [coeffAll_apply]
  rw [h1, Pi.sub_apply, h2, h3, ← h4, hpoly, Real.norm_eq_abs]
  have hr := hrem u (c i0) (x - c i0) hseg
  rw [add_sub_cancel] at hr
  refine hr.trans ?_
  gcongr

/-- C3-D3: for a fixed scalar coefficient, compact buffer `K ⊆ D` and order `s`, the constant
`L` is chosen first; then for EVERY finite measurable partition of `S` into cells of radius
`δ` with centres in `K` and segments in `K`, the actual cellwise Taylor operator `P` has range
dimension `≤ N·Σ_{k≤s} 3^k` and `‖R − P‖ ≤ L·δ^(s+1)`. No approximation premise is used. -/
theorem exists_cell_taylor_finite_rank (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (S : Set R3) (hS : MeasurableSet S) (hSD : S ⊆ D) (hSfin : volume S ≠ ⊤)
    (K : Set R3) (hK : IsCompact K) (hKD : K ⊆ D) (s : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (N : ℕ) (Q : Fin N → Set R3) (c : Fin N → R3) (δ : ℝ), 0 ≤ δ →
      (∀ i, MeasurableSet (Q i)) → Pairwise (fun i j => Disjoint (Q i) (Q j)) →
      S ⊆ ⋃ i, Q i → (∀ i, c i ∈ K) →
      (∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ ∧ ∀ t ∈ Icc (0 : ℝ) 1, c i + t • (x - c i) ∈ K) →
      ∃ P : harmonicSub D hD A hA →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict S),
        FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤
            N * ∑ k ∈ Finset.range (s + 1), 3 ^ k ∧
          ‖harmonicRestrict D hD A hA S hSD - P‖ ≤ L * δ ^ (s + 1) := by
  classical
  haveI : IsFiniteMeasure ((volume : Measure R3).restrict S) :=
    isFiniteMeasure_restrict.mpr hSfin
  obtain ⟨L, hL, hrem⟩ := harmonicRep_taylor_remainder D hD A hA hpos K hK hKD s
  set M : ℝ := ((measureUnivNNReal ((volume : Measure R3).restrict S) ^
    ((2 : ℝ≥0∞).toReal⁻¹) : NNReal) : ℝ) with hMdef
  have hM : 0 ≤ M := NNReal.coe_nonneg _
  refine ⟨M * ((s ! : ℝ)⁻¹ * L), by positivity, ?_⟩
  intro N Q c δ hδ hQ hdisj hcover hcK hgeom
  have hQδ : ∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ := fun i x hx => (hgeom i x hx).1
  let V := cellV S s Q c δ hδ hQ hQδ
  let Jall := coeffAll D hD A hA hpos N s c (fun i => hKD (hcK i))
  let P : harmonicSub D hD A hA →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict S) :=
    ⟨V.comp (Jall : harmonicSub D hD A hA →ₗ[ℝ] CoeffSpace N s),
      (LinearMap.continuous_of_finiteDimensional V).comp Jall.continuous⟩
  have hle : LinearMap.range P.toLinearMap ≤ LinearMap.range V :=
    LinearMap.range_comp_le_range _ _
  refine ⟨P, ?_, ?_, ?_⟩
  · -- C3-D3′: actual finite-range witness through the finite synthesis `V`
    haveI : FiniteDimensional ℝ (LinearMap.range V) := LinearMap.finiteDimensional_range V
    exact Submodule.finiteDimensional_of_le hle
  · -- explicit rank count through the finite coefficient space
    calc Module.finrank ℝ (LinearMap.range P.toLinearMap)
        ≤ Module.finrank ℝ (LinearMap.range V) := Submodule.finrank_mono hle
      _ ≤ Module.finrank ℝ (CoeffSpace N s) := LinearMap.finrank_range_le V
      _ = N * ∑ k ∈ Finset.range (s + 1), 3 ^ k := coeffSpace_finrank N s
  · -- operator-norm error from the pointwise native Taylor remainder
    have hbound : ∀ u : harmonicSub D hD A hA,
        ‖harmonicRestrict D hD A hA S hSD u - P u‖ ≤
          M * ((s ! : ℝ)⁻¹ * (L * ‖u‖ * δ ^ (s + 1))) := fun u =>
      cell_taylor_error D hD A hA hpos S hS hSD K s L hL hrem Q c δ hδ hQ hdisj hcover
        (fun i => hKD (hcK i)) hgeom u
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    rw [ContinuousLinearMap.sub_apply]
    refine (hbound u).trans (le_of_eq ?_)
    ring

end C3JetEvaluation

/-! ### C3-D5a / C3-D6a: geometry-free compactness and threshold counting

No compactness, spectral system or approximation of the actual restriction is assumed here;
both lemmas take an actual finite-range approximant as data. -/
end OAI.AnisotropicCalderon.MixedKernelConstructionTask
