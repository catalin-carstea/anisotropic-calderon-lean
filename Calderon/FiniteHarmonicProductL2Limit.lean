import Calderon.ClassicalHarmonicInteriorJetBound
import Calderon.CollaboratorLocalJetsCalcOct17
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set Filter TopologicalSpace
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity
open EnergyBridge
open _root_.OAI.AnisotropicCalderon.Affine

/-- The interior product-jet constant depends on the two coefficients and order,
but not on the number or representation of the finite harmonic product sum. -/
theorem exists_finite_harmonic_product_jet_bound
    {A1 A2 : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA1 : ContDiff ℝ ∞ A1) (hpos1 : ∀ z, (A1 z).PosDef)
    (hA2 : ContDiff ℝ ∞ A2) (hpos2 : ∀ z, (A2 z).PosDef)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (f g : Fin d → R3 → ℝ),
      (∀ i, ContDiffOn ℝ ∞ (f i) (ball (0 : R3) 2)) →
      (∀ i, ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A1 (f i) z = 0) →
      (∀ i, ContDiffOn ℝ ∞ (g i) (ball (0 : R3) 2)) →
      (∀ i, ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A2 (g i) z = 0) →
      ∀ w : Lp ℝ 2
        (((volume : Measure R3).restrict (ballOpens : Set R3)).prod
         ((volume : Measure R3).restrict (ballOpens : Set R3))),
      (w : R3 × R3 → ℝ) =ᵐ[
        (((volume : Measure R3).restrict (ballOpens : Set R3)).prod
         ((volume : Measure R3).restrict (ballOpens : Set R3)))]
        (fun p => ∑ i, f i p.1 * g i p.2) →
      ∀ p ∈ (closedBall (0 : R3) (1/4 : ℝ)) ×ˢ
              (closedBall (0 : R3) (1/4 : ℝ)),
        ‖iteratedFDeriv ℝ m (fun p : R3 × R3 => ∑ i, f i p.1 * g i p.2) p‖
          ≤ C * ‖w‖ := by
  classical
  choose c1 hc1 using exists_classical_harmonic_interior_jet_bound hA1 hpos1
  choose c2 hc2 using exists_classical_harmonic_interior_jet_bound hA2 hpos2
  let S1 : ℝ := ∑ a ∈ Finset.range (m + 1), c1 a
  let S2 : ℝ := ∑ a ∈ Finset.range (m + 1), c2 a
  have hS1 : 0 < S1 := Finset.sum_pos (fun a _ => (hc1 a).1) (by simp)
  have hS2 : 0 < S2 := Finset.sum_pos (fun a _ => (hc2 a).1) (by simp)
  refine ⟨(2 : ℝ) ^ m * S1 * S2, by positivity, ?_⟩
  intro d f g hf hfp hg hgp w hw p hp
  let B : Set R3 := ball (0 : R3) 2
  let ν : Measure R3 := (volume : Measure R3).restrict (ballOpens : Set R3)
  have hUnitFinite : (volume : Measure R3) (ballOpens : Set R3) ≠ ⊤ := by
    change (volume : Measure R3) (ball (0 : R3) 1) ≠ ⊤
    exact measure_ball_ne_top
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hUnitFinite
  let μ : Measure (R3 × R3) := ν.prod ν
  let H : R3 × R3 → ℝ := fun q => ∑ i, f i q.1 * g i q.2
  let DD : {T : Type} → [NormedAddCommGroup T] → [NormedSpace ℝ T] →
      (T → ℝ) → List T → T → ℝ :=
    fun {_} _ _ F l => l.foldr (fun v J x => fderiv ℝ J x v) F
  have hFoldCont (T : Type) [NormedAddCommGroup T] [NormedSpace ℝ T]
      (Ω : Set T) (hΩ : IsOpen Ω) (F : T → ℝ) (hF : ContDiffOn ℝ ∞ F Ω)
      (l : List T) : ContDiffOn ℝ ∞ (DD F l) Ω := by
    induction l with
    | nil => exact hF
    | cons v l ih =>
      exact (ih.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hFoldIter (T : Type) [NormedAddCommGroup T] [NormedSpace ℝ T]
      (Ω : Set T) (hΩ : IsOpen Ω) (F : T → ℝ) (hF : ContDiffOn ℝ ∞ F Ω)
      (l : List T) : ∀ x ∈ Ω,
        DD F l x = iteratedFDeriv ℝ l.length F x (fun i => l.get i) := by
    induction l with
    | nil => intro x hx; simp [DD, iteratedFDeriv_zero_apply]
    | cons v l ih =>
      intro x hx
      have he : DD F l =ᶠ[𝓝 x]
          (fun t => iteratedFDeriv ℝ l.length F t (fun i => l.get i)) := by
        filter_upwards [hΩ.mem_nhds hx] with t ht using ih t ht
      have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ l.length F) x :=
        (hF.contDiffAt (hΩ.mem_nhds hx)).differentiableAt_iteratedFDeriv
          (by exact_mod_cast (WithTop.coe_lt_top l.length))
      have hDirs : (fun i : Fin (v :: l).length => (v :: l).get i) =
          Fin.cons v (fun i => l.get i) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      change fderiv ℝ (DD F l) x v = _
      rw [he.fderiv_eq]
      simpa only [List.length_cons, hDirs, Fin.tail_cons, Fin.cons_zero] using
        (DifferentiableAt.iteratedFDeriv_succ_apply_left'
          (m := Fin.cons v (fun i => l.get i)) hD).symm
  have hPDEsum {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
      (hA : ContDiff ℝ ∞ A) (F : Fin d → R3 → ℝ)
      (hF : ∀ i, ContDiffOn ℝ ∞ (F i) B)
      (hP : ∀ i, ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A (F i) z = 0)
      (c : Fin d → ℝ) :
      ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A (fun t => ∑ i, c i * F i t) z = 0 := by
    intro z hz
    have hzB : z ∈ B := (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hz
    have hAz := hA.differentiable (by simp) z
    have hFinite : ∀ s : Finset (Fin d),
        divCoeffGrad A (fun t => ∑ i ∈ s, c i * F i t) z = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [divCoeffGrad]
      | @insert i s hi ih =>
        have hFi : ContDiffAt ℝ 2 (F i) z :=
          ((hF i).contDiffAt (isOpen_ball.mem_nhds hzB)).of_le (by simp)
        have hFs : ContDiffAt ℝ 2 (fun t => ∑ j ∈ s, c j * F j t) z :=
          (ContDiffOn.sum (fun j _ => (hF j).const_smul (c j))).contDiffAt
            (isOpen_ball.mem_nhds hzB) |>.of_le (by simp)
        simp only [Finset.sum_insert hi]
        change divCoeffGrad A ((c i) • F i + (fun t => ∑ j ∈ s, c j * F j t)) z = 0
        have hAdd := Jets.divCoeffGrad_add (u := (c i) • F i)
          (v := fun t => ∑ j ∈ s, c j * F j t) hAz (hFi.const_smul (c i)) hFs
        exact hAdd.trans (by rw [Jets.divCoeffGrad_smul (c i) hAz hFi, hP i z hz, ih]; ring)
    exact hFinite Finset.univ
  have hLinearFold (F : Fin d → R3 → ℝ)
      (hF : ∀ i, ContDiffOn ℝ ∞ (F i) B) (c : Fin d → ℝ) (l : List R3) :
      ∀ x ∈ B, DD (fun t => ∑ i, c i * F i t) l x = ∑ i, c i * DD (F i) l x := by
    induction l with
    | nil => intro x hx; rfl
    | cons v l ih =>
      intro x hx
      have he : DD (fun t => ∑ i, c i * F i t) l =ᶠ[𝓝 x]
          (fun t => ∑ i, c i * DD (F i) l t) := by
        filter_upwards [isOpen_ball.mem_nhds hx] with t ht using ih t ht
      change fderiv ℝ (DD (fun t => ∑ i, c i * F i t) l) x v = _
      rw [he.fderiv_eq, fderiv_fun_sum]
      · simp only [ContinuousLinearMap.sum_apply]
        apply Finset.sum_congr rfl
        intro i hi
        have hDi := ((hFoldCont R3 B isOpen_ball (F i) (hF i) l).contDiffAt
          (isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
        rw [fderiv_const_mul hDi (c i)]
        rfl
      · intro i hi
        exact (((hFoldCont R3 B isOpen_ball (F i) (hF i) l).contDiffAt
          (isOpen_ball.mem_nhds hx)).differentiableAt (by simp)).const_mul (c i)
  have hH : ContDiffOn ℝ ∞ H (B ×ˢ B) :=
    ContDiffOn.sum (fun i _ =>
      ((hf i).comp contDiffOn_fst (fun q hq => hq.1)).mul
      ((hg i).comp contDiffOn_snd (fun q hq => hq.2)))
  let left : R3 ⊕ R3 → Option R3 := Sum.elim some (fun _ => none)
  let right : R3 ⊕ R3 → Option R3 := Sum.elim (fun _ => none) some
  let em : R3 ⊕ R3 → R3 × R3 := Sum.elim (fun v => (v, 0)) (fun v => (0, v))
  have hWord (l : List (R3 ⊕ R3)) : ∀ q ∈ B ×ˢ B,
      DD H (l.map em) q =
        ∑ i, DD (f i) (l.filterMap left) q.1 * DD (g i) (l.filterMap right) q.2 := by
    induction l with
    | nil => intro q hq; rfl
    | cons v l ih =>
      intro q hq
      let fl : Fin d → R3 → ℝ := fun i => DD (f i) (l.filterMap left)
      let gl : Fin d → R3 → ℝ := fun i => DD (g i) (l.filterMap right)
      have he : DD H (l.map em) =ᶠ[𝓝 q] (fun t => ∑ i, fl i t.1 * gl i t.2) := by
        filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds hq] with t ht using ih t ht
      have hfD (i : Fin d) : DifferentiableAt ℝ (fl i) q.1 :=
        ((hFoldCont R3 B isOpen_ball (f i) (hf i) _).contDiffAt
          (isOpen_ball.mem_nhds hq.1)).differentiableAt (by simp)
      have hgD (i : Fin d) : DifferentiableAt ℝ (gl i) q.2 :=
        ((hFoldCont R3 B isOpen_ball (g i) (hg i) _).contDiffAt
          (isOpen_ball.mem_nhds hq.2)).differentiableAt (by simp)
      have hprod (i : Fin d) : HasFDerivAt (fun t : R3 × R3 => fl i t.1 * gl i t.2)
          ((fl i q.1) • ((fderiv ℝ (gl i) q.2).comp (ContinuousLinearMap.snd ℝ R3 R3)) +
           (gl i q.2) • ((fderiv ℝ (fl i) q.1).comp (ContinuousLinearMap.fst ℝ R3 R3))) q :=
        ((hfD i).hasFDerivAt.comp q (ContinuousLinearMap.fst ℝ R3 R3).hasFDerivAt).mul
          ((hgD i).hasFDerivAt.comp q (ContinuousLinearMap.snd ℝ R3 R3).hasFDerivAt)
      change fderiv ℝ (DD H (l.map em)) q (em v) = _
      rw [he.fderiv_eq, fderiv_fun_sum (fun i _ => (hprod i).differentiableAt)]
      simp only [ContinuousLinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(hprod i).fderiv]
      cases v with
      | inl v =>
        simp [DD, em, left, right, fl, gl, List.filterMap_cons,
          ContinuousLinearMap.comp_apply, mul_comm]
      | inr v =>
        simp [DD, em, left, right, fl, gl, List.filterMap_cons,
          ContinuousLinearMap.comp_apply]
  have hLpH : MemLp H 2 μ := (memLp_congr_ae hw).mp (Lp.memLp w)
  have hIntH : Integrable (fun q => H q ^ 2) μ := hLpH.integrable_sq
  have hIntNorm : (∫ q, H q ^ 2 ∂μ) = ‖w‖ ^ 2 := by
    calc
      _ = ∫ q, (w q) ^ 2 ∂μ := integral_congr_ae (hw.symm.fun_comp (fun t : ℝ => t ^ 2))
      _ = ∫ q, inner ℝ (w q) (w q) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun q => by simpa only [Real.norm_eq_abs, sq_abs] using
          (real_inner_self_eq_norm_sq (w q)).symm)
      _ = inner ℝ w w := (L2.inner_def w w).symm
      _ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
  have hSliceCont (F : Fin d → R3 → ℝ) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) B)
      (c : Fin d → ℝ) : ContDiffOn ℝ ∞ (fun t => ∑ i, c i * F i t) B :=
    ContDiffOn.sum (fun i _ => (hF i).const_smul (c i))
  have hSliceInt (F : Fin d → R3 → ℝ) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) B)
      (c : Fin d → ℝ) : Integrable (fun t => (∑ i, c i * F i t) ^ 2) ν := by
    have hc : ContinuousOn (fun t => (∑ i, c i * F i t) ^ 2)
        (closedBall (0 : R3) 1) :=
      ((hSliceCont F hF c).continuousOn.pow 2).mono
        (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))
    exact hc.integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      isOpen_ball.measurableSet ball_subset_closedBall hUnitFinite
  have hScalarFold {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (c : ℕ → ℝ)
      (hc : ∀ a, 0 < c a ∧ ∀ U : R3 → ℝ, ContDiffOn ℝ ∞ U B →
        (∀ z ∈ (ballOpens : Set R3), divCoeffGrad A U z = 0) →
        ∀ x ∈ closedBall (0 : R3) (1/4 : ℝ),
          ‖iteratedFDeriv ℝ a U x‖ ≤ c a * Real.sqrt (∫ z in (ballOpens : Set R3), U z ^ 2))
      (U : R3 → ℝ) (hU : ContDiffOn ℝ ∞ U B)
      (hP : ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A U z = 0)
      (l : List R3) (x : R3) (hx : x ∈ closedBall (0 : R3) (1/4 : ℝ)) :
      |DD U l x| ≤ c l.length * Real.sqrt (∫ z, U z ^ 2 ∂ν) * (l.map norm).prod := by
    have hxB : x ∈ B := closedBall_subset_ball (by norm_num : (1/4 : ℝ) < 2) hx
    rw [hFoldIter R3 B isOpen_ball U hU l x hxB]
    have he := (iteratedFDeriv ℝ l.length U x).le_opNorm (fun i => l.get i)
    have hpN : (0 : ℝ) ≤ (l.map norm).prod := List.prod_nonneg (by simp)
    have hProd : (∏ i : Fin l.length, ‖l.get i‖) = (l.map norm).prod := by
      rw [← List.prod_ofFn]
      congr 1
      simp
    rw [hProd] at he
    exact he.trans (mul_le_mul_of_nonneg_right ((hc l.length).2 U hU hP x hx) hpN)
  have hMixed (lx ly : List R3) :
      |∑ i, DD (f i) lx p.1 * DD (g i) ly p.2| ≤
        c1 lx.length * c2 ly.length * ‖w‖ * (lx.map norm).prod * (ly.map norm).prod := by
    let Y : R3 → ℝ := fun y => ∑ i, DD (f i) lx p.1 * g i y
    have hY : ContDiffOn ℝ ∞ Y B := hSliceCont g hg (fun i => DD (f i) lx p.1)
    have hYP : ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A2 Y z = 0 :=
      hPDEsum hA2 g hg hgp (fun i => DD (f i) lx p.1)
    have hIY := hSliceInt g hg (fun i => DD (f i) lx p.1)
    have hPx : (0 : ℝ) ≤ (lx.map norm).prod := List.prod_nonneg (by simp)
    have hPy : (0 : ℝ) ≤ (ly.map norm).prod := List.prod_nonneg (by simp)
    have hSquare : ∀ y ∈ (ballOpens : Set R3),
        Y y ^ 2 ≤ (c1 lx.length * (lx.map norm).prod) ^ 2 *
          (∫ x, H (x,y) ^ 2 ∂ν) := by
      intro y hy
      let U : R3 → ℝ := fun x => ∑ i, g i y * f i x
      have hU : ContDiffOn ℝ ∞ U B := hSliceCont f hf (fun i => g i y)
      have hUP : ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A1 U z = 0 :=
        hPDEsum hA1 f hf hfp (fun i => g i y)
      have hUEq : U = fun x => H (x,y) := by
        ext x
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      have hYE : DD U lx p.1 = Y y := by
        rw [hLinearFold f hf (fun i => g i y) lx p.1
          (closedBall_subset_ball (by norm_num : (1/4 : ℝ) < 2) hp.1)]
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      have hb := hScalarFold c1 hc1 U hU hUP lx p.1 hp.1
      rw [hYE, hUEq] at hb
      have hIntegral : 0 ≤ ∫ x, H (x,y) ^ 2 ∂ν := integral_nonneg (fun _ => sq_nonneg _)
      have hs := (sq_le_sq₀ (abs_nonneg (Y y))
        (mul_nonneg (mul_nonneg (hc1 lx.length).1.le (Real.sqrt_nonneg _)) hPx)).2 hb
      rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt hIntegral] at hs
      nlinarith only [hs]
    have hSquareInt : (∫ y, Y y ^ 2 ∂ν) ≤
        (c1 lx.length * (lx.map norm).prod) ^ 2 * ‖w‖ ^ 2 := by
      have hR : Integrable (fun y =>
          (c1 lx.length * (lx.map norm).prod) ^ 2 * (∫ x, H (x,y) ^ 2 ∂ν)) ν :=
        hIntH.integral_prod_right.const_mul _
      have hi := integral_mono_ae hIY hR
        (by filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with y hy
            using hSquare y hy)
      rw [integral_const_mul] at hi
      have hFubini : (∫ y, ∫ x, H (x,y) ^ 2 ∂ν ∂ν) = ∫ q, H q ^ 2 ∂μ :=
        (integral_integral_swap hIntH).symm.trans (integral_prod _ hIntH).symm
      rwa [hFubini, hIntNorm] at hi
    have hcx : 0 < c1 lx.length := (hc1 lx.length).1
    have hRoot : Real.sqrt (∫ y, Y y ^ 2 ∂ν) ≤ c1 lx.length * (lx.map norm).prod * ‖w‖ := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      simpa only [mul_pow, mul_assoc] using hSquareInt
    have hYE : DD Y ly p.2 = ∑ i, DD (f i) lx p.1 * DD (g i) ly p.2 :=
      hLinearFold g hg (fun i => DD (f i) lx p.1) ly p.2
        (closedBall_subset_ball (by norm_num : (1/4 : ℝ) < 2) hp.2)
    have hb := hScalarFold c2 hc2 Y hY hYP ly p.2 hp.2
    rw [hYE] at hb
    calc
      _ ≤ c2 ly.length * Real.sqrt (∫ y, Y y ^ 2 ∂ν) * (ly.map norm).prod := hb
      _ ≤ c2 ly.length * (c1 lx.length * (lx.map norm).prod * ‖w‖) * (ly.map norm).prod :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hRoot (hc2 ly.length).1.le) hPy
      _ = _ := by ring
  have hNormSplit (l : List (R3 ⊕ R3)) :
      ((l.filterMap left).map norm).prod * ((l.filterMap right).map norm).prod =
        (l.map (fun t => ‖em t‖)).prod := by
    induction l with
    | nil => simp
    | cons v l ih =>
      cases v <;> simp [left, right, em, List.filterMap_cons, ih, mul_assoc,
        mul_left_comm, mul_comm, Prod.norm_def]
  have hC1 (a : ℕ) (ha : a ≤ m) : c1 a ≤ S1 :=
    Finset.single_le_sum (fun b _ => (hc1 b).1.le) (Finset.mem_range.mpr (by omega))
  have hC2 (a : ℕ) (ha : a ≤ m) : c2 a ≤ S2 :=
    Finset.single_le_sum (fun b _ => (hc2 b).1.le) (Finset.mem_range.mpr (by omega))
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro z
  let z' : Fin m → Bool → R3 × R3 := fun i b => if b then (0,(z i).2) else ((z i).1,0)
  have hDecompose : (fun i => ∑ b : Bool, z' i b) = z := by
    ext i <;> simp [z']
  have hExpand := (iteratedFDeriv ℝ m H p).toMultilinearMap.map_sum z'
  rw [hDecompose] at hExpand
  have hExpandNative : (iteratedFDeriv ℝ m H p) z =
      ∑ r : Fin m → Bool, (iteratedFDeriv ℝ m H p) (fun i => z' i (r i)) := by
    simpa only [ContinuousMultilinearMap.coe_coe] using hExpand
  change ‖(iteratedFDeriv ℝ m H p) z‖ ≤ _
  rw [hExpandNative]
  apply (norm_sum_le _ _).trans
  have hTerm (s : Fin m → Bool) :
      ‖(iteratedFDeriv ℝ m H p) (fun i => z' i (s i))‖ ≤
        S1 * S2 * ‖w‖ * ∏ i, ‖z i‖ := by
    let l : List (R3 ⊕ R3) := List.ofFn (fun i => if s i then Sum.inr (z i).2 else Sum.inl (z i).1)
    have hLen : l.length = m := List.length_ofFn (f := fun i : Fin m =>
      if s i then Sum.inr (z i).2 else Sum.inl (z i).1)
    have hLeftLen : (l.filterMap left).length ≤ m :=
      (List.length_filterMap_le left l).trans_eq hLen
    have hRightLen : (l.filterMap right).length ≤ m :=
      (List.length_filterMap_le right l).trans_eq hLen
    have hMap : l.map em = List.ofFn (fun i => z' i (s i)) := by
      simp only [l, List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      change em (if s i then Sum.inr (z i).2 else Sum.inl (z i).1) = z' i (s i)
      cases hs : s i <;> simp [em, z', hs]
    have hpB : p ∈ B ×ˢ B :=
      ⟨closedBall_subset_ball (by norm_num : (1/4 : ℝ) < 2) hp.1,
       closedBall_subset_ball (by norm_num : (1/4 : ℝ) < 2) hp.2⟩
    have hEval : (iteratedFDeriv ℝ m H p) (fun i => z' i (s i)) =
        ∑ i, DD (f i) (l.filterMap left) p.1 * DD (g i) (l.filterMap right) p.2 := by
      have hFoldOfFn (v : Fin m → R3 × R3) :
          DD H (List.ofFn v) p = (iteratedFDeriv ℝ m H p) v := by
        have he := hFoldIter (R3 × R3) (B ×ˢ B) (isOpen_ball.prod isOpen_ball)
          H hH (List.ofFn v) p hpB
        have hTuple : (⟨(List.ofFn v).length,(List.ofFn v).get⟩ :
            Σ k : ℕ, Fin k → R3 × R3) = ⟨m,v⟩ :=
          List.equivSigmaTuple.apply_symm_apply ⟨m,v⟩
        have hEvalTuple := congrArg
          (fun z : Σ k : ℕ, Fin k → R3 × R3 => (iteratedFDeriv ℝ z.1 H p) z.2) hTuple
        exact he.trans hEvalTuple
      have he := hWord l p hpB
      rw [hMap, hFoldOfFn] at he
      exact he
    rw [hEval, Real.norm_eq_abs]
    have hSplit : ((l.filterMap left).map norm).prod * ((l.filterMap right).map norm).prod
        ≤ ∏ i, ‖z i‖ := by
      rw [hNormSplit]
      simp only [l, List.map_ofFn, List.prod_ofFn]
      apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      intro i hi
      cases hs : s i
      · simpa [em, hs] using norm_fst_le (z i)
      · simpa [em, hs] using norm_snd_le (z i)
    calc
      _ ≤ c1 (l.filterMap left).length * c2 (l.filterMap right).length * ‖w‖ *
          ((l.filterMap left).map norm).prod * ((l.filterMap right).map norm).prod :=
        hMixed _ _
      _ = (c1 (l.filterMap left).length * c2 (l.filterMap right).length) * ‖w‖ *
          (((l.filterMap left).map norm).prod * ((l.filterMap right).map norm).prod) := by ring
      _ ≤ (S1 * S2) * ‖w‖ * (∏ i, ‖z i‖) := by
        have hCC : c1 (l.filterMap left).length * c2 (l.filterMap right).length ≤ S1 * S2 :=
          mul_le_mul (hC1 _ hLeftLen) (hC2 _ hRightLen) (hc2 _).1.le hS1.le
        exact mul_le_mul (mul_le_mul_of_nonneg_right hCC (norm_nonneg _)) hSplit
          (mul_nonneg (List.prod_nonneg (by simp)) (List.prod_nonneg (by simp)))
          (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ _s : Fin m → Bool, S1 * S2 * ‖w‖ * ∏ i, ‖z i‖ :=
      Finset.sum_le_sum (fun s _ => hTerm s)
    _ = ((2 : ℝ) ^ m * S1 * S2 * ‖w‖) * ∏ i, ‖z i‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

/-- A native L2 limit of finite products of the two fixed scalar harmonic
families has one jointly smooth representative solving both original equations. -/
theorem exists_contDiffOn_of_tendsto_L2_harmonic_product_sums
    {A1 A2 : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA1 : ContDiff ℝ ∞ A1) (hpos1 : ∀ z, (A1 z).PosDef)
    (hA2 : ContDiff ℝ ∞ A2) (hpos2 : ∀ z, (A2 z).PosDef)
    (d : ℕ → ℕ) (f g : (j : ℕ) → Fin (d j) → R3 → ℝ)
    (hf : ∀ j i, ContDiffOn ℝ ∞ (f j i) (ball (0 : R3) 2))
    (hfp : ∀ j i, ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A1 (f j i) z = 0)
    (hg : ∀ j i, ContDiffOn ℝ ∞ (g j i) (ball (0 : R3) 2))
    (hgp : ∀ j i, ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A2 (g j i) z = 0)
    (v : ℕ → Lp ℝ 2
      (((volume : Measure R3).restrict (ballOpens : Set R3)).prod
       ((volume : Measure R3).restrict (ballOpens : Set R3))))
    (w : Lp ℝ 2
      (((volume : Measure R3).restrict (ballOpens : Set R3)).prod
       ((volume : Measure R3).restrict (ballOpens : Set R3))))
    (hv : ∀ j, (v j : R3 × R3 → ℝ) =ᵐ[
      (((volume : Measure R3).restrict (ballOpens : Set R3)).prod
       ((volume : Measure R3).restrict (ballOpens : Set R3)))]
      (fun p => ∑ i, f j i p.1 * g j i p.2))
    (hlim : Tendsto v atTop (𝓝 w)) :
    let O : Set (R3 × R3) :=
      (ball (0 : R3) (1/4 : ℝ)) ×ˢ (ball (0 : R3) (1/4 : ℝ))
    ∃ H : R3 × R3 → ℝ,
      ContDiffOn ℝ ∞ H O ∧
      H =ᵐ[
        ((((volume : Measure R3).restrict (ballOpens : Set R3)).prod
          ((volume : Measure R3).restrict (ballOpens : Set R3))).restrict O)]
        (w : R3 × R3 → ℝ) ∧
      (∀ p ∈ O, divCoeffGrad A1 (fun x => H (x,p.2)) p.1 = 0) ∧
      (∀ p ∈ O, divCoeffGrad A2 (fun y => H (p.1,y)) p.2 = 0) ∧
      (∀ m : ℕ, TendstoUniformlyOn
        (fun j => iteratedFDeriv ℝ m
          (fun p : R3 × R3 => ∑ i, f j i p.1 * g j i p.2))
        (iteratedFDeriv ℝ m H) atTop O) := by
  classical
  let B : Set R3 := ball (0 : R3) 2
  let V : Set R3 := ball (0 : R3) (1/4 : ℝ)
  let O : Set (R3 × R3) := V ×ˢ V
  let μ : Measure (R3 × R3) :=
    (((volume : Measure R3).restrict (ballOpens : Set R3)).prod
     ((volume : Measure R3).restrict (ballOpens : Set R3)))
  let Hs : ℕ → R3 × R3 → ℝ := fun j p => ∑ i, f j i p.1 * g j i p.2
  have hO : IsOpen O := isOpen_ball.prod isOpen_ball
  have hB : IsOpen (B ×ˢ B) := isOpen_ball.prod isOpen_ball
  have hOB : O ⊆ B ×ˢ B :=
    Set.prod_mono (ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 2))
      (ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 2))
  have hHs (j : ℕ) : ContDiffOn ℝ ∞ (Hs j) (B ×ˢ B) :=
    ContDiffOn.sum (fun i _ =>
      ((hf j i).comp contDiffOn_fst (fun p hp => hp.1)).mul
      ((hg j i).comp contDiffOn_snd (fun p hp => hp.2)))
  choose C hC using exists_finite_harmonic_product_jet_bound hA1 hpos1 hA2 hpos2
  have hNeg {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
      (U : R3 → ℝ) (hU : ContDiffOn ℝ ∞ U B)
      (hP : ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A U z = 0) :
      ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A (-U) z = 0 := by
    intro z hz
    have hzB : z ∈ B := ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz
    have hUz : ContDiffAt ℝ 2 U z :=
      (hU.contDiffAt (isOpen_ball.mem_nhds hzB)).of_le (by simp)
    have he := Jets.divCoeffGrad_smul (-1 : ℝ) (hA.differentiable (by simp) z) hUz
    simpa only [neg_one_smul, hP z hz, mul_zero] using he
  have hDifference (m j k : ℕ) (p : R3 × R3) (hp : p ∈ O) :
      ‖iteratedFDeriv ℝ m (Hs j) p - iteratedFDeriv ℝ m (Hs k) p‖ ≤ C m * ‖v j - v k‖ := by
    let F : Fin (d j + d k) → R3 → ℝ := Fin.addCases (f j) (fun i => -f k i)
    let G : Fin (d j + d k) → R3 → ℝ := Fin.addCases (g j) (g k)
    have hF (i : Fin (d j + d k)) : ContDiffOn ℝ ∞ (F i) B := by
      refine Fin.addCases ?_ ?_ i
      · intro t
        simpa only [F, G, B, Fin.addCases_left] using hf j t
      · intro t
        have hNeg : ContDiffOn ℝ ∞ (-f k t) (ball (0 : R3) 2) :=
          ((hf k t).neg).congr (fun x _ => rfl)
        simpa only [F, G, B, Fin.addCases_right] using hNeg
    have hFP (i : Fin (d j + d k)) :
        ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A1 (F i) z = 0 := by
      refine Fin.addCases ?_ ?_ i
      · intro t
        simpa only [F, G, B, Fin.addCases_left] using hfp j t
      · intro t
        simpa only [F, G, B, Fin.addCases_right] using hNeg hA1 (f k t) (hf k t) (hfp k t)
    have hG (i : Fin (d j + d k)) : ContDiffOn ℝ ∞ (G i) B := by
      refine Fin.addCases ?_ ?_ i
      · intro t
        simpa only [F, G, B, Fin.addCases_left] using hg j t
      · intro t
        simpa only [F, G, B, Fin.addCases_right] using hg k t
    have hGP (i : Fin (d j + d k)) :
        ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A2 (G i) z = 0 := by
      refine Fin.addCases ?_ ?_ i
      · intro t
        simpa only [F, G, B, Fin.addCases_left] using hgp j t
      · intro t
        simpa only [F, G, B, Fin.addCases_right] using hgp k t
    have he : (fun p : R3 × R3 => ∑ i, F i p.1 * G i p.2) = Hs j - Hs k := by
      ext q
      simp [F, G, Hs, Fin.sum_univ_add, sub_eq_add_neg, Finset.sum_neg_distrib]
    have hvd : (v j - v k : Lp ℝ 2 μ) =ᵐ[μ] (fun q => ∑ i, F i q.1 * G i q.2) := by
      rw [he]
      filter_upwards [Lp.coeFn_sub (v j) (v k), hv j, hv k] with q hq hj hk
      simpa only [Pi.sub_apply, hj, hk] using hq
    have hpQ : p ∈ closedBall (0 : R3) (1/4 : ℝ) ×ˢ closedBall (0 : R3) (1/4 : ℝ) :=
      ⟨ball_subset_closedBall hp.1, ball_subset_closedBall hp.2⟩
    have hb := (hC m).2 (d j + d k) F G hF hFP hG hGP (v j - v k) hvd p hpQ
    rw [he, iteratedFDeriv_sub_apply
      (((hHs j).contDiffAt (hB.mem_nhds (hOB hp))).of_le (by simp))
      (((hHs k).contDiffAt (hB.mem_nhds (hOB hp))).of_le (by simp))] at hb
    exact hb
  have hCauchy (m : ℕ) : UniformCauchySeqOn (fun j => iteratedFDeriv ℝ m (Hs j)) atTop O := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have hCm : 0 < C m := (hC m).1
    obtain ⟨J, hJ⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq (ε / (C m + 1)) (by positivity)
    refine ⟨J, fun j hj k hk p hp => ?_⟩
    have hjk : ‖v j - v k‖ < ε / (C m + 1) := by
      simpa only [dist_eq_norm] using hJ j hj k hk
    calc
      dist (iteratedFDeriv ℝ m (Hs j) p) (iteratedFDeriv ℝ m (Hs k) p)
          = ‖iteratedFDeriv ℝ m (Hs j) p - iteratedFDeriv ℝ m (Hs k) p‖ := dist_eq_norm _ _
      _ ≤ C m * ‖v j - v k‖ := hDifference m j k p hp
      _ ≤ (C m + 1) * ‖v j - v k‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C m + 1) * (ε / (C m + 1)) := mul_lt_mul_of_pos_left hjk (by positivity)
      _ = ε := mul_div_cancel₀ ε (by positivity)
  letI (m : ℕ) : CompleteSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ) :=
    ContinuousMultilinearMap.instCompleteSpace (𝕜 := ℝ)
      (E := fun _ : Fin m => R3 × R3) (F := ℝ)
  let G : (m : ℕ) → R3 × R3 →
      ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ :=
    fun m p => limUnder atTop (fun j => iteratedFDeriv ℝ m (Hs j) p)
  have hT (m : ℕ) : TendstoUniformlyOn (fun j => iteratedFDeriv ℝ m (Hs j)) (G m) atTop O :=
    (hCauchy m).tendstoUniformlyOn_of_tendsto
      (fun p hp => ((hCauchy m).cauchySeq hp).tendsto_limUnder)
  have hCont (m : ℕ) : ContinuousOn (G m) O := by
    apply (hT m).continuousOn
    apply (Eventually.of_forall (f := atTop) (fun j => ?_)).frequently
    have hc := ((hHs j).mono hOB).continuousOn_iteratedFDerivWithin (m := m) (by simp) hO.uniqueDiffOn
    exact hc.congr (fun p hp => (iteratedFDerivWithin_of_isOpen m hO hp).symm)
  have hCurry (m : ℕ) : TendstoUniformlyOn
      (fun j p => (iteratedFDeriv ℝ (m + 1) (Hs j) p).curryLeft)
      (fun p => (G (m + 1) p).curryLeft) atTop O := by
    let C : ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ →L[ℝ]
        ((R3 × R3) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    have hFun : (C : ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ →
        ((R3 × R3) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ)) =
        fun L => L.curryLeft := rfl
    have hUC : UniformContinuous (fun L :
        ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ => L.curryLeft) := by
      let A : ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ →+
          ((R3 × R3) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ) := C.toLinearMap.toAddMonoidHom
      have hA : Continuous (A : ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ →
          ((R3 × R3) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ)) := C.continuous
      have hAU : UniformContinuous (A : ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ →
          ((R3 × R3) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ)) := uniformContinuous_addMonoidHom_of_continuous hA
      have hAFun : (A : ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ →
          ((R3 × R3) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ)) = fun L => L.curryLeft := hFun
      exact hAFun ▸ hAU
    intro E hE
    exact (hT (m+1)) _ (hUC hE)

  let H : R3 × R3 → ℝ := fun p => (G 0 p).curry0
  let series : R3 × R3 → FormalMultilinearSeries ℝ (R3 × R3) ℝ := fun p m => G m p
  have hTaylor (k : ℕ) : HasFTaylorSeriesUpToOn (k : ℕ∞) H series O := by
    refine ⟨fun p _ => rfl, ?_, ?_⟩
    · intro m hm p hp
      have hm' : m < k := by exact_mod_cast hm
      apply (hasFDerivAt_of_tendstoUniformlyOn (l := atTop) hO
        (f := fun j => iteratedFDeriv ℝ m (Hs j))
        (f' := fun j p => (iteratedFDeriv ℝ (m + 1) (Hs j) p).curryLeft)
        (hCurry m) (fun j q hq => ?_) (fun q hq => (hT m).tendsto_at hq) hp).hasFDerivWithinAt
      have hd := (((hHs j).mono hOB).contDiffAt (hO.mem_nhds hq)).differentiableAt_iteratedFDeriv
        (m := m) (by exact_mod_cast (WithTop.coe_lt_top m))
      convert! hd.hasFDerivAt using 1 <;> rfl
    · intro m hm
      exact hCont m
  have hH : ContDiffOn ℝ ∞ H O := contDiffOn_infty.mpr (fun k => (hTaylor k).contDiffOn)
  have hJets (m : ℕ) (p : R3 × R3) (hp : p ∈ O) : G m p = iteratedFDeriv ℝ m H p := by
    exact ((hTaylor m).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hO.uniqueDiffOn hp).trans
      (iteratedFDerivWithin_of_isOpen m hO hp)
  have hUniform (m : ℕ) : TendstoUniformlyOn (fun j => iteratedFDeriv ℝ m (Hs j))
      (iteratedFDeriv ℝ m H) atTop O := by
    have ht := hT m
    rw [Metric.tendstoUniformlyOn_iff] at ht ⊢
    intro ε hε
    filter_upwards [ht ε hε] with j hj p hp
    simpa only [← hJets m p hp] using hj p hp
  have hPoint (p : R3 × R3) (hp : p ∈ O) : Tendsto (fun j => Hs j p) atTop (𝓝 (H p)) := by
    have ht := ((continuousMultilinearCurryFin0 ℝ (R3 × R3) ℝ).continuous.tendsto (G 0 p)).comp
      ((hT 0).tendsto_at hp)
    exact ht.congr (fun j => by simp [Function.comp])
  have hAE : H =ᵐ[μ.restrict O] (w : R3 × R3 → ℝ) := by
    obtain ⟨ns, hns, hnsAE⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
    have hall : ∀ᵐ p ∂μ, ∀ j, (v j : R3 × R3 → ℝ) p = Hs j p := ae_all_iff.mpr hv
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_of_ae hnsAE,
      ae_restrict_mem hO.measurableSet] with p hp hnsP hpO
    have hHlim := (hPoint p hpO).comp hns.tendsto_atTop
    have hwlim : Tendsto (fun j => Hs (ns j) p) atTop (𝓝 (w p)) :=
      hnsP.congr (fun j => hp (ns j))
    exact tendsto_nhds_unique hHlim hwlim
  have hPDEsum {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
      (hA : ContDiff ℝ ∞ A) (j : ℕ) (F : Fin (d j) → R3 → ℝ)
      (hF : ∀ i, ContDiffOn ℝ ∞ (F i) B)
      (hP : ∀ i, ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A (F i) z = 0)
      (c : Fin (d j) → ℝ) :
      ∀ z ∈ (ballOpens : Set R3), divCoeffGrad A (fun t => ∑ i, c i * F i t) z = 0 := by
    intro z hz
    have hzB : z ∈ B := ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz
    have hAz := hA.differentiable (by simp) z
    have hFinite : ∀ s : Finset (Fin (d j)),
        divCoeffGrad A (fun t => ∑ i ∈ s, c i * F i t) z = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [divCoeffGrad]
      | @insert i s hi ih =>
        have hFi : ContDiffAt ℝ 2 (F i) z :=
          ((hF i).contDiffAt (isOpen_ball.mem_nhds hzB)).of_le (by simp)
        have hFs : ContDiffAt ℝ 2 (fun t => ∑ l ∈ s, c l * F l t) z :=
          (ContDiffOn.sum (fun l _ => (hF l).const_smul (c l))).contDiffAt
            (isOpen_ball.mem_nhds hzB) |>.of_le (by simp)
        have hAdd := Jets.divCoeffGrad_add (u := (c i) • F i)
          (v := fun t => ∑ l ∈ s, c l * F l t) hAz (hFi.const_smul (c i)) hFs
        simp only [Finset.sum_insert hi]
        change divCoeffGrad A ((c i) • F i + (fun t => ∑ l ∈ s, c l * F l t)) z = 0
        exact hAdd.trans (by rw [Jets.divCoeffGrad_smul (c i) hAz hFi, hP i z hz, ih]; ring)
    exact hFinite Finset.univ
  have hOperatorLimit {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
      (hA : ContDiff ℝ ∞ A) (U : ℕ → R3 → ℝ) (U0 : R3 → ℝ) (x : R3)
      (hU : ∀ j, ContDiffAt ℝ 2 (U j) x) (hU0 : ContDiffAt ℝ 2 U0 x)
      (hP : ∀ j, divCoeffGrad A (U j) x = 0)
      (h1 : ∀ a : R3, Tendsto (fun j => fderiv ℝ (U j) x a) atTop (𝓝 (fderiv ℝ U0 x a)))
      (h2 : ∀ a b : R3, Tendsto (fun j => fderiv ℝ (fderiv ℝ (U j)) x a b) atTop
        (𝓝 (fderiv ℝ (fderiv ℝ U0) x a b))) : divCoeffGrad A U0 x = 0 := by
    have hAt := hA.differentiable (by simp) x
    have ht : Tendsto (fun j => ∑ i : Fin 3, ∑ k : Fin 3,
        (fderiv ℝ (fun z => A z i k) x (EuclideanSpace.single i 1) *
          fderiv ℝ (U j) x (EuclideanSpace.single k 1) +
        A x i k * fderiv ℝ (fderiv ℝ (U j)) x (EuclideanSpace.single i 1) (EuclideanSpace.single k 1)))
        atTop (𝓝 (∑ i : Fin 3, ∑ k : Fin 3,
        (fderiv ℝ (fun z => A z i k) x (EuclideanSpace.single i 1) *
          fderiv ℝ U0 x (EuclideanSpace.single k 1) +
        A x i k * fderiv ℝ (fderiv ℝ U0) x (EuclideanSpace.single i 1) (EuclideanSpace.single k 1)))) := by
      apply tendsto_finsetSum
      intro i hi
      apply tendsto_finsetSum
      intro k hk
      exact (tendsto_const_nhds.mul (h1 _)).add (tendsto_const_nhds.mul (h2 _ _))
    have ht' : Tendsto (fun j => divCoeffGrad A (U j) x) atTop (𝓝 (divCoeffGrad A U0 x)) := by
      rw [Jets.divCoeffGrad_eq_jet hAt hU0]
      exact ht.congr (fun j => (Jets.divCoeffGrad_eq_jet hAt (hU j)).symm)
    have he : (fun j => divCoeffGrad A (U j) x) = fun _ : ℕ => (0 : ℝ) := funext hP
    rw [he] at ht'
    exact tendsto_nhds_unique ht' tendsto_const_nhds
  have hLeftSmooth (F : R3 × R3 → ℝ) (hF : ContDiffOn ℝ ∞ F O)
      (p : R3 × R3) (hp : p ∈ O) : ContDiffOn ℝ ∞ (fun x => F (x,p.2)) V :=
    hF.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => ⟨hx, hp.2⟩)
  have hRightSmooth (F : R3 × R3 → ℝ) (hF : ContDiffOn ℝ ∞ F O)
      (p : R3 × R3) (hp : p ∈ O) : ContDiffOn ℝ ∞ (fun y => F (p.1,y)) V :=
    hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨hp.1, hy⟩)
  have hLeft1 (F : R3 × R3 → ℝ) (hF : ContDiffOn ℝ ∞ F O)
      (p : R3 × R3) (hp : p ∈ O) (a : R3) :
      fderiv ℝ (fun x => F (x,p.2)) p.1 a = fderiv ℝ F p (a,0) := by
    have hd := (hF.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
    have he := (hd.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)).fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using
      congrArg (fun L : R3 →L[ℝ] ℝ => L a) he
  have hRight1 (F : R3 × R3 → ℝ) (hF : ContDiffOn ℝ ∞ F O)
      (p : R3 × R3) (hp : p ∈ O) (a : R3) :
      fderiv ℝ (fun y => F (p.1,y)) p.2 a = fderiv ℝ F p (0,a) := by
    have hd := (hF.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
    have he := (hd.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)).fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using
      congrArg (fun L : R3 →L[ℝ] ℝ => L a) he
  have hLeft2 (F : R3 × R3 → ℝ) (hF : ContDiffOn ℝ ∞ F O)
      (p : R3 × R3) (hp : p ∈ O) (a b : R3) :
      fderiv ℝ (fderiv ℝ (fun x => F (x,p.2))) p.1 a b =
        iteratedFDeriv ℝ 2 F p ![(a,0),(b,0)] := by
    let J : R3 × R3 → ℝ := fun q => fderiv ℝ F q (b,0)
    have hJ : ContDiffOn ℝ ∞ J O :=
      (hF.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
    have he : (fun x => fderiv ℝ (fun z => F (z,p.2)) x b) =ᶠ[𝓝 p.1] (fun x => J (x,p.2)) := by
      filter_upwards [isOpen_ball.mem_nhds hp.1] with x hx using hLeft1 F hF (x,p.2) ⟨hx,hp.2⟩ b
    have hS : ContDiffAt ℝ 2 (fun x => F (x,p.2)) p.1 :=
      ((hLeftSmooth F hF p hp).contDiffAt (isOpen_ball.mem_nhds hp.1)).of_le (by simp)
    rw [← Jets.fderiv_fderiv_apply hS b a, he.fderiv_eq, hLeft1 J hJ p hp a]
    have hDF : DifferentiableAt ℝ (fderiv ℝ F) p :=
      ((hF.fderiv_of_isOpen hO (m := 1) (by simp)).contDiffAt
        (hO.mem_nhds hp)).differentiableAt (by norm_num)
    change fderiv ℝ (fun q => fderiv ℝ F q (b,0)) p (a,0) = _
    have hConst : fderiv ℝ (fun (_ : R3 × R3) => ((b,0) : R3 × R3)) p = 0 :=
      fderiv_const_apply ((b,0) : R3 × R3)
    rw [fderiv_clm_apply hDF (differentiableAt_const _), hConst]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, zero_apply,
      ContinuousLinearMap.map_zero, zero_add, ContinuousLinearMap.flip_apply,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hRight2 (F : R3 × R3 → ℝ) (hF : ContDiffOn ℝ ∞ F O)
      (p : R3 × R3) (hp : p ∈ O) (a b : R3) :
      fderiv ℝ (fderiv ℝ (fun y => F (p.1,y))) p.2 a b =
        iteratedFDeriv ℝ 2 F p ![(0,a),(0,b)] := by
    let J : R3 × R3 → ℝ := fun q => fderiv ℝ F q (0,b)
    have hJ : ContDiffOn ℝ ∞ J O :=
      (hF.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
    have he : (fun y => fderiv ℝ (fun z => F (p.1,z)) y b) =ᶠ[𝓝 p.2] (fun y => J (p.1,y)) := by
      filter_upwards [isOpen_ball.mem_nhds hp.2] with y hy using hRight1 F hF (p.1,y) ⟨hp.1,hy⟩ b
    have hS : ContDiffAt ℝ 2 (fun y => F (p.1,y)) p.2 :=
      ((hRightSmooth F hF p hp).contDiffAt (isOpen_ball.mem_nhds hp.2)).of_le (by simp)
    rw [← Jets.fderiv_fderiv_apply hS b a, he.fderiv_eq, hRight1 J hJ p hp a]
    have hDF : DifferentiableAt ℝ (fderiv ℝ F) p :=
      ((hF.fderiv_of_isOpen hO (m := 1) (by simp)).contDiffAt
        (hO.mem_nhds hp)).differentiableAt (by norm_num)
    change fderiv ℝ (fun q => fderiv ℝ F q (0,b)) p (0,a) = _
    have hConst : fderiv ℝ (fun (_ : R3 × R3) => ((0,b) : R3 × R3)) p = 0 :=
      fderiv_const_apply ((0,b) : R3 × R3)
    rw [fderiv_clm_apply hDF (differentiableAt_const _), hConst]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, zero_apply,
      ContinuousLinearMap.map_zero, zero_add, ContinuousLinearMap.flip_apply,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hEval (m : ℕ) (p : R3 × R3) (hp : p ∈ O) (a : Fin m → R3 × R3) :
      Tendsto (fun j => iteratedFDeriv ℝ m (Hs j) p a) atTop (𝓝 (iteratedFDeriv ℝ m H p a)) := by
    have hc : Continuous (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ => L a) :=
      by fun_prop
    exact (hc.tendsto _).comp ((hUniform m).tendsto_at hp)
  refine ⟨H, hH, hAE, ?_, ?_, hUniform⟩
  · intro p hp
    let U : ℕ → R3 → ℝ := fun j x => Hs j (x,p.2)
    let U0 : R3 → ℝ := fun x => H (x,p.2)
    apply hOperatorLimit hA1 U U0 p.1
    · intro j
      exact ((hLeftSmooth (Hs j) ((hHs j).mono hOB) p hp).contDiffAt
        (isOpen_ball.mem_nhds hp.1)).of_le (by simp)
    · exact ((hLeftSmooth H hH p hp).contDiffAt (isOpen_ball.mem_nhds hp.1)).of_le (by simp)
    · intro j
      have he := hPDEsum hA1 j (f j) (hf j) (hfp j) (fun i => g j i p.2) p.1
        (ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1) hp.1)
      have hFun : (fun x => ∑ i, g j i p.2 * f j i x) = U j := by
        ext x
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      rwa [hFun] at he
    · intro a
      have ht := hEval 1 p hp (fun _ => (a,0))
      simp only [iteratedFDeriv_one_apply] at ht
      rw [← hLeft1 H hH p hp a] at ht
      exact ht.congr (fun j => (hLeft1 (Hs j) ((hHs j).mono hOB) p hp a).symm)
    · intro a b
      have ht := hEval 2 p hp ![(a,0),(b,0)]
      rw [← hLeft2 H hH p hp a b] at ht
      exact ht.congr (fun j => (hLeft2 (Hs j) ((hHs j).mono hOB) p hp a b).symm)
  · intro p hp
    let U : ℕ → R3 → ℝ := fun j y => Hs j (p.1,y)
    let U0 : R3 → ℝ := fun y => H (p.1,y)
    apply hOperatorLimit hA2 U U0 p.2
    · intro j
      exact ((hRightSmooth (Hs j) ((hHs j).mono hOB) p hp).contDiffAt
        (isOpen_ball.mem_nhds hp.2)).of_le (by simp)
    · exact ((hRightSmooth H hH p hp).contDiffAt (isOpen_ball.mem_nhds hp.2)).of_le (by simp)
    · intro j
      exact hPDEsum hA2 j (g j) (hg j) (hgp j) (fun i => f j i p.1) p.2
        (ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1) hp.2)
    · intro a
      have ht := hEval 1 p hp (fun _ => (0,a))
      simp only [iteratedFDeriv_one_apply] at ht
      rw [← hRight1 H hH p hp a] at ht
      exact ht.congr (fun j => (hRight1 (Hs j) ((hHs j).mono hOB) p hp a).symm)
    · intro a b
      have ht := hEval 2 p hp ![(0,a),(0,b)]
      rw [← hRight2 H hH p hp a b] at ht
      exact ht.congr (fun j => (hRight2 (Hs j) ((hHs j).mono hOB) p hp a b).symm)

end OAI.AnisotropicCalderon.Regularity

#print axioms OAI.AnisotropicCalderon.Regularity.exists_finite_harmonic_product_jet_bound
#print axioms OAI.AnisotropicCalderon.Regularity.exists_contDiffOn_of_tendsto_L2_harmonic_product_sums
