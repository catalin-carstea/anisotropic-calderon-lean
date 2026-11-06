import Calderon.ActualRadiusTwoScaledMetricCoefficientFamily
import Calderon.NativeSmoothOperatorRealization
import Calderon.CollaboratorSmoothRepOct17
import Calderon.CollaboratorAffineSobolevOct17
import Calderon.CollaboratorLocalJetsCalcOct17
import Calderon.CollaboratorRegularityLocalizationOct17
import Calderon.LocalizedDivergenceCutoff
import Calderon.SmoothHarmonicCaccioppoli
import Calderon.ActualRadiusTwoKernelOffPoleClassicalEquation
import Calderon.ActualRadiusTwoSourceKernelLocalL2Concentration
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! HELD complete all4 ordinary author candidate. Exact before-code expansion4278e14 and
supplemental API bindings8a2a367/a0963a8/e43fc43. Mechanical compilation is pending;
no prospective parent/object/config or acceptance. The final selected SAME Green
consumer requires exact genuinely released all3 concentration, never a failed receipt. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap MetricVolume
open Literature (nativeMetricDifferential)
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The forcing of the actual compact harmonic cutoff has one bound on the fixed parameter compact. -/
theorem exists_uniform_radiusTwoScaledMetric_cutoff_forcing_bound
    (hcalc : FixedSobolevCalculus) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (zeta : R3 → ℝ) (hzeta : ContDiff ℝ ∞ zeta)
    (hzetaSupport : tsupport zeta ⊆ closedBall (0 : R3) (5/8 : ℝ)) :
    let b : ((R3 × ℝ) × R3) → Matrix (Fin 3) (Fin 3) ℝ := fun v =>
      unitBallSmoothCutoff v.2 • principalCoefficient g (v.1.1+v.1.2 • v.2)
    let F : (R3 × ℝ) → SmoothCoefficientMatrix 2 := commonSupportMatrixFamily 2 b
      (radiusTwoScaledMetricCoefficient_data g hg).1 (closedBall (0 : R3) 3)
      (isCompact_closedBall _ _) (radiusTwoScaledMetricCoefficient_data g hg).2
    ∃ C : ℝ, 0 < C ∧ ∀ (t : R3 × ℝ),
      t ∈ closedBall (0 : R3) (5/4 : ℝ) ×ˢ Icc (0 : ℝ) (1/4 : ℝ) →
      ∀ U : R3 → ℝ, ContDiffOn ℝ ∞ U (ball (0 : R3) 2) →
      (∀ x ∈ (ballOpens : Set R3), divCoeffGrad
        (fun z => principalCoefficient g (t.1+t.2 • z)) U x = 0) →
      ∃ W : StrongDirichletSpace 0,
        ((TauCeti.Wkp.value 2 (W : BallSobolev 2) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens]
          fun x => zeta x * U x) ∧
        ‖strongDirichletOperator hcalc 0 (F t) W‖ ≤
          C * Real.sqrt (∫ x in (ballOpens : Set R3), U x ^ 2) := by
  dsimp only
  let b : ((R3 × ℝ) × R3) → Matrix (Fin 3) (Fin 3) ℝ := fun v =>
    unitBallSmoothCutoff v.2 • principalCoefficient g (v.1.1+v.1.2 • v.2)
  have hb : ContDiff ℝ ∞ b := (radiusTwoScaledMetricCoefficient_data g hg).1
  let F : (R3 × ℝ) → SmoothCoefficientMatrix 2 := commonSupportMatrixFamily 2 b hb
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (radiusTwoScaledMetricCoefficient_data g hg).2
  let Q : Set (R3 × ℝ) := closedBall (0 : R3) (5/4 : ℝ) ×ˢ Icc (0 : ℝ) (1/4 : ℝ)
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod isCompact_Icc
  have hbEntry (i j : Fin 3) : ContDiff ℝ ∞ (fun v => b v i j) :=
    contDiff_pi.mp (contDiff_pi.mp hb i) j
  let d : ((R3 × ℝ) × R3) → ℝ := fun v => ∑ i : Fin 3, ∑ j : Fin 3,
    ((SpatialJetFields.spatialJetField 1 (fun w => b w i j) v) (fun _ => EuclideanSpace.single i 1) *
      pd j zeta v.2 + b v i j * pd i (pd j zeta) v.2)
  have hSpatial (i j : Fin 3) : ContDiff ℝ ∞ (fun v =>
      (SpatialJetFields.spatialJetField 1 (fun w => b w i j) v)
        (fun _ => EuclideanSpace.single i 1)) := by
    simpa only [Function.comp_apply,continuousMultilinearCurryFin1_apply,Fin.snoc_zero] using
      (((continuousMultilinearCurryFin1 ℝ R3 ℝ).contDiff.comp
        (SpatialJetFields.contDiff_spatialJetField 1 _ (hbEntry i j))).clm_apply
          (contDiff_const (c := EuclideanSpace.single i (1 : ℝ))))
  have hd : ContDiff ℝ ∞ d := by
    dsimp only [d]
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact ((hSpatial i j).mul ((contDiff_pd hzeta).comp contDiff_snd)).add
        ((hbEntry i j).mul ((contDiff_pd (contDiff_pd hzeta)).comp contDiff_snd))
  have hdValue (t : R3 × ℝ) (x : R3) :
      d (t,x) = Lop (fun i j y => b (t,y) i j) zeta x := by
    let a : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => b (t,y) i j
    have ha (i j : Fin 3) : ContDiff ℝ ∞ (a i j) :=
      (hbEntry i j).comp ((contDiff_const (c := t)).prodMk contDiff_id)
    have hJet (i j : Fin 3) :
        (SpatialJetFields.spatialJetField 1 (fun w => b w i j) (t,x))
          (fun _ => EuclideanSpace.single i 1) = pd i (a i j) x := by
      rw [SpatialJetFields.spatialJetField_eq_iteratedFDeriv 1 _ (hbEntry i j)]
      simp only [iteratedFDeriv_one_apply,pd,a]
    calc
      d (t,x) = ∑ i : Fin 3, ∑ j : Fin 3,
          (pd i (a i j) x*pd j zeta x+a i j x*pd i (pd j zeta) x) := by
        dsimp only [d]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun v : ℝ => v*pd j zeta x+a i j x*pd i (pd j zeta) x) (hJet i j)
      _ = ∑ i : Fin 3, pd i (fun y => ∑ j : Fin 3, a i j y*pd j zeta y) x := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = ∑ j : Fin 3, pd i (fun y => a i j y*pd j zeta y) x := by
            apply Finset.sum_congr rfl
            intro j _
            exact (pd_mul (ha i j) (contDiff_pd hzeta) x).symm
          _ = _ := (pd_sum (fun j => (ha i j).mul (contDiff_pd hzeta)) x).symm
      _ = Lop (fun i j y => b (t,y) i j) zeta x := rfl
  obtain ⟨M0,hM0⟩ := (hQ.prod (isCompact_closedBall (0 : R3) 1)).exists_bound_of_continuousOn
    (hb.continuous.prodMk hd.continuous).continuousOn
  let M : ℝ := max 1 M0
  have hM : 1 ≤ M := le_max_left _ _
  have hCoeff (t : R3 × ℝ) (ht : t ∈ Q) (x : R3) (hx : x ∈ (ballOpens : Set R3))
      (i j : Fin 3) : |b (t,x) i j| ≤ M := by
    have hp := hM0 (t,x) ⟨ht,ball_subset_closedBall hx⟩
    exact ((norm_le_pi_norm (b (t,x) i) j).trans (norm_le_pi_norm (b (t,x)) i)).trans
      ((norm_fst_le (b (t,x),d (t,x))).trans (hp.trans (le_max_right _ _)))
  have hDiv (t : R3 × ℝ) (ht : t ∈ Q) (x : R3) (hx : x ∈ (ballOpens : Set R3)) :
      |Lop (fun i j y => b (t,y) i j) zeta x| ≤ M := by
    rw [← hdValue]
    exact (norm_snd_le (b (t,x),d (t,x))).trans
      ((hM0 (t,x) ⟨ht,ball_subset_closedBall hx⟩).trans (le_max_right _ _))
  have hzetac : HasCompactSupport zeta :=
    (isCompact_closedBall (0 : R3) (5/8 : ℝ)).of_isClosed_subset (isClosed_tsupport zeta) hzetaSupport
  obtain ⟨Mz0,hMz0,_hZetaAbs,hZetaGrad⟩ := (hzeta.of_le (by simp)).exists_abs_le_and_norm_gradient_le hzetac
  let Mz : ℝ := max 1 Mz0
  have hMz : 1 ≤ Mz := le_max_left _ _
  have hZetaGrad' (x : R3) : ‖gradient zeta x‖ ≤ Mz :=
    (hZetaGrad x).trans (le_max_right _ _)
  let eta : ContDiffBump (0 : R3) := ⟨(3/4 : ℝ),(7/8 : ℝ),by norm_num,by norm_num⟩
  have hetaSupport : tsupport (eta : R3 → ℝ) ⊆ (ballOpens : Set R3) := by
    rw [eta.tsupport_eq]
    exact closedBall_subset_ball (by norm_num)
  obtain ⟨Me,hMe,_hEtaAbs,hEtaGrad⟩ := eta.contDiff.exists_abs_le_and_norm_gradient_le eta.hasCompactSupport
  obtain ⟨alpha,Lambda,hEll⟩ := exists_uniformlyEllipticOn_radiusTwoScaledMetricCoefficient g hg
  let K : ℝ := (2*Lambda/alpha)^2
  let B : ℝ := 18*M*Mz
  let D : ℝ := 2*B^2*(K*Me^2+1)
  have hK : 0 ≤ K := sq_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D+1,by positivity,?_⟩
  intro t ht U hU heq
  have hbt : ContDiff ℝ ∞ (fun x => b (t,x)) := hb.comp (contDiff_const.prodMk contDiff_id)
  have hbtEntry (i j : Fin 3) : ContDiff ℝ ∞ (fun x => b (t,x) i j) :=
    contDiff_pi.mp (contDiff_pi.mp hbt i) j
  have hU1 : ContDiffOn ℝ ∞ U (ballOpens : Set R3) :=
    hU.mono (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2))
  have hbeq (x : R3) (hx : x ∈ (ballOpens : Set R3)) :
      divCoeffGrad (fun z => b (t,z)) U x = 0 := by
    have hNear : (fun z => b (t,z)) =ᶠ[𝓝 x]
        (fun z => principalCoefficient g (t.1+t.2 • z)) := by
      filter_upwards [unitBallSmoothCutoff_eventuallyEq_one (ball_subset_closedBall hx)] with z hz
      simp only [b,hz,one_smul]
    exact (UCP.divCoeffGrad_congr hNear (EventuallyEq.refl _ U)).trans (heq x hx)
  have hzetaBall : tsupport zeta ⊆ (ballOpens : Set R3) :=
    hzetaSupport.trans (closedBall_subset_ball (by norm_num))
  obtain ⟨hw,hProduct⟩ := Lop_cutoff_of_contDiffOn ballOpens.isOpen hbtEntry hzeta
    hzetaBall hU1 (by simpa only [Lop,pd,divCoeffGrad] using hbeq)
  let w : SmoothData := ⟨fun x => zeta x*U x,hw⟩
  let V : BallSobolev 2 := smoothBallSobolev 2 w
  have hV : TauCeti.Wkp.firstOrder 1 V ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    rw [show V = smoothBallSobolev 2 w from rfl,firstOrder_smoothBallSobolev]
    apply TauCeti.W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hzetac hzetaBall
    filter_upwards [value_smoothSobolev_ae w] with x hx hxK
    rw [hx]
    exact mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport hxK) _
  let W : StrongDirichletSpace 0 := ⟨V,hV⟩
  let L : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 := strongDirichletOperator hcalc 0 (F t)
  have hF : coefficientMatrixField 2 (F t) = fun z => b (t,z) :=
    coefficientMatrixField_commonSupportMatrixFamily 2 b hb _ _ _ t
  have hRestriction : L W = ordinaryPrincipalL hcalc 0 (F t) V := by
    have hp := congrArg (fun T : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 => T W)
      (ordinaryPrincipalL_restriction hcalc 0 (F t))
    exact hp.symm
  have hLValue : (TauCeti.Wkp.value 0 (L W) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => -Lop (fun i j y => b (t,y) i j) w.1 x := by
    rw [hRestriction]
    have hp := ordinaryPrincipalL_smoothBallSobolev_value_ae hcalc 0 (F t) w
    have hEntry (i j : Fin 3) : coefficientValue 2 (F t i j) = fun y => b (t,y) i j := by
      exact congrArg (fun A : R3 → Matrix (Fin 3) (Fin 3) ℝ => fun y => A y i j) hF
    have hLopSum (x : R3) : Lop (fun i j y => b (t,y) i j) w.1 x =
        ∑ i : Fin 3, ∑ j : Fin 3, pd i (fun y => b (t,y) i j*pd j w.1 y) x := by
      unfold Lop
      apply Finset.sum_congr rfl
      intro i _
      exact pd_sum (fun j => (hbtEntry i j).mul (contDiff_pd hw)) x
    have hp' : (TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 (F t) V) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict ballOpens]
        fun x => -∑ i : Fin 3, ∑ j : Fin 3, pd i (fun y => b (t,y) i j*pd j w.1 y) x := by
      simpa only [V,hEntry,pd,coordinateVector] using hp
    filter_upwards [hp'] with x hx
    rw [hx,← hLopSum x]
  have hAbs (x : R3) (hx : x ∈ (ballOpens : Set R3)) :
      |-Lop (fun i j y => b (t,y) i j) w.1 x| ≤
        B*(|eta x| *‖gradient U x‖+|U x|) := by
    by_cases hxK : x ∈ tsupport zeta
    · have hEta : eta x = 1 := eta.one_of_mem_closedBall
        ((hzetaSupport hxK).trans (by norm_num : (5/8 : ℝ) ≤ 3/4))
      have hpU (j : Fin 3) : |pd j U x| ≤ ‖gradient U x‖ := by
        rw [show pd j U x = (gradient U x) j from (gradient_coordinate U x j).symm]
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (gradient U x) j
      have hpZ (i : Fin 3) : |pd i zeta x| ≤ Mz := by
        rw [show pd i zeta x = (gradient zeta x) i from (gradient_coordinate zeta x i).symm]
        exact (PiLp.norm_apply_le (gradient zeta x) i).trans (hZetaGrad' x)
      have hCross : |∑ i : Fin 3, ∑ j : Fin 3,
          (b (t,x) i j+b (t,x) j i)*pd i zeta x*pd j U x| ≤ B*‖gradient U x‖ := by
        calc
          _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |(b (t,x) i j+b (t,x) j i)*pd i zeta x*pd j U x| :=
            (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
          _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, (2*M)*Mz*‖gradient U x‖ := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            rw [abs_mul,abs_mul]
            have ha := (abs_add_le (b (t,x) i j) (b (t,x) j i)).trans
              (add_le_add (hCoeff t ht x hx i j) (hCoeff t ht x hx j i))
            have ha' : |b (t,x) i j+b (t,x) j i| ≤ 2*M := by linarith only [ha]
            exact mul_le_mul (mul_le_mul ha' (hpZ i) (abs_nonneg _) (by positivity))
              (hpU j) (abs_nonneg _) (by positivity)
          _ = B*‖gradient U x‖ := by dsimp only [B]; simp only [Fin.sum_univ_three]; ring
      rw [abs_neg,show w.1 = (fun y => zeta y*U y) from rfl,hProduct x]
      have hZero : |U x*Lop (fun i j y => b (t,y) i j) zeta x| ≤ |U x| *M := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hDiv t ht x hx) (abs_nonneg _)
      have hMB : M ≤ B := by dsimp only [B]; nlinarith only [hM,hMz]
      rw [hEta,abs_one,one_mul]
      exact (abs_add_le _ _).trans ((add_le_add hZero hCross).trans (by
        nlinarith only [mul_le_mul_of_nonneg_right hMB (abs_nonneg (U x))]))
    · have hz : (fun y => zeta y*U y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hxK)] with y hy
        rw [hy,Pi.zero_apply,zero_mul]
      have hzero : Lop (fun i j y => b (t,y) i j) w.1 x = 0 :=
        UCP.divCoeffGrad_eq_zero_of_eventuallyEq_zero _ hz
      rw [hzero,neg_zero,abs_zero]
      positivity
  refine ⟨W,value_smoothBallSobolev_ae 2 w,?_⟩
  have hUClosed : ContinuousOn U (closedBall (0 : R3) 1) := hU.continuousOn.mono
    (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))
  have hIntU : IntegrableOn (fun x => U x^2) (ballOpens : Set R3) (volume : Measure R3) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : R3) 1)
      (hUClosed.pow 2)).mono_set ball_subset_closedBall
  have hGradClosed : ContinuousOn (gradient U) (closedBall (0 : R3) 1) := by
    intro x hx
    have hAt := hU.contDiffAt (isOpen_ball.mem_nhds
      ((closedBall_subset_ball (by norm_num : (1 : ℝ) < 2)) hx))
    have hdU := (hAt.fderiv_right (m := 1) (by simp)).continuousAt
    exact ((InnerProductSpace.toDual ℝ R3).symm.continuousAt.comp hdU).continuousWithinAt
  have hIntGrad : IntegrableOn (fun x => eta x^2*‖gradient U x‖^2)
      (ballOpens : Set R3) (volume : Measure R3) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : R3) 1)
      ((eta.continuous.continuousOn.pow 2).mul (hGradClosed.norm.pow 2))).mono_set ball_subset_closedBall
  have hc := setIntegral_sq_mul_norm_gradient_sq_le_of_harmonic hbt
    (hEll t.1 ht.1 t.2 ht.2.1 ht.2.2) (by norm_num : (1 : ℝ) < 2)
    hU hbeq eta.contDiff eta.hasCompactSupport hetaSupport
  have hEtaInt : (∫ x in (ballOpens : Set R3), ‖gradient eta x‖^2*U x^2) ≤
      Me^2*(∫ x in (ballOpens : Set R3), U x^2) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) (hIntU.const_mul _)
    exact Eventually.of_forall fun x => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hEtaGrad x) 2) (sq_nonneg _)
  have hGradBound : (∫ x in (ballOpens : Set R3), eta x^2*‖gradient U x‖^2) ≤
      K*Me^2*(∫ x in (ballOpens : Set R3), U x^2) := by
    exact hc.trans ((mul_le_mul_of_nonneg_left hEtaInt hK).trans_eq (by ring))
  have hSq : (fun x => (TauCeti.Wkp.value 0 (L W) x)^2) ≤ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => 2*B^2*(eta x^2*‖gradient U x‖^2+U x^2) := by
    filter_upwards [hLValue,ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx hxB
    rw [hx]
    have hp := hAbs x hxB
    have hPos : 0 ≤ B*(|eta x| *‖gradient U x‖+|U x|) := by positivity
    have hpSq := pow_le_pow_left₀ (abs_nonneg _) hp 2
    have hYoungPlain (a b : ℝ) : (a+b)^2 ≤ 2*(a^2+b^2) := by
      nlinarith only [sq_nonneg (a-b)]
    have hYoung := hYoungPlain (|eta x| *‖gradient U x‖) |U x|
    simp only [mul_pow,sq_abs] at hYoung
    have hScaledYoung := mul_le_mul_of_nonneg_left hYoung (sq_nonneg B)
    calc
      (-Lop (fun i j y => b (t,y) i j) w.1 x)^2 =
          |-Lop (fun i j y => b (t,y) i j) w.1 x|^2 := (sq_abs _).symm
      _ ≤ (B*(|eta x| *‖gradient U x‖+|U x|))^2 := hpSq
      _ = B^2*(|eta x| *‖gradient U x‖+|U x|)^2 := mul_pow _ _ 2
      _ ≤ B^2*(2*(eta x^2*‖gradient U x‖^2+U x^2)) := hScaledYoung
      _ = 2*B^2*(eta x^2*‖gradient U x‖^2+U x^2) := by ring
  have hNormSq : ‖L W‖^2 = ∫ x in (ballOpens : Set R3), (TauCeti.Wkp.value 0 (L W) x)^2 := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs,TauCeti.Wkp.value_zero]
  have hForceSq : ‖L W‖^2 ≤ D*(∫ x in (ballOpens : Set R3), U x^2) := by
    rw [hNormSq]
    calc
      _ ≤ ∫ x in (ballOpens : Set R3), 2*B^2*(eta x^2*‖gradient U x‖^2+U x^2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
          ((hIntGrad.add hIntU).const_mul _) hSq
      _ = 2*B^2*((∫ x in (ballOpens : Set R3), eta x^2*‖gradient U x‖^2)+
          ∫ x in (ballOpens : Set R3), U x^2) := by rw [integral_const_mul,integral_add hIntGrad hIntU]
      _ ≤ 2*B^2*(K*Me^2*(∫ x in (ballOpens : Set R3), U x^2)+
          ∫ x in (ballOpens : Set R3), U x^2) := by gcongr
      _ = D*(∫ x in (ballOpens : Set R3), U x^2) := by dsimp only [D]; ring
  have hI : 0 ≤ ∫ x in (ballOpens : Set R3), U x^2 := integral_nonneg fun _ => sq_nonneg _
  have hDD : D ≤ (D+1)^2 := by nlinarith only [hD,sq_nonneg D]
  have hForce : ‖L W‖ ≤ (D+1)*Real.sqrt (∫ x in (ballOpens : Set R3), U x^2) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hI]
    exact hForceSq.trans (mul_le_mul_of_nonneg_right hDD hI)
  exact hForce

/-- SAME native strong inverse and fixed H2 evaluation yield a uniform sampled harmonic point bound. -/
theorem exists_uniform_radiusTwoScaledMetric_harmonic_point_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : R3 × ℝ),
      t ∈ closedBall (0 : R3) (5/4 : ℝ) ×ˢ Icc (0 : ℝ) (1/4 : ℝ) →
      ∀ U : R3 → ℝ, ContDiffOn ℝ ∞ U (ball (0 : R3) 2) →
      (∀ x ∈ (ballOpens : Set R3), divCoeffGrad
        (fun z => principalCoefficient g (t.1+t.2 • z)) U x = 0) →
      |U 0| ≤ C*Real.sqrt (∫ x in (ballOpens : Set R3), U x^2) := by
  let zeta : ContDiffBump (0 : R3) := ⟨(1/2 : ℝ),(5/8 : ℝ),by norm_num,by norm_num⟩
  have hzetaSupport : tsupport (zeta : R3 → ℝ) ⊆ closedBall (0 : R3) (5/8 : ℝ) := by
    rw [zeta.tsupport_eq]
  obtain ⟨Cf,hCf,hForce⟩ := exists_uniform_radiusTwoScaledMetric_cutoff_forcing_bound
    hcalc g hg zeta zeta.contDiff hzetaSupport
  obtain ⟨Ci,hCi,hInverse⟩ := exists_uniform_radiusTwoScaledMetricInverse_apply_bound hcalc hreg g hg 0
  obtain ⟨alpha,Lambda,hEll⟩ := exists_uniformlyEllipticOn_radiusTwoScaledMetricCoefficient g hg
  obtain ⟨Ce,hEval⟩ := Regularity.SmoothRepAux.deriv_bound 0 (1/4 : ℝ) (by norm_num)
  let C : ℝ := 1+max Ce 0*Ci*Cf
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro t ht U hU heq
  let b : ((R3 × ℝ) × R3) → Matrix (Fin 3) (Fin 3) ℝ := fun v =>
    unitBallSmoothCutoff v.2 • principalCoefficient g (v.1.1+v.1.2 • v.2)
  let F : SmoothCoefficientMatrix 2 := commonSupportMatrixFamily 2 b
    (radiusTwoScaledMetricCoefficient_data g hg).1 (closedBall (0 : R3) 3)
    (isCompact_closedBall _ _) (radiusTwoScaledMetricCoefficient_data g hg).2 t
  let L : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 := strongDirichletOperator hcalc 0 F
  obtain ⟨W,hValue,hNorm⟩ := hForce t ht U hU heq
  have hField : coefficientMatrixField 2 F = fun z => b (t,z) :=
    coefficientMatrixField_commonSupportMatrixFamily 2 b _ _ _ _ t
  have hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField 2 F) alpha Lambda := by
    rw [hField]
    exact hEll t.1 ht.1 t.2 ht.2.1 ht.2.2
  have hInv : L.IsInvertible := strongDirichletOperator_isInvertible_of_elliptic hcalc hreg 0 F hUE
  have hBack : L.inverse (L W) = W := hInv.inverse_apply_eq.mpr rfl
  have hWNorm : ‖W‖ ≤ Ci*Cf*Real.sqrt (∫ x in (ballOpens : Set R3), U x^2) := by
    calc
      ‖W‖ = ‖L.inverse (L W)‖ := congrArg norm hBack.symm
      _ ≤ Ci*‖L W‖ := hInverse t ht (L W)
      _ ≤ Ci*(Cf*Real.sqrt (∫ x in (ballOpens : Set R3), U x^2)) :=
        mul_le_mul_of_nonneg_left hNorm hCi
      _ = _ := by ring
  let w : R3 → ℝ := fun x => zeta x*U x
  have hw : ContDiff ℝ ∞ w := UCP.contDiff_of_tsupport_subset isOpen_ball
    (zeta.contDiff.contDiffOn.mul hU)
    (tsupport_mul_subset_left.trans (hzetaSupport.trans (closedBall_subset_ball (by norm_num))))
  have hPoint : |U 0| ≤ Ce*‖W‖ := by
    have hp := hEval 2 (by norm_num : 0+2 ≤ 2) ballOpens (W : BallSobolev 2) w hw hValue
      0 (ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1))
    have hz : zeta (0 : R3) = 1 := zeta.one_of_mem_closedBall (by
      change dist (0 : R3) 0 ≤ zeta.rIn
      rw [dist_self]
      exact zeta.rIn_pos.le)
    simpa only [norm_iteratedFDeriv_zero,w,hz,one_mul,Real.norm_eq_abs,ClosedSubmodule.norm_coe] using hp
  calc
    |U 0| ≤ Ce*‖W‖ := hPoint
    _ ≤ max Ce 0*‖W‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max Ce 0*(Ci*Cf*Real.sqrt (∫ x in (ballOpens : Set R3), U x^2)) :=
      mul_le_mul_of_nonneg_left hWNorm (le_max_right _ _)
    _ ≤ C*Real.sqrt (∫ x in (ballOpens : Set R3), U x^2) := by
      dsimp only [C]
      nlinarith only [Real.sqrt_nonneg (∫ x in (ballOpens : Set R3), U x^2)]

/-- The exact affine Jacobian produces the original physical radius exponent. -/
theorem exists_uniform_radiusTwo_rescaled_nativeHarmonic_point_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : R3), q ∈ closedBall (0 : R3) (5/4 : ℝ) →
      ∀ (r : ℝ), 0 < r → r ≤ (1/4 : ℝ) →
      ∀ H : R3 → ℝ, ContDiffOn ℝ ∞ H (ball q r) →
      MemLp H 2 ((volume : Measure R3).restrict (ball q r)) →
      (∀ x ∈ ball q r, nativeMetricDifferential g H x = 0) →
      |H q| ≤ C*r^(-(3 : ℝ)/2)*Real.sqrt (∫ x in ball q r, H x^2) := by
  obtain ⟨Cu,hCu,hUnit⟩ := exists_uniform_radiusTwoScaledMetric_harmonic_point_bound hreg hcalc g hg
  refine ⟨Real.sqrt 8*Cu,by positivity,?_⟩
  intro q hq r hr hrMax H hH hMem hPDE
  let rho : ℝ := r/2
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hrhoLe : rho ≤ r := by dsimp only [rho]; linarith only [hr]
  let U : R3 → ℝ := fun z => H (q+rho • z)
  have hMaps (z : R3) (hz : z ∈ ball (0 : R3) 2) : q+rho • z ∈ ball q r := by
    change dist (q+rho • z) q < r
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hrho]
    have hn := mem_ball_zero_iff.mp hz
    dsimp only [rho]
    nlinarith only [hn,hr]
  have hAffineCDF : ContDiff ℝ ∞ (fun z : R3 => q+rho • z) :=
    (contDiff_const (c := q)).add (contDiff_const_smul rho)
  have hU : ContDiffOn ℝ ∞ U (ball (0 : R3) 2) :=
    hH.comp hAffineCDF.contDiffOn hMaps
  have hEq (x : R3) (hx : x ∈ (ballOpens : Set R3)) :
      divCoeffGrad (fun z => principalCoefficient g (q+rho • z)) U x = 0 := by
    have hx2 : x ∈ ball (0 : R3) 2 := (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hx
    have hOld := hPDE (q+rho • x) (hMaps x hx2)
    change -divCoeffGrad (principalCoefficient g) H (q+rho • x) = 0 at hOld
    rw [show U = (fun z => H (q+rho • z)) from rfl,
      Regularity.Jets.divCoeffGrad_comp_affine _ _ q hrho.ne',neg_eq_zero.mp hOld,mul_zero]
  have ht : (q,rho) ∈ closedBall (0 : R3) (5/4 : ℝ) ×ˢ Icc (0 : ℝ) (1/4 : ℝ) :=
    ⟨hq,hrho.le,by dsimp only [rho]; linarith only [hrMax,hr]⟩
  have hPoint := hUnit (q,rho) ht U hU hEq
  have hAff : Affine.IsAff (Affine.ballO q rho) ballOpens q rho := by
    intro z
    change dist (q+rho • z) q < rho ↔ dist z 0 < 1
    simp only [dist_eq_norm,add_sub_cancel_left,sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos hrho]
    constructor <;> intro h <;> nlinarith only [h,hrho]
  have hChange : rho^3*(∫ x in (ballOpens : Set R3), U x^2) =
      ∫ x in ball q rho, H x^2 := by
    have hc := (Affine.mp_restrict hrho hAff).integral_comp
      (Affine.measurableEmbedding_aff q hrho) (fun x => H x^2)
    rw [integral_smul_measure] at hc
    simpa only [U,Affine.aff,Affine.ballO,Opens.coe_mk,Affine.sc,
      ENNReal.toReal_ofReal (pow_nonneg hrho.le 3),smul_eq_mul] using hc
  have hILe : (∫ x in ball q rho, H x^2) ≤ ∫ x in ball q r, H x^2 :=
    setIntegral_mono_set hMem.integrable_sq (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun _ hx => (ball_subset_ball hrhoLe) hx)
  have hFactor : rho^3*(8*(r^3)⁻¹) = 1 := by
    dsimp only [rho]
    field_simp [hr.ne']
    <;> ring
  have hScaled : (∫ x in (ballOpens : Set R3), U x^2) ≤
      (8*(r^3)⁻¹)*(∫ x in ball q r, H x^2) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hrho 3)).mp
    calc
      _ = ∫ x in ball q rho, H x^2 := hChange
      _ ≤ ∫ x in ball q r, H x^2 := hILe
      _ = rho^3*((8*(r^3)⁻¹)*(∫ x in ball q r, H x^2)) := by
        rw [← mul_assoc,hFactor,one_mul]
  have hPower : (r^(-(3 : ℝ)/2))^2 = (r^3)⁻¹ := by
    calc
      (r^(-(3 : ℝ)/2))^2 = r^(-(3 : ℝ)) := by
        rw [← Real.rpow_natCast _ 2,← Real.rpow_mul hr.le]
        congr 1
        norm_num
      _ = (r^(3 : ℝ))⁻¹ := Real.rpow_neg hr.le 3
      _ = (r^3)⁻¹ := congrArg Inv.inv (Real.rpow_natCast r 3)
  have hI : 0 ≤ ∫ x in ball q r, H x^2 := integral_nonneg fun _ => sq_nonneg _
  have hSqrt : Real.sqrt (∫ x in (ballOpens : Set R3), U x^2) ≤
      Real.sqrt 8*r^(-(3 : ℝ)/2)*Real.sqrt (∫ x in ball q r, H x^2) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _),mul_pow,mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8),hPower,Real.sq_sqrt hI]
    exact hScaled
  have hZero : U (0 : R3) = H q := by simp only [U,smul_zero,add_zero]
  rw [hZero] at hPoint
  exact hPoint.trans ((mul_le_mul_of_nonneg_left hSqrt hCu.le).trans_eq (by ring))

/-- Critical concentration and the SAME actual harmonic point bound give the original inverse-distance cap. -/
theorem exists_uniform_radiusTwoSourceKernel_inverse_distance_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p q : ↥(radiusTwoOpens : Set R3)),
      ‖(p : R3)‖ ≤ (5/4 : ℝ) → ‖(q : R3)‖ ≤ (5/4 : ℝ) → p ≠ q →
      |G p q| ≤ C/dist (p : R3) (q : R3) := by
  obtain ⟨Cp,hCp,hPoint⟩ := exists_uniform_radiusTwo_rescaled_nativeHarmonic_point_bound hreg hcalc g hg
  obtain ⟨Cc,hCc,hConcentration⟩ := exists_uniform_radiusTwoSourceKernel_row_localL2_concentration
    hreg hcalc g hg K G hData
  let V3 : ℝ := (volume : Measure R3).real (ball (0 : R3) 1)
  let A : ℝ := Cc*V3^((1 : ℝ)/3)
  have hV3 : 0 ≤ V3 := ENNReal.toReal_nonneg
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let C : ℝ := 10*Cp*Real.sqrt A+1
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro p q hp hq hne
  let d : ℝ := dist (p : R3) (q : R3)
  have hd : 0 < d := dist_pos.mpr (fun h => hne (Subtype.ext h))
  let r : ℝ := min (d/2) (1/4 : ℝ)
  have hr : 0 < r := lt_min (by linarith only [hd]) (by norm_num)
  have hrMax : r ≤ (1/4 : ℝ) := min_le_right _ _
  have hrDist : r ≤ d/2 := min_le_left _ _
  have hRoom : ball (q : R3) r ⊆ (radiusTwoOpens : Set R3) \ {(p : R3)} := by
    intro x hx
    have hxDist : dist x (q : R3) < r := mem_ball.mp hx
    constructor
    · apply mem_ball_zero_iff.mpr
      have hn : ‖x‖ ≤ dist x (q : R3)+‖(q : R3)‖ := by
        calc ‖x‖ = ‖(x-(q : R3))+(q : R3)‖ := by rw [sub_add_cancel]
          _ ≤ ‖x-(q : R3)‖+‖(q : R3)‖ := norm_add_le _ _
          _ = dist x (q : R3)+‖(q : R3)‖ := by rw [dist_eq_norm]
      linarith only [hn,hxDist,hrMax,hq]
    · intro hxP
      have hxEq : x = (p : R3) := mem_singleton_iff.mp hxP
      rw [hxEq] at hxDist
      change d < r at hxDist
      linarith only [hxDist,hrDist,hd]
  have hBallU : ball (q : R3) r ⊆ (radiusTwoOpens : Set R3) := fun _ hx => (hRoom hx).1
  obtain ⟨hSmooth,hPDE⟩ := radiusTwoSourceKernel_row_contDiffOn_and_nativeMetricDifferential_eq_zero
    hreg hcalc g hg K G hData p
  have hRep : (G p) =ᵐ[(volume : Measure R3).restrict (ball (q : R3) r)] (K p : R3 → ℝ) :=
    (hData.1 p).2.2.1.filter_mono (ae_mono (Measure.restrict_mono_set (volume : Measure R3) hBallU))
  have hMem : MemLp (G p) 2 ((volume : Measure R3).restrict (ball (q : R3) r)) :=
    (memLp_congr_ae hRep).mpr
      ((Lp.memLp (K p)).mono_measure (Measure.restrict_mono_set (volume : Measure R3) hBallU))
  have hPhysical := hPoint (q : R3) (mem_closedBall_zero_iff.mpr hq) r hr hrMax
    (G p) (hSmooth.mono hRoom) hMem (fun _ hx => hPDE _ (hRoom hx))
  have hVolume : (volume : Measure R3).real (ball (q : R3) r) = r^3*V3 := by
    rw [measureReal_def,Measure.addHaar_ball (volume : Measure R3) (q : R3) hr.le,
      ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
    simp only [R3,finrank_euclideanSpace,Fintype.card_fin,V3,measureReal_def]
  have hVolumeRoot : ((volume : Measure R3).real (ball (q : R3) r))^((1 : ℝ)/3) =
      V3^((1 : ℝ)/3)*r := by
    rw [hVolume,Real.mul_rpow (pow_nonneg hr.le 3) hV3]
    have hPower : (r^3)^((1 : ℝ)/3) = r := by
      rw [← Real.rpow_natCast r 3,← Real.rpow_mul hr.le]
      norm_num
    rw [hPower]
    ring
  have hI : 0 ≤ ∫ x in ball (q : R3) r, (G p x)^2 := integral_nonneg fun _ => sq_nonneg _
  have hIUpper : (∫ x in ball (q : R3) r, (G p x)^2) ≤ A*r := by
    have h := hConcentration p hp (ball (q : R3) r) measurableSet_ball hBallU
    rw [hVolumeRoot] at h
    exact h.trans_eq (by dsimp only [A]; ring)
  have hSqrt : Real.sqrt (∫ x in ball (q : R3) r, (G p x)^2) ≤ Real.sqrt A*Real.sqrt r := by
    exact (Real.sqrt_le_sqrt hIUpper).trans_eq (Real.sqrt_mul hA _)
  have hPower : r^(-(3 : ℝ)/2)*Real.sqrt r = r⁻¹ := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_add hr]
    norm_num [Real.rpow_neg_one]
  have hCap : |G p q| ≤ Cp*Real.sqrt A/r := by
    calc
      _ ≤ Cp*r^(-(3 : ℝ)/2)*Real.sqrt (∫ x in ball (q : R3) r, (G p x)^2) := hPhysical
      _ ≤ Cp*r^(-(3 : ℝ)/2)*(Real.sqrt A*Real.sqrt r) := by gcongr
      _ = Cp*Real.sqrt A*(r^(-(3 : ℝ)/2)*Real.sqrt r) := by ring
      _ = Cp*Real.sqrt A*r⁻¹ := by rw [hPower]
      _ = Cp*Real.sqrt A/r := (div_eq_mul_inv _ _).symm
  have hdMax : d ≤ (5/2 : ℝ) := by
    have h := dist_le_norm_add_norm (p : R3) (q : R3)
    dsimp only [d]
    linarith only [h,hp,hq]
  have hrLower : d/10 ≤ r := by
    apply le_min
    · linarith only [hd]
    · linarith only [hdMax]
  have hRatio : Cp*Real.sqrt A/r ≤ (10*Cp*Real.sqrt A)/d := by
    apply (div_le_div_iff₀ hr hd).mpr
    have h := mul_le_mul_of_nonneg_left (show d ≤ 10*r by linarith only [hrLower])
      (show 0 ≤ Cp*Real.sqrt A by positivity)
    nlinarith only [h]
  exact hCap.trans (hRatio.trans (by
    apply (div_le_div_iff_of_pos_right hd).mpr
    dsimp only [C]
    linarith))

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniform_radiusTwoScaledMetric_cutoff_forcing_bound
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniform_radiusTwoScaledMetric_harmonic_point_bound
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniform_radiusTwo_rescaled_nativeHarmonic_point_bound
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniform_radiusTwoSourceKernel_inverse_distance_bound
