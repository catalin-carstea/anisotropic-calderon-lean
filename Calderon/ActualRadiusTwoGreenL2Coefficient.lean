import Calderon.ActualRadiusTwoUniformHigherGreenJets
import Calderon.ActualRadiusTwoKernelOffPoleClassicalEquation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter TopologicalSpace
open scoped ContDiff Topology ENNReal Distributions BigOperators Classical
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

theorem contDiffOn_integral_and_fderiv_of_dominated_iteratedFDeriv
    (μ : Measure R3) (D : Set R3) (hD : IsOpen D)
    (H : R3 → R3 → ℝ) (z : R3 → ℝ)
    (hRow : ∀ᵐ x ∂μ, ContDiffOn ℝ ∞ (H x) D)
    (hInt : ∀ (n : ℕ) (y : R3), y ∈ D →
      Integrable (fun x => z x • iteratedFDeriv ℝ n (H x) y) μ)
    (b : ℕ → R3 → ℝ) (hbInt : ∀ n, Integrable (b n) μ)
    (hBound : ∀ n, ∀ᵐ x ∂μ, ∀ y ∈ D,
      ‖z x • iteratedFDeriv ℝ n (H x) y‖ ≤ b n x) :
    let T : R3 → ℝ := fun y => ∫ x, H x y * z x ∂μ
    ContDiffOn ℝ ∞ T D ∧
      (∀ y ∈ D, ∀ v : R3,
        fderiv ℝ T y v = ∫ x, z x * fderiv ℝ (H x) y v ∂μ) ∧
      (∀ y ∈ D, ∀ v w : R3,
        fderiv ℝ (fderiv ℝ T) y v w =
          ∫ x, z x * fderiv ℝ (fderiv ℝ (H x)) y v w ∂μ)
 := by
  classical
  intro T
  let E : ℕ → Type := fun n => R3 [×n]→L[ℝ] ℝ
  let F : (n : ℕ) → R3 → R3 → E n :=
    fun n x y => iteratedFDeriv ℝ n (H x) y
  let I : (n : ℕ) → R3 → E n := fun n y => ∫ x, z x • F n x y ∂μ
  have hNativeLinear (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace X] [CompleteSpace Y]
      (f : X → Y) (ha : ∀ x y, f (x+y) = f x+f y)
      (hs : ∀ (c : ℝ) x, f (c • x) = c • f x)
      (hb : ∀ x, ‖f x‖ ≤ ‖x‖) :
      ∃ L : X →L[ℝ] Y, (∀ x, L x = f x) ∧ ‖L‖ ≤ 1 ∧
        (∀ φ : R3 → X, Integrable φ μ → Integrable (fun x => L (φ x)) μ) ∧
        (∀ φ : R3 → X, Integrable φ μ →
          (∫ x, L (φ x) ∂μ) = L (∫ x, φ x ∂μ)) := by
    let F : X →ₗ[ℝ] Y :=
      { toFun := f
        map_add' := ha
        map_smul' := fun c x => by simpa only [RingHom.id_apply] using hs c x }
    have hF : ∀ x, ‖F x‖ ≤ 1*‖x‖ := by
      intro x
      change ‖f x‖ ≤ 1*‖x‖
      simpa only [one_mul] using hb x
    let L : X →L[ℝ] Y := F.mkContinuous 1 hF
    refine ⟨L, (fun _ => rfl), LinearMap.mkContinuous_norm_le F (by norm_num) hF, ?_, ?_⟩
    · intro φ hφ
      exact L.integrable_comp hφ
    · intro φ hφ
      exact L.integral_comp_comm hφ
  let Cdata (n : ℕ) := hNativeLinear (E (n+1)) (R3 →L[ℝ] E n)
    (fun L => L.curryLeft)
    (by intro L M; ext v w; rfl)
    (by intro c L; ext v w; rfl)
    (fun L => (ContinuousMultilinearMap.curryLeft_norm L).le)
  let Curry (n : ℕ) := Classical.choose (Cdata n)
  have hCurryFun (n : ℕ) (L : E (n+1)) : Curry n L = L.curryLeft :=
    (Classical.choose_spec (Cdata n)).1 L
  have hCurryInt (n : ℕ) (y : R3) (hy : y ∈ D) :=
    (Classical.choose_spec (Cdata n)).2.2.1 (fun x => z x • F (n+1) x y)
      (hInt (n+1) y hy)
  have hICurry (n : ℕ) (y : R3) (hy : y ∈ D) :
      (∫ x, Curry n (z x • F (n+1) x y) ∂μ) = (I (n+1) y).curryLeft := by
    calc
      _ = Curry n (∫ x, z x • F (n+1) x y ∂μ) :=
        (Classical.choose_spec (Cdata n)).2.2.2 (fun x => z x • F (n+1) x y)
          (hInt (n+1) y hy)
      _ = (I (n+1) y).curryLeft := hCurryFun n (I (n+1) y)
  have hIDeriv (n : ℕ) (y : R3) (hy : y ∈ D) :
      HasFDerivAt (I n) (I (n+1) y).curryLeft y := by
    have hm : ∀ᶠ q in 𝓝 y, AEStronglyMeasurable (fun x => z x • F n x q) μ := by
      filter_upwards [hD.mem_nhds hy] with q hq
      exact (hInt n q hq).aestronglyMeasurable
    have hm' := (hCurryInt n y hy).aestronglyMeasurable
    have hb : ∀ᵐ x ∂μ, ∀ q ∈ D,
        ‖Curry n (z x • F (n+1) x q)‖ ≤ b (n+1) x := by
      filter_upwards [hBound (n+1)] with x hx q hq
      rw [hCurryFun,ContinuousMultilinearMap.curryLeft_norm]
      exact hx q hq
    have hf : ∀ᵐ x ∂μ, ∀ q ∈ D,
        HasFDerivAt (fun q => z x • F n x q) (Curry n (z x • F (n+1) x q)) q := by
      filter_upwards [hRow] with x hx q hq
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n (H x)) q :=
        (hx.contDiffAt (hD.mem_nhds hq)).differentiableAt_iteratedFDeriv
          (by exact_mod_cast (WithTop.coe_lt_top n))
      have hWeighted := hdiff.hasFDerivAt.const_smul (z x)
      apply hWeighted.congr_fderiv
      simp only [hCurryFun,F,fderiv_iteratedFDeriv,Function.comp_def,
        continuousMultilinearCurryLeftEquiv_apply]
      ext v w
      rfl
    have hi := hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun q x => z x • F n x q)
      (F' := fun q x => Curry n (z x • F (n+1) x q))
      (bound := b (n+1)) (hD.mem_nhds hy) hm (hInt n y hy) hm'
      hb (hbInt (n+1)) hf
    rw [hICurry n y hy] at hi
    exact hi
  have hICont (n : ℕ) : ContinuousOn (I n) D := by
    intro y hy
    exact (hIDeriv n y hy).continuousAt.continuousWithinAt
  have hISmooth : ∀ (k n : ℕ), ContDiffOn ℝ k (I n) D := by
    intro k
    induction k with
    | zero => intro n; exact contDiffOn_zero.mpr (hICont n)
    | succ k ih =>
      intro n
      rw [Nat.cast_add,Nat.cast_one,
        contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hD.uniqueDiffOn]
      refine ⟨by simp,fun y => (I (n+1) y).curryLeft,?_,?_⟩
      · have hc : ContDiffOn ℝ k (fun y => Curry n (I (n+1) y)) D :=
          (Curry n).contDiff.comp_contDiffOn (ih (n+1))
        exact hc.congr (fun y _ => (hCurryFun n (I (n+1) y)).symm)
      · intro y hy
        exact (hIDeriv n y hy).hasFDerivWithinAt
  have hIInfinity (n : ℕ) : ContDiffOn ℝ ∞ (I n) D :=
    contDiffOn_infty.mpr (fun k => hISmooth k n)
  let L0 : E 0 →L[ℝ] ℝ :=
    (continuousMultilinearCurryFin0 ℝ R3 ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let L1 : E 1 →L[ℝ] (R3 →L[ℝ] ℝ) :=
    (continuousMultilinearCurryFin1 ℝ R3 ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hTValue (y : R3) (hy : y ∈ D) : T y = L0 (I 0 y) := by
    change (∫ x, H x y*z x ∂μ) = (∫ x, z x • F 0 x y ∂μ) 0
    rw [ContinuousMultilinearMap.integral_apply (hInt 0 y hy)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by simp only [F,ContinuousMultilinearMap.smul_apply,
      iteratedFDeriv_zero_apply,smul_eq_mul,mul_comm])
  have hTDeriv (y : R3) (hy : y ∈ D) : HasFDerivAt T (L1 (I 1 y)) y := by
    have hi := L0.hasFDerivAt.comp y (hIDeriv 0 y hy)
    have hlin : L0.comp (I 1 y).curryLeft = L1 (I 1 y) := by
      ext v
      change (I 1 y) (Fin.cons v (0 : Fin 0 → R3)) =
        (I 1 y) (Fin.snoc (0 : Fin 0 → R3) v)
      congr 1
      funext i
      fin_cases i
      rfl
    rw [hlin] at hi
    apply hi.congr_of_eventuallyEq
    filter_upwards [hD.mem_nhds hy] with q hq using hTValue q hq
  have hTSecond (y : R3) (hy : y ∈ D) :
      HasFDerivAt (fderiv ℝ T) (L1.comp (I 2 y).curryLeft) y := by
    have hi := L1.hasFDerivAt.comp y (hIDeriv 1 y hy)
    apply hi.congr_of_eventuallyEq
    filter_upwards [hD.mem_nhds hy] with q hq using (hTDeriv q hq).fderiv
  have hFirst (y : R3) (hy : y ∈ D) (v : R3) :
      fderiv ℝ T y v = ∫ x, z x*fderiv ℝ (H x) y v ∂μ := by
    rw [(hTDeriv y hy).fderiv]
    change (∫ x, z x • F 1 x y ∂μ) (Fin.snoc (0 : Fin 0 → R3) v) = _
    rw [ContinuousMultilinearMap.integral_apply (hInt 1 y hy)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by simp only [F,ContinuousMultilinearMap.smul_apply,
      smul_eq_mul,iteratedFDeriv_one_apply,Fin.snoc_zero])
  have hSecond (y : R3) (hy : y ∈ D) (v w : R3) :
      fderiv ℝ (fderiv ℝ T) y v w =
        ∫ x, z x*fderiv ℝ (fderiv ℝ (H x)) y v w ∂μ := by
    rw [(hTSecond y hy).fderiv]
    change (∫ x, z x • F 2 x y ∂μ)
      (Fin.cons v (Fin.snoc (0 : Fin 0 → R3) w)) = _
    rw [ContinuousMultilinearMap.integral_apply (hInt 2 y hy)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by simp only [F,ContinuousMultilinearMap.smul_apply,
      smul_eq_mul,iteratedFDeriv_two_apply,Fin.cons_zero,Fin.cons_succ,Fin.cons_one,Fin.snoc_last,
      Fin.snoc_zero])
  have hTInfinity : ContDiffOn ℝ ∞ T D :=
    (L0.contDiff.comp_contDiffOn (hIInfinity 0)).congr hTValue
  exact ⟨hTInfinity, hFirst, hSecond⟩

theorem contDiffOn_integral_radiusTwoSourceKernel_mul_L2_and_nativeMetricDifferential_eq_zero
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (S : Set R3) (hS : MeasurableSet S)
    (hSroom : closure S ⊆ closedBall (0 : R3) (5/4 : ℝ))
    (D : Set R3) (hD : IsOpen D)
    (hDroom : D ⊆ closedBall (0 : R3) (5/4 : ℝ))
    (d : ℝ) (hd : 0 < d)
    (hSep : ∀ x ∈ closure S, ∀ y ∈ D, d ≤ dist x y)
    (z : Lp ℝ 2 ((volume : Measure R3).restrict S)) :
    let H : R3 → R3 → ℝ := fun x y =>
      if hx : x ∈ (radiusTwoOpens : Set R3) then G ⟨x,hx⟩ y else 0
    let T : R3 → ℝ := fun y => ∫ x in S, H x y * z x ∂(volume : Measure R3)
    ContDiffOn ℝ ∞ T D ∧
      ∀ y ∈ D, Literature.nativeMetricDifferential g T y = 0
 := by
  classical
  intro H T
  let μ : Measure R3 := (volume : Measure R3).restrict S
  let A : R3 → Matrix (Fin 3) (Fin 3) ℝ := principalCoefficient g
  let E : ℕ → Type := fun n => R3 [×n]→L[ℝ] ℝ
  let F : (n : ℕ) → R3 → R3 → E n :=
    fun n x y => iteratedFDeriv ℝ n (H x) y
  let e : Fin 3 → R3 := fun i => EuclideanSpace.single i (1 : ℝ)
  have hSnorm (x : R3) (hx : x ∈ S) : ‖x‖ ≤ (5/4 : ℝ) :=
    mem_closedBall_zero_iff.mp (hSroom (subset_closure hx))
  have hDnorm (y : R3) (hy : y ∈ D) : ‖y‖ ≤ (5/4 : ℝ) :=
    mem_closedBall_zero_iff.mp (hDroom hy)
  have hSU (x : R3) (hx : x ∈ S) : x ∈ (radiusTwoOpens : Set R3) := by
    have hn : ‖x‖ < 2 := by linarith only [hSnorm x hx]
    simpa only [radiusTwoOpens,TopologicalSpace.Opens.coe_mk,mem_ball,dist_zero_right] using hn
  have hDU (y : R3) (hy : y ∈ D) : y ∈ (radiusTwoOpens : Set R3) := by
    have hn : ‖y‖ < 2 := by linarith only [hDnorm y hy]
    simpa only [radiusTwoOpens,TopologicalSpace.Opens.coe_mk,mem_ball,dist_zero_right] using hn
  have hNe (x : R3) (hx : x ∈ S) (y : R3) (hy : y ∈ D) : x ≠ y := by
    intro he
    have hs := hSep x (subset_closure hx) y hy
    rw [he,dist_self] at hs
    exact (not_le_of_gt hd) hs
  have hFinite : (volume : Measure R3) S ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono (fun x hx => hSroom (subset_closure hx))).trans_lt
      measure_closedBall_lt_top
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hFinite
  have hzInt : Integrable (fun x : R3 => |z x|) μ := by
    have hi : Integrable (z : R3 → ℝ) μ :=
      memLp_one_iff_integrable.mp ((Lp.memLp z).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    simpa only [Real.norm_eq_abs] using hi.norm
  have hBasisNorm (j : Fin 3) : ‖e j‖ = 1 := by
    simpa only [e,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.1 j
  have hRow (x : R3) (hx : x ∈ S) :
      ContDiffOn ℝ ∞ (H x) D ∧ ∀ y ∈ D, divCoeffGrad A (H x) y = 0 := by
    let p : ↥(radiusTwoOpens : Set R3) := ⟨x,hSU x hx⟩
    have hr := radiusTwoSourceKernel_row_contDiffOn_and_nativeMetricDifferential_eq_zero
      hreg hcalc g hg K G hData p
    have hSub : D ⊆ (radiusTwoOpens : Set R3) \ {(p : R3)} := by
      intro y hy
      exact ⟨hDU y hy,by simpa only [mem_singleton_iff] using (hNe x hx y hy).symm⟩
    have hEq : H x = G p := by
      funext y
      simp only [H,dif_pos (hSU x hx),p]
    refine ⟨(by rw [hEq]; exact hr.1.mono hSub),?_⟩
    intro y hy
    have hp := hr.2 y (hSub hy)
    change -divCoeffGrad A (G p) y = 0 at hp
    rw [hEq]
    exact neg_eq_zero.mp hp
  have hBase (y : R3) (hy : y ∈ D) : AEStronglyMeasurable (fun x => H x y) μ := by
    let p : ↥(radiusTwoOpens : Set R3) := ⟨y,hDU y hy⟩
    have hc : ContinuousOn (G p) S := (hData.1 p).2.1.mono (by
      intro x hx
      exact ⟨(closedBall_subset_closedBall (by norm_num : (5/4 : ℝ) ≤ 2))
        (hSroom (subset_closure hx)),by simpa only [mem_singleton_iff] using hNe x hx y hy⟩)
    have he : EqOn (fun x => H x y) (G p) S := by
      intro x hx
      simpa only [H,dif_pos (hSU x hx),p] using
        hData.2 (⟨x,hSU x hx⟩ : ↥(radiusTwoOpens : Set R3)) p
    exact (hc.congr he).aestronglyMeasurable hS
  choose C hC hJet using
    (fun n : ℕ => exists_uniform_radiusTwoSourceKernel_inverse_distance_jet_bound
      hreg hcalc g hg K G hData n)
  let B : ℕ → ℝ := fun n => C n / d^(n+1)
  have hB (n : ℕ) : 0 ≤ B n := div_nonneg (hC n).le (pow_nonneg hd.le _)
  have hBound (n : ℕ) (x : R3) (hx : x ∈ S) (y : R3) (hy : y ∈ D) :
      ‖F n x y‖ ≤ B n := by
    have h0 := hJet n ⟨x,hSU x hx⟩ ⟨y,hDU y hy⟩
      (hSnorm x hx) (hDnorm y hy) (hNe x hx y hy)
    have hxy := hSep x (subset_closure hx) y hy
    have hEq : H x = G ⟨x,hSU x hx⟩ := by funext t; simp only [H,dif_pos (hSU x hx)]
    change ‖iteratedFDeriv ℝ n (H x) y‖ ≤ _
    rw [hEq]
    calc
      _ ≤ C n / dist x y^(n+1) := h0
      _ ≤ C n / d^(n+1) := by
        apply div_le_div_of_nonneg_left (hC n).le (pow_pos hd _)
        exact pow_le_pow_left₀ hd.le hxy _
  let Q : (n : ℕ) → (Fin n → Fin 3) → E n := fun n α =>
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
      (fun i => EuclideanSpace.proj (α i))
  have hExpand (n : ℕ) (L : E n) :
      L = ∑ α : Fin n → Fin 3, L (fun i => e (α i)) • Q n α := by
    ext v
    have hv (i : Fin n) : ∑ j : Fin 3, (v i j) • e j = v i := by
      simpa only [OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,e] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.sum_repr (v i)
    have hm := L.toMultilinearMap.map_sum (fun (i : Fin n) (j : Fin 3) => (v i j) • e j)
    simp only [hv] at hm
    have hm' : L v = ∑ α : Fin n → Fin 3,
        L (fun i => (v i (α i)) • e (α i)) := hm
    calc
      L v = ∑ α : Fin n → Fin 3,
          L (fun i => (v i (α i)) • e (α i)) := hm'
      _ = (∑ α : Fin n → Fin 3, L (fun i => e (α i)) • Q n α) v := by
        simp only [ContinuousMultilinearMap.sum_apply,ContinuousMultilinearMap.smul_apply,
          Q,ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply,EuclideanSpace.coe_proj,smul_eq_mul]
        apply Finset.sum_congr rfl
        intro α hα
        have hScale : L (fun i => (v i (α i)) • e (α i)) =
            (∏ i, v i (α i)) • L (fun i => e (α i)) :=
          L.toMultilinearMap.map_smul_univ (fun i => v i (α i)) (fun i => e (α i))
        rw [hScale,smul_eq_mul]
        exact mul_comm _ _
  have hMeas : ∀ (n : ℕ) (y : R3), y ∈ D → AEStronglyMeasurable (F n · y) μ := by
    intro n
    induction n with
    | zero =>
      intro y hy
      have hh := ((continuousMultilinearCurryFin0 ℝ R3 ℝ).symm.continuous).comp_aestronglyMeasurable
        (hBase y hy)
      simpa only [F,iteratedFDeriv_zero_eq_comp,Function.comp_def] using hh
    | succ n ih =>
      intro y hy
      obtain ⟨ε,hε,hεD⟩ := Metric.isOpen_iff.mp hD y hy
      let t : ℕ → ℝ := fun m => ε/((m : ℝ)+2)
      have htPos (m : ℕ) : 0 < t m := by dsimp only [t]; positivity
      have htLt (m : ℕ) : t m < ε := by
        dsimp only [t]
        apply (div_lt_iff₀ (by positivity : 0 < (m : ℝ)+2)).mpr
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      have ht0 : Tendsto t atTop (𝓝 (0 : ℝ)) := by
        simpa only [t,Nat.cast_add,Nat.cast_ofNat,Function.comp_def] using
          (tendsto_const_div_atTop_nhds_zero_nat ε).comp (tendsto_add_atTop_nat 2)
      have htRight : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
        tendsto_nhdsWithin_iff.mpr ⟨ht0,Eventually.of_forall htPos⟩
      have hComp (α : Fin (n+1) → Fin 3) :
          AEStronglyMeasurable (fun x => F (n+1) x y (fun i => e (α i))) μ := by
        let v : Fin n → R3 := fun i => e (α i.succ)
        let yshift : ℕ → R3 := fun m => y+t m • e (α 0)
        have hyshift (m : ℕ) : yshift m ∈ D := by
          apply hεD
          rw [mem_ball,dist_eq_norm]
          simp only [yshift,add_sub_cancel_left,norm_smul,hBasisNorm,Real.norm_eq_abs,
            abs_of_pos (htPos m),mul_one]
          exact htLt m
        let q : ℕ → R3 → ℝ := fun m x =>
          (t m)⁻¹ * (F n x (yshift m) v-F n x y v)
        have hqMeas (m : ℕ) : AEMeasurable (q m) μ := by
          have h1 := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => R3) ℝ v).continuous).comp_aestronglyMeasurable
            (ih (yshift m) (hyshift m))
          have h0 := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => R3) ℝ v).continuous).comp_aestronglyMeasurable
            (ih y hy)
          exact ((h1.aemeasurable.sub h0.aemeasurable).const_mul ((t m)⁻¹))
        have hqLim : ∀ᵐ x ∂μ, Tendsto (fun m => q m x) atTop
            (𝓝 (F (n+1) x y (fun i => e (α i)))) := by
          filter_upwards [ae_restrict_mem hS] with x hx
          have hfx : DifferentiableAt ℝ (iteratedFDeriv ℝ n (H x)) y :=
            ((hRow x hx).1.contDiffAt (hD.mem_nhds hy)).differentiableAt_iteratedFDeriv
              (by exact_mod_cast (WithTop.coe_lt_top n))
          have hLine {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
              (a b : V) : HasDerivAt (fun t : ℝ => a+t • b) b 0 := by
            simpa only [id_eq,zero_smul,add_zero,one_smul] using
              (((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a)
          have hp := hLine y (e (α 0))
          have hf := (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => R3) ℝ v).hasFDerivAt).comp
            y hfx.hasFDerivAt).comp_hasDerivAt_of_eq (0 : ℝ) hp (by simp only [zero_smul,add_zero])
          have hDirs : Fin.cons (e (α 0)) v = (fun i => e (α i)) := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i <;> rfl
          have hDeriv : HasDerivAt (fun s : ℝ => F n x (y+s • e (α 0)) v)
              (F (n+1) x y (fun i => e (α i))) 0 := by
            simpa only [F,v,fderiv_iteratedFDeriv,Function.comp_def,
              ContinuousLinearMap.comp_apply,ContinuousMultilinearMap.apply_apply,
              continuousMultilinearCurryLeftEquiv_apply,hDirs,zero_smul,add_zero] using hf
          simpa only [q,yshift,zero_add,zero_smul,add_zero,smul_eq_mul,Function.comp_def] using
            hDeriv.tendsto_slope_zero_right.comp htRight
        exact (aemeasurable_of_tendsto_metrizable_ae atTop hqMeas hqLim).aestronglyMeasurable
      have hs := (Finset.univ : Finset (Fin (n+1) → Fin 3)).aestronglyMeasurable_fun_sum
        (fun α _ => (hComp α).smul_const (Q (n+1) α))
      apply hs.congr
      exact Eventually.of_forall (fun x => (hExpand (n+1) (F (n+1) x y)).symm)
  have hInt (n : ℕ) (y : R3) (hy : y ∈ D) :
      Integrable (fun x => z x • F n x y) μ := by
    apply (hzInt.const_mul (B n)).mono' ((Lp.aestronglyMeasurable z).smul (hMeas n y hy))
    filter_upwards [ae_restrict_mem hS] with x hx
    change ‖z x • F n x y‖ ≤ B n * |z x|
    rw [norm_smul,Real.norm_eq_abs,mul_comm (B n)]
    exact mul_le_mul_of_nonneg_left (hBound n x hx y hy) (abs_nonneg _)
  have hRowsAE : ∀ᵐ x ∂μ, ContDiffOn ℝ ∞ (H x) D := by
    filter_upwards [ae_restrict_mem hS] with x hx
    exact (hRow x hx).1
  have hWeightedBound (n : ℕ) : ∀ᵐ x ∂μ, ∀ y ∈ D,
      ‖z x • iteratedFDeriv ℝ n (H x) y‖ ≤ B n * |z x| := by
    filter_upwards [ae_restrict_mem hS] with x hx y hy
    rw [norm_smul, Real.norm_eq_abs, mul_comm (B n)]
    exact mul_le_mul_of_nonneg_left (hBound n x hx y hy) (abs_nonneg _)
  obtain ⟨hTInfinity, hFirst, hSecond⟩ :=
    contDiffOn_integral_and_fderiv_of_dominated_iteratedFDeriv
      μ D hD H (fun x => z x) hRowsAE
      (fun n y hy => hInt n y hy)
      (fun n x => B n * |z x|) (fun n => hzInt.const_mul (B n)) hWeightedBound
  refine ⟨hTInfinity,?_⟩
  intro y hy
  have hAy : DifferentiableAt ℝ A y := by
    exact differentiableAt_pi.mpr (fun i => differentiableAt_pi.mpr (fun j =>
      (contDiff_principalCoefficient_entry g hg i j).differentiable (by simp) y))
  have hTy : ContDiffAt ℝ 2 T y := (hTInfinity.contDiffAt (hD.mem_nhds hy)).of_le (by simp)
  have hRowTy (x : R3) (hx : x ∈ S) : ContDiffAt ℝ 2 (H x) y :=
    ((hRow x hx).1.contDiffAt (hD.mem_nhds hy)).of_le (by simp)
  let a : Fin 3 → Fin 3 → ℝ := fun i j =>
    fderiv ℝ (fun q => A q i j) y (e i)
  have hFirstInt (j : Fin 3) : Integrable (fun x => z x*fderiv ℝ (H x) y (e j)) μ := by
    let Eval : E 1 →L[ℝ] ℝ :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => R3) ℝ
        (Fin.snoc (0 : Fin 0 → R3) (e j))
    have hi := Eval.integrable_comp (hInt 1 y hy)
    change Integrable (fun x => (z x • F 1 x y)
      (Fin.snoc (0 : Fin 0 → R3) (e j))) μ at hi
    have hEval (x : R3) : F 1 x y (Fin.snoc (0 : Fin 0 → R3) (e j)) =
        fderiv ℝ (H x) y (e j) := by
      change iteratedFDeriv ℝ 1 (H x) y (Fin.snoc (0 : Fin 0 → R3) (e j)) = _
      simpa only [Fin.snoc_zero] using
        (iteratedFDeriv_one_apply (𝕜 := ℝ) (f := H x) (x := y)
          (Fin.snoc (0 : Fin 0 → R3) (e j)))
    apply hi.congr
    exact Eventually.of_forall (fun x => by
      simpa only [ContinuousMultilinearMap.smul_apply, smul_eq_mul] using
        congrArg (fun r : ℝ => z x * r) (hEval x))
  have hSecondInt (i j : Fin 3) :
      Integrable (fun x => z x*fderiv ℝ (fderiv ℝ (H x)) y (e i) (e j)) μ := by
    let Eval : E 2 →L[ℝ] ℝ :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => R3) ℝ
        (Fin.cons (e i) (Fin.snoc (0 : Fin 0 → R3) (e j)))
    have hi := Eval.integrable_comp (hInt 2 y hy)
    change Integrable (fun x => (z x • F 2 x y)
      (Fin.cons (e i) (Fin.snoc (0 : Fin 0 → R3) (e j)))) μ at hi
    have hEval (x : R3) :
        F 2 x y (Fin.cons (e i) (Fin.snoc (0 : Fin 0 → R3) (e j))) =
          fderiv ℝ (fderiv ℝ (H x)) y (e i) (e j) := by
      change iteratedFDeriv ℝ 2 (H x) y
        (Fin.cons (e i) (Fin.snoc (0 : Fin 0 → R3) (e j))) = _
      simpa only [Fin.cons_zero, Fin.cons_one, Fin.snoc_zero] using
        (iteratedFDeriv_two_apply (𝕜 := ℝ) (H x) y
          (Fin.cons (e i) (Fin.snoc (0 : Fin 0 → R3) (e j))))
    apply hi.congr
    exact Eventually.of_forall (fun x => by
      simpa only [ContinuousMultilinearMap.smul_apply, smul_eq_mul] using
        congrArg (fun r : ℝ => z x * r) (hEval x))
  let J : Fin 3 → Fin 3 → R3 → ℝ := fun i j x =>
    a i j*(z x*fderiv ℝ (H x) y (e j)) +
      A y i j*(z x*fderiv ℝ (fderiv ℝ (H x)) y (e i) (e j))
  have hJInt (i j : Fin 3) : Integrable (J i j) μ :=
    ((hFirstInt j).const_mul (a i j)).add ((hSecondInt i j).const_mul (A y i j))
  have hDiv : divCoeffGrad A T y = ∫ x, ∑ i : Fin 3, ∑ j : Fin 3, J i j x ∂μ := by
    calc
      divCoeffGrad A T y = ∑ i : Fin 3, ∑ j : Fin 3,
          (a i j * fderiv ℝ T y (e j) +
            A y i j * fderiv ℝ (fderiv ℝ T) y (e i) (e j)) := by
        exact Regularity.Jets.divCoeffGrad_eq_jet hAy hTy
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          (a i j * (∫ x, z x * fderiv ℝ (H x) y (e j) ∂μ) +
            A y i j * (∫ x, z x * fderiv ℝ (fderiv ℝ (H x)) y (e i) (e j) ∂μ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact (congrArg
          (fun t : ℝ => a i j * t + A y i j * fderiv ℝ (fderiv ℝ T) y (e i) (e j))
          (hFirst y hy (e j))).trans
            (congrArg
              (fun t : ℝ => a i j * (∫ x, z x * fderiv ℝ (H x) y (e j) ∂μ) +
                A y i j * t)
              (hSecond y hy (e i) (e j)))
      _ = ∫ x, ∑ i : Fin 3, ∑ j : Fin 3, J i j x ∂μ := by
        rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hJInt i j))]
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finset_sum _ (fun j _ => hJInt i j)]
        apply Finset.sum_congr rfl
        intro j hj
        rw [integral_add ((hFirstInt j).const_mul (a i j))
          ((hSecondInt i j).const_mul (A y i j)),integral_const_mul,integral_const_mul]
  have hzDiv : (∫ x, ∑ i : Fin 3, ∑ j : Fin 3, J i j x ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hS] with x hx
    change (∑ i : Fin 3, ∑ j : Fin 3, J i j x) = (0 : ℝ)
    have hJetEq := Regularity.Jets.divCoeffGrad_eq_jet hAy (hRowTy x hx)
    have hForm : (∑ i : Fin 3, ∑ j : Fin 3, J i j x) = z x*divCoeffGrad A (H x) y := by
      rw [hJetEq,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [J,a,e]
      ring
    rw [hForm,(hRow x hx).2 y hy,mul_zero]
  have hZero : divCoeffGrad A T y = 0 := hDiv.trans hzDiv
  change -divCoeffGrad A T y = 0
  exact neg_eq_zero.mpr hZero

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.contDiffOn_integral_and_fderiv_of_dominated_iteratedFDeriv
#print axioms OAI.AnisotropicCalderon.ExteriorSource.contDiffOn_integral_radiusTwoSourceKernel_mul_L2_and_nativeMetricDifferential_eq_zero
