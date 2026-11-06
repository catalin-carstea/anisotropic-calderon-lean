import Calderon.NativeInteriorH2ContinuousRepresentative
import TauCeti.Analysis.Sobolev.Embedding
import TauCeti.Analysis.Sobolev.W1p.HolderEmbedding

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal Gradient ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

local instance nativeQuantitativeH2SixFact : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance nativeQuantitativeH2NNRealSixFact : Fact (1 ≤ ((6 : NNReal) : ENNReal)) := ⟨by
  rw [ENNReal.coe_ofNat]
  norm_num⟩

theorem exists_norm_bound_nativeW1pSix_of_compactH2
    (hcalc : FixedSobolevCalculus) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : BallSobolev 2) (K : Set R3), IsCompact K →
      K ⊆ (ballOpens : Set R3) →
      (∀ᵐ x ∂(volume : Measure R3).restrict ballOpens,
        x ∉ K → TauCeti.Wkp.value 2 U x = 0) →
      ∃ v : TauCeti.W1p (volume : Measure R3) ballOpens 6,
        ((TauCeti.W1p.value v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens]
          TauCeti.W1p.value (TauCeti.Wkp.firstOrder 1 U)) ∧
        ((TauCeti.W1p.gradient v : R3 → R3) =ᵐ[(volume : Measure R3).restrict ballOpens]
          TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U)) ∧ ‖v‖ ≤ C * ‖U‖ := by
  have hExp : (6 : ℝ≥0∞)⁻¹ + (Module.finrank ℝ R3 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
    have hDim : Module.finrank ℝ R3 = 3 := by simp [R3]
    rw [hDim]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by simp) (by finiteness)]
    norm_num [ENNReal.toReal_inv]
  let S : TauCeti.W1p0 (volume : Measure R3) ballOpens 2 →L[ℝ]
      Lp ℝ 6 ((volume : Measure R3).restrict ballOpens) :=
    TauCeti.W1p0.sobolevEmbeddingL (show (6 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) by norm_num) hExp
  let P : BallSobolev 2 →L[ℝ] BallH1 := TauCeti.Wkp.firstOrderL 1
  let D (i : Fin 3) : BallSobolev 2 →L[ℝ] BallH1 :=
    unitBallCoordinateDerivativeL hcalc 1 i
  let L (i : Fin 3) : ℝ →L[ℝ] R3 :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector i)
  let C : ℝ := ‖S‖ * ‖P‖ + ∑ i : Fin 3, ‖L i‖ * ‖S‖ * ‖D i‖
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro U K hK hKB hU
  let u : BallH1 := TauCeti.Wkp.firstOrder 1 U
  have hu : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens,
      x ∉ K → TauCeti.W1p.value u x = 0 := by
    simpa only [u, TauCeti.Wkp.value_firstOrder] using hU
  have hu0 : u ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    TauCeti.W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hK hKB hu
  let u0 : TauCeti.W1p0 (volume : Measure R3) ballOpens 2 := ⟨u, hu0⟩
  have hg := nativeH1_gradient_ae_zero_off_compact u K hK hu
  have hd (i : Fin 3) :
      (TauCeti.W1p.value (D i U) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens]
        (fun x => (TauCeti.W1p.gradient u x) i) := by
    have hRaw := unitBallCoordinateDerivativeL_value_ae hcalc 1 i U
    filter_upwards [hRaw] with x hx
    have hValue : TauCeti.Wkp.value 1 (D i U) = TauCeti.W1p.value (D i U) :=
      TauCeti.Wkp.value_one (D i U)
    have hPoint := congrArg (fun f : BallSobolev 0 => f x) hValue
    change TauCeti.Wkp.value 1 (D i U) x = (TauCeti.W1p.gradient u x) i at hx
    exact hPoint.symm.trans hx
  have hd0 (i : Fin 3) : D i U ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    apply TauCeti.W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hK hKB
    filter_upwards [hd i, hg] with x hx hgrad hxK
    exact hx.trans (congrArg (fun z : R3 => z i) (hgrad hxK))
  let d0 (i : Fin 3) : TauCeti.W1p0 (volume : Measure R3) ballOpens 2 := ⟨D i U, hd0 i⟩
  have hSu : (S u0 : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens]
      TauCeti.W1p.value u := by
    exact TauCeti.W1p0.coeFn_sobolevEmbeddingL
      (show (6 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) by norm_num) hExp u0
  have hSd (i : Fin 3) : (S (d0 i) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => (TauCeti.W1p.gradient u x) i) :=
    (TauCeti.W1p0.coeFn_sobolevEmbeddingL
      (show (6 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) by norm_num) hExp (d0 i)).trans (hd i)
  let G6 : Lp R3 6 ((volume : Measure R3).restrict ballOpens) :=
    ∑ i : Fin 3, (L i).compLp (S (d0 i))
  have hG6 : (G6 : R3 → R3) =ᵐ[(volume : Measure R3).restrict ballOpens]
      TauCeti.W1p.gradient u := by
    have hi (i : Fin 3) : ((L i).compLp (S (d0 i)) : R3 → R3)
        =ᵐ[(volume : Measure R3).restrict ballOpens]
          (fun x => (TauCeti.W1p.gradient u x) i • coordinateVector i) := by
      filter_upwards [(L i).coeFn_compLp (S (d0 i)), hSd i] with x hx hs
      rw [hx, hs]
      rfl
    have hsum : (G6 : R3 → R3) =ᵐ[(volume : Measure R3).restrict ballOpens]
        (fun x => ∑ i : Fin 3, (TauCeti.W1p.gradient u x) i • coordinateVector i) := by
      have hSum := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin 3))
        (fun i => (L i).compLp (S (d0 i)))
      filter_upwards [hSum, ae_all_iff.mpr hi] with x hx hxi
      exact hx.trans (Finset.sum_congr rfl (fun i _ => hxi i))
    filter_upwards [hsum] with x hx
    exact hx.trans (by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordinateVector]
        using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (TauCeti.W1p.gradient u x))
  obtain ⟨v, hv, hvg⟩ := exists_nativeW1pSix_of_compactH2 hcalc U K hK hKB hU
  have hvS : TauCeti.W1p.value v = S u0 := Lp.ext (hv.trans hSu.symm)
  have hgS : TauCeti.W1p.gradient v = G6 := Lp.ext (hvg.trans hG6.symm)
  have hValue : ‖S u0‖ ≤ (‖S‖ * ‖P‖) * ‖U‖ := by
    calc
      ‖S u0‖ ≤ ‖S‖ * ‖u0‖ := S.le_opNorm u0
      _ = ‖S‖ * ‖P U‖ := rfl
      _ ≤ ‖S‖ * (‖P‖ * ‖U‖) :=
        mul_le_mul_of_nonneg_left (P.le_opNorm U) (norm_nonneg S)
      _ = _ := by ring
  have hGradient : ‖G6‖ ≤ (∑ i : Fin 3, ‖L i‖ * ‖S‖ * ‖D i‖) * ‖U‖ := by
    calc
      ‖G6‖ ≤ ∑ i : Fin 3, ‖(L i).compLp (S (d0 i))‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, (‖L i‖ * ‖S‖ * ‖D i‖) * ‖U‖ := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          _ ≤ ‖L i‖ * ‖S (d0 i)‖ := (L i).norm_compLp_le _
          _ ≤ ‖L i‖ * (‖S‖ * ‖d0 i‖) :=
            mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg _)
          _ = ‖L i‖ * (‖S‖ * ‖D i U‖) := rfl
          _ ≤ ‖L i‖ * (‖S‖ * (‖D i‖ * ‖U‖)) := by
            gcongr
            exact (D i).le_opNorm U
          _ = _ := by ring
      _ = _ := (Finset.sum_mul _ _ _).symm
  refine ⟨v, hv, hvg, ?_⟩
  calc
    ‖v‖ ≤ ‖TauCeti.W1p.value v‖ + ‖TauCeti.W1p.gradient v‖ :=
      TauCeti.W1p.norm_le_norm_value_add_norm_gradient v
    _ = ‖S u0‖ + ‖G6‖ := by
      have hvNorm : ‖TauCeti.W1p.value v‖ = ‖S u0‖ :=
        congrArg (fun f : Lp ℝ 6 ((volume : Measure R3).restrict ballOpens) => ‖f‖) hvS
      have hgNorm : ‖TauCeti.W1p.gradient v‖ = ‖G6‖ :=
        congrArg (fun f : Lp R3 6 ((volume : Measure R3).restrict ballOpens) => ‖f‖) hgS
      exact congrArg₂ (fun x y : ℝ => x + y) hvNorm hgNorm
    _ ≤ (‖S‖ * ‖P‖) * ‖U‖ + (∑ i : Fin 3, ‖L i‖ * ‖S‖ * ‖D i‖) * ‖U‖ :=
      add_le_add hValue hGradient
    _ = C * ‖U‖ := by dsimp only [C]; ring

theorem exists_uniform_bound_continuous_representative_of_nativeCompactH2
    (hcalc : FixedSobolevCalculus) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : BallSobolev 2) (K : Set R3), IsCompact K →
      K ⊆ (ballOpens : Set R3) →
      (∀ᵐ x ∂(volume : Measure R3).restrict ballOpens,
        x ∉ K → TauCeti.Wkp.value 2 U x = 0) →
      ∃ F : R3 → ℝ, Continuous F ∧
        ((TauCeti.Wkp.value 2 U : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens] F) ∧
        ∀ x : R3, |F x| ≤ C * ‖U‖ := by
  obtain ⟨C, hC, hSix⟩ := exists_norm_bound_nativeW1pSix_of_compactH2 hcalc
  have hp : (Module.finrank ℝ R3 : NNReal) < (6 : NNReal) := by norm_num [R3]
  let M := TauCeti.W1p.morreyEmbedding (E := R3) (mu := (volume : Measure R3))
    (p := (6 : NNReal)) hp
  refine ⟨‖M‖ * C, mul_nonneg (norm_nonneg M) hC, ?_⟩
  intro U K hK hKB hU
  obtain ⟨v, hv, hg, hNorm⟩ := hSix U K hK hKB hU
  have hvK : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens,
      x ∉ K → TauCeti.W1p.value v x = 0 := by
    filter_upwards [hv, hU] with x hx hux hxK
    exact hx.trans (by simpa only [TauCeti.Wkp.value_firstOrder] using hux hxK)
  have hv0 : v ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 6 :=
    TauCeti.W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hK hKB hvK
  let z : TauCeti.W1p0 (volume : Measure R3) ballOpens 6 := ⟨v, hv0⟩
  let w : TauCeti.W1p (volume : Measure R3) ⊤ 6 :=
    (TauCeti.W1p0.extendByZeroL (Omega := ballOpens) (Omega' := ⊤) le_top z :
      TauCeti.W1p (volume : Measure R3) ⊤ 6)
  let F : R3 → ℝ := M w
  have hF : Continuous F := (M w).continuous
  have hRep : (TauCeti.W1p.value w : R3 → ℝ) =ᵐ[(volume : Measure R3)] F :=
    TauCeti.W1p.value_ae_eq_morreyEmbedding hp w
  have hExt : (TauCeti.W1p.value w : R3 → ℝ) =ᵐ[(volume : Measure R3)]
      (ballOpens : Set R3).indicator (TauCeti.W1p.value v) := by
    dsimp only [w]
    rw [TauCeti.W1p0.value_extendByZeroL]
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      TauCeti.coeFn_extendByZeroLpₗᵢ ℝ ballOpens.isOpen.measurableSet
        (SetLike.coe_subset_coe.mpr (le_top : ballOpens ≤ (⊤ : Opens R3))) (TauCeti.W1p.value v)
  have hRepB := ae_restrict_of_ae hRep (s := (ballOpens : Set R3))
  have hExtB := ae_restrict_of_ae hExt (s := (ballOpens : Set R3))
  have hNativeRep : (TauCeti.Wkp.value 2 U : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens] F := by
    filter_upwards [hRepB, hExtB, hv, ae_restrict_mem ballOpens.isOpen.measurableSet]
      with x hx he hvx hxB
    have hOld : TauCeti.W1p.value (TauCeti.Wkp.firstOrder 1 U) x = TauCeti.Wkp.value 2 U x :=
      congrArg (fun f : BallSobolev 0 => (f : R3 → ℝ) x) (TauCeti.Wkp.value_firstOrder 1 U)
    have he' : TauCeti.W1p.value w x = TauCeti.W1p.value v x := by
      simpa only [indicator_of_mem hxB] using he
    exact hOld.symm.trans (hvx.symm.trans (he'.symm.trans hx))
  have hwNorm : ‖w‖ = ‖v‖ := by
    exact TauCeti.W1p0.norm_extendByZeroL le_top z
  refine ⟨F, hF, hNativeRep, ?_⟩
  intro x
  calc
    |F x| = ‖(M w) x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖M w‖ := ((M w).toBoundedContinuousFunction.norm_coe_le_norm x).trans
      (M w).norm_toBoundedContinuousFunction_le
    _ ≤ ‖M‖ * ‖w‖ := M.le_opNorm w
    _ ≤ ‖M‖ * (C * ‖U‖) :=
      mul_le_mul_of_nonneg_left (hwNorm.trans_le hNorm) (norm_nonneg M)
    _ = (‖M‖ * C) * ‖U‖ := by ring

theorem exists_uniform_bound_continuous_representative_on_innerBall_of_nativeH2
    (hcalc : FixedSobolevCalculus) (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : BallSobolev 2, ∃ F : R3 → ℝ, Continuous F ∧
      (∀ᵐ x ∂(volume : Measure R3).restrict ballOpens,
        x ∈ closedBall (0 : R3) a → F x = TauCeti.Wkp.value 2 U x) ∧
      ∀ x : R3, |F x| ≤ C * ‖U‖ := by
  let b : ℝ := (a+1)/2
  let χ : ContDiffBump (0 : R3) := ⟨(a+b)/2, b, by dsimp [b]; linarith, by dsimp [b]; linarith⟩
  let Q : SmoothCoefficientJets 3 := compactCoefficient 3 χ χ.contDiff χ.hasCompactSupport
  let T : BallSobolev 2 →L[ℝ] BallSobolev 2 := coefficientMultiplier hcalc 2 Q
  let K : Set R3 := tsupport (χ : R3 → ℝ)
  have hK : IsCompact K := χ.hasCompactSupport
  have hKB : K ⊆ (ballOpens : Set R3) := by
    intro x hx
    have hnorm : ‖x‖ ≤ b := by
      simpa only [K, χ.tsupport_eq, mem_closedBall, dist_zero_right] using hx
    change dist x (0 : R3) < 1
    rw [dist_zero_right]
    dsimp only [b] at hnorm
    linarith
  obtain ⟨C, hC, hCompact⟩ := exists_uniform_bound_continuous_representative_of_nativeCompactH2 hcalc
  refine ⟨C * ‖T‖, mul_nonneg hC (norm_nonneg _), ?_⟩
  intro U
  let V : BallSobolev 2 := T U
  have hValue : (TauCeti.Wkp.value 2 V : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x : R3 => χ x * TauCeti.Wkp.value 2 U x) := by
    have hv := coefficientMultiplier_value_ae hcalc 2 Q U
    have hQ : coefficientValue 3 Q = (χ : R3 → ℝ) := coefficientValue_compactCoefficient 3 _ _ _
    simpa only [V, T, hQ] using hv
  have hVK : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens,
      x ∉ K → TauCeti.Wkp.value 2 V x = 0 := by
    filter_upwards [hValue] with x hx hxK
    have hχ0 : χ x = (0 : ℝ) := (notMem_tsupport_iff_eventuallyEq.mp hxK).eq_of_nhds
    exact hx.trans ((congrArg (fun q : ℝ => q * TauCeti.Wkp.value 2 U x) hχ0).trans (zero_mul _))
  obtain ⟨F, hF, hRep, hBound⟩ := hCompact V K hK hKB hVK
  refine ⟨F, hF, ?_, ?_⟩
  · filter_upwards [hRep, hValue] with x hx hv hxA
    have hχ1 : χ x = (1 : ℝ) := χ.one_of_mem_closedBall (by
      change dist x (0 : R3) ≤ (a+b)/2
      have hxnorm : dist x (0 : R3) ≤ a := hxA
      dsimp only [b]
      linarith)
    exact hx.symm.trans (hv.trans ((congrArg (fun q : ℝ => q * TauCeti.Wkp.value 2 U x) hχ1).trans (one_mul _)))
  · intro x
    calc
      |F x| ≤ C * ‖V‖ := hBound x
      _ ≤ C * (‖T‖ * ‖U‖) := mul_le_mul_of_nonneg_left (T.le_opNorm U) hC
      _ = (C * ‖T‖) * ‖U‖ := by ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_norm_bound_nativeW1pSix_of_compactH2
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_uniform_bound_continuous_representative_of_nativeCompactH2
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_uniform_bound_continuous_representative_on_innerBall_of_nativeH2
