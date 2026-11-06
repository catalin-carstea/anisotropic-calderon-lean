import Calderon.NativeSmoothOperatorRealization
import TauCeti.Analysis.Sobolev.Embedding
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import TauCeti.Analysis.Sobolev.W1p.HolderEmbedding

/-! Expanded first in EXPANSION-native-interior-H2-continuous-representative-v001.json.
Critical L6 embedding and Morrey give an actual local continuous representative.
No C-infinity representative or physical harmonic density is assumed. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal Gradient ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

local instance : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ((6 : NNReal) : ENNReal)) := ⟨by
  rw [ENNReal.coe_ofNat]
  norm_num⟩

theorem nativeH1_gradient_ae_zero_off_compact
    (u : BallH1) (K : Set R3) (hK : IsCompact K)
    (hu : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.W1p.value u x = 0) :
    ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.W1p.gradient u x = 0 := by
  let V : Opens R3 := ⟨(ballOpens : Set R3) \ K, ballOpens.isOpen.sdiff hK.isClosed⟩
  have hB : MeasurableSet (ballOpens : Set R3) := ballOpens.isOpen.measurableSet
  have hV : MeasurableSet (V : Set R3) := V.isOpen.measurableSet
  have huμ : ∀ᵐ x ∂(volume : Measure R3), x ∈ (ballOpens : Set R3) → x ∉ K →
      TauCeti.W1p.value u x = 0 := (ae_restrict_iff' hB).mp hu
  have huV : ∀ᵐ x ∂(volume : Measure R3).restrict V, TauCeti.W1p.value u x = 0 := by
    rw [ae_restrict_iff' hV]
    filter_upwards [huμ] with x hx hxV
    exact hx hxV.1 hxV.2
  have hgV := (ae_restrict_iff' hV).mp
    (TauCeti.W1p.gradient_ae_eq_zero_of_value_ae_eq_zero
      (V := V) (show V ≤ ballOpens from Set.sdiff_subset) huV)
  rw [ae_restrict_iff' hB]
  filter_upwards [hgV] with x hx hxB hxK
  exact hx ⟨hxB, hxK⟩

theorem memLp_nativeH1_value_six_of_zero
    (u : BallH1) (hu : u ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2) :
    MemLp (TauCeti.W1p.value u : R3 → ℝ) 6 ((volume : Measure R3).restrict ballOpens) :=
  TauCeti.W1p.memLp_value_of_mem_w1p0Submodule
    (show (6 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) by norm_num)
    (show (6 : ℝ≥0∞)⁻¹ + (Module.finrank ℝ R3 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ by
      have hDim : Module.finrank ℝ R3 = 3 := by simp [R3]
      rw [hDim]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by simp) (by simp)]
      norm_num [ENNReal.toReal_inv]) hu

theorem memLp_nativeCompactH2_gradient_coordinate_six
    (hcalc : FixedSobolevCalculus) (U : BallSobolev 2) (K : Set R3)
    (hK : IsCompact K) (hKB : K ⊆ (ballOpens : Set R3))
    (hU : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.Wkp.value 2 U x = 0)
    (i : Fin 3) :
    MemLp (fun x : R3 => (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) x) i)
      6 ((volume : Measure R3).restrict ballOpens) := by
  let u : BallH1 := TauCeti.Wkp.firstOrder 1 U
  let d : BallH1 := unitBallCoordinateDerivativeL hcalc 1 i U
  have hu : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.W1p.value u x = 0 := by
    simpa only [u, TauCeti.Wkp.value_firstOrder] using hU
  have hg := nativeH1_gradient_ae_zero_off_compact u K hK hu
  have hd : (TauCeti.W1p.value d : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x : R3 => (TauCeti.W1p.gradient u x) i) := by
    simpa only [d, u, TauCeti.Wkp.value_one] using
      unitBallCoordinateDerivativeL_value_ae hcalc 1 i U
  have hdK : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.W1p.value d x = 0 := by
    filter_upwards [hd, hg] with x hx hgrad hxK
    exact hx.trans (congrArg (fun z : R3 => z i) (hgrad hxK))
  have hd0 : d ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    TauCeti.W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hK hKB hdK
  exact MemLp.ae_eq hd (memLp_nativeH1_value_six_of_zero d hd0)

theorem memLp_nativeCompactH2_gradient_six
    (hcalc : FixedSobolevCalculus) (U : BallSobolev 2) (K : Set R3)
    (hK : IsCompact K) (hKB : K ⊆ (ballOpens : Set R3))
    (hU : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.Wkp.value 2 U x = 0) :
    MemLp (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) : R3 → R3)
      6 ((volume : Measure R3).restrict ballOpens) := by
  have hi (i : Fin 3) : MemLp
      (fun x : R3 => (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) x) i • coordinateVector i)
      6 ((volume : Measure R3).restrict ballOpens) := by
    let L : ℝ →L[ℝ] R3 := (ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector i)
    exact L.comp_memLp' (memLp_nativeCompactH2_gradient_coordinate_six hcalc U K hK hKB hU i)
  have hsum := memLp_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hi i)
  have he : (fun x : R3 => ∑ i : Fin 3,
      (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) x) i • coordinateVector i) =
      (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) : R3 → R3) := by
    funext x
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordinateVector] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) x)
  rw [he] at hsum
  exact hsum

theorem exists_nativeW1pSix_of_compactH2
    (hcalc : FixedSobolevCalculus) (U : BallSobolev 2) (K : Set R3)
    (hK : IsCompact K) (hKB : K ⊆ (ballOpens : Set R3))
    (hU : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.Wkp.value 2 U x = 0) :
    ∃ v : TauCeti.W1p (volume : Measure R3) ballOpens 6,
      ((TauCeti.W1p.value v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens]
        TauCeti.W1p.value (TauCeti.Wkp.firstOrder 1 U)) ∧
      ((TauCeti.W1p.gradient v : R3 → R3) =ᵐ[(volume : Measure R3).restrict ballOpens]
        TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U)) := by
  let u : BallH1 := TauCeti.Wkp.firstOrder 1 U
  have hu : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.W1p.value u x = 0 := by
    simpa only [u, TauCeti.Wkp.value_firstOrder] using hU
  have hu0 : u ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    TauCeti.W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hK hKB hu
  have hv := memLp_nativeH1_value_six_of_zero u hu0
  have hg := memLp_nativeCompactH2_gradient_six hcalc U K hK hKB hU
  have hw : TauCeti.HasWeakFDerivOn (volume : Measure R3) ballOpens
      (hv.toLp (TauCeti.W1p.value u))
      (fun x => innerSL ℝ ((hg.toLp (TauCeti.W1p.gradient u)) x)) := by
    apply ((TauCeti.W1p.hasWeakFDerivOn u).congr_ae hv.coeFn_toLp.symm).congr_ae_deriv
    filter_upwards [hg.coeFn_toLp] with x hx
    exact congrArg (innerSL ℝ) hx.symm
  refine ⟨TauCeti.W1p.mk (hv.toLp (TauCeti.W1p.value u))
    (hg.toLp (TauCeti.W1p.gradient u)) hw, ?_, ?_⟩
  · rw [TauCeti.W1p.value_mk]
    exact hv.coeFn_toLp
  · rw [TauCeti.W1p.gradient_mk]
    exact hg.coeFn_toLp

theorem exists_continuous_representative_of_nativeCompactH2
    (hcalc : FixedSobolevCalculus) (U : BallSobolev 2) (K : Set R3)
    (hK : IsCompact K) (hKB : K ⊆ (ballOpens : Set R3))
    (hU : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.Wkp.value 2 U x = 0) :
    ∃ F : R3 → ℝ, Continuous F ∧
      (TauCeti.Wkp.value 2 U : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens] F := by
  obtain ⟨v, hv, hg⟩ := exists_nativeW1pSix_of_compactH2 hcalc U K hK hKB hU
  have hvK : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.W1p.value v x = 0 := by
    filter_upwards [hv, hU] with x hx hux hxK
    exact hx.trans (by simpa only [TauCeti.Wkp.value_firstOrder] using hux hxK)
  have hv0 : v ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 6 :=
    TauCeti.W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hK hKB hvK
  let z : TauCeti.W1p0 (volume : Measure R3) ballOpens 6 := ⟨v, hv0⟩
  let w : TauCeti.W1p (volume : Measure R3) ⊤ 6 :=
    (TauCeti.W1p0.extendByZeroL (Omega := ballOpens) (Omega' := ⊤) le_top z :
      TauCeti.W1p (volume : Measure R3) ⊤ 6)
  have hp : (Module.finrank ℝ R3 : NNReal) < (6 : NNReal) := by norm_num [R3]
  let F : R3 → ℝ := TauCeti.W1p.morreyEmbedding (E := R3) (mu := (volume : Measure R3))
    (p := (6 : NNReal)) (hp := hp) w
  have hF : Continuous F := (TauCeti.W1p.morreyEmbedding (E := R3) (mu := (volume : Measure R3))
    (p := (6 : NNReal)) (hp := hp) w).continuous
  have hRep : (TauCeti.W1p.value w : R3 → ℝ) =ᵐ[(volume : Measure R3)] F :=
    TauCeti.W1p.value_ae_eq_morreyEmbedding (E := R3)
      (mu := (volume : Measure R3)) (p := (6 : NNReal)) (hp := hp) (u := w)
  have hExt : (TauCeti.W1p.value w : R3 → ℝ) =ᵐ[(volume : Measure R3)]
      (ballOpens : Set R3).indicator (TauCeti.W1p.value v) := by
    dsimp only [w]
    rw [TauCeti.W1p0.value_extendByZeroL]
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      TauCeti.coeFn_extendByZeroLpₗᵢ ℝ ballOpens.isOpen.measurableSet
        (SetLike.coe_subset_coe.mpr (le_top : ballOpens ≤ (⊤ : Opens R3))) (TauCeti.W1p.value v)
  have hRepB : (TauCeti.W1p.value w : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens] F := ae_restrict_of_ae hRep
  have hExtB : (TauCeti.W1p.value w : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens]
        (ballOpens : Set R3).indicator (TauCeti.W1p.value v) := ae_restrict_of_ae hExt
  refine ⟨F, hF, ?_⟩
  filter_upwards [hRepB, hExtB, hv, ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx he hvx hxB
  have hOld : TauCeti.W1p.value (TauCeti.Wkp.firstOrder 1 U) x = TauCeti.Wkp.value 2 U x :=
    congrArg (fun f : BallSobolev 0 => (f : R3 → ℝ) x)
      (TauCeti.Wkp.value_firstOrder 1 U)
  have he' : TauCeti.W1p.value w x = TauCeti.W1p.value v x := by
    simpa only [indicator_of_mem hxB] using he
  exact hOld.symm.trans (hvx.symm.trans (he'.symm.trans hx))

theorem exists_continuous_representative_on_innerBall_of_nativeH2
    (hcalc : FixedSobolevCalculus) (U : BallSobolev 2) (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ F : R3 → ℝ, Continuous F ∧
      ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∈ closedBall (0 : R3) a →
        F x = TauCeti.Wkp.value 2 U x := by
  let b : ℝ := (a+1)/2
  let χ : ContDiffBump (0 : R3) := ⟨(a+b)/2, b, by dsimp [b]; linarith, by dsimp [b]; linarith⟩
  let C : SmoothCoefficientJets 3 := compactCoefficient 3 χ χ.contDiff χ.hasCompactSupport
  let V : BallSobolev 2 := coefficientMultiplier hcalc 2 C U
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
  have hValue : (TauCeti.Wkp.value 2 V : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x : R3 => χ x * TauCeti.Wkp.value 2 U x) := by
    have hv := coefficientMultiplier_value_ae hcalc 2 C U
    have hC : coefficientValue 3 C = (χ : R3 → ℝ) := coefficientValue_compactCoefficient 3 _ _ _
    simpa only [V, hC] using hv
  have hVK : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.Wkp.value 2 V x = 0 := by
    filter_upwards [hValue] with x hx hxK
    have hχ0 : χ x = (0 : ℝ) :=
      (notMem_tsupport_iff_eventuallyEq.mp hxK).eq_of_nhds
    exact hx.trans ((congrArg (fun q : ℝ => q * TauCeti.Wkp.value 2 U x) hχ0).trans (zero_mul _))
  obtain ⟨F, hF, hRep⟩ := exists_continuous_representative_of_nativeCompactH2 hcalc V K hK hKB hVK
  refine ⟨F, hF, ?_⟩
  filter_upwards [hRep, hValue] with x hx hv hxA
  have hχ1 : χ x = (1 : ℝ) := χ.one_of_mem_closedBall (by
    change dist x (0 : R3) ≤ (a+b)/2
    have hxnorm : dist x (0 : R3) ≤ a := hxA
    dsimp only [b]
    linarith)
  exact hx.symm.trans (hv.trans ((congrArg (fun q : ℝ => q * TauCeti.Wkp.value 2 U x) hχ1).trans (one_mul _)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1_gradient_ae_zero_off_compact
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.memLp_nativeH1_value_six_of_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.memLp_nativeCompactH2_gradient_coordinate_six
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.memLp_nativeCompactH2_gradient_six
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeW1pSix_of_compactH2
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_continuous_representative_of_nativeCompactH2
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_continuous_representative_on_innerBall_of_nativeH2
